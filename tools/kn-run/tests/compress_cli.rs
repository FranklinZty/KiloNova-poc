//! P7 acceptance: "after the prover's private checkpoint is deleted, the independent verifier
//! still verifies chain and tree proofs, and never reads a witness from an undeclared cache".
//!
//! Every step runs as its own `kn-scenario` process and communicates only through files:
//! `compress-setup` writes `public/{material.knvm, setup.json}`; `compress-prove` writes
//! `private/checkpoint.bin` and `public/proof.kncp`; the `private/` directory is then deleted
//! and `compress-verify` (a fresh process) verifies from `public/` alone. A tampered proof file
//! and a verifier pinned to another setup are rejected in the same way.
//!
//! These runs prove real recursion (setup ≈ 15–25 s per process); they need the release build.
use serde_json::Value;
use std::{fs, path::Path, process::Command};

fn scenario(name: &str, args: &[String]) -> (bool, Value) {
  let out = Command::new(env!("CARGO_BIN_EXE_kn-scenario"))
    .arg(name)
    .args(args)
    .env("RAYON_NUM_THREADS", "2")
    .output()
    .expect("run kn-scenario");
  let stdout = String::from_utf8_lossy(&out.stdout);
  let line = stdout
    .lines()
    .find_map(|l| l.strip_prefix(kn_run::RESULT_PREFIX))
    .unwrap_or_else(|| {
      panic!(
        "{name}: no result line; stderr: {}",
        String::from_utf8_lossy(&out.stderr)
      )
    });
  (out.status.success(), serde_json::from_str(line).unwrap())
}

fn flow(dir: &Path, base: &[&str]) {
  let _ = fs::remove_dir_all(dir);
  let mut args: Vec<String> = base.iter().map(|s| s.to_string()).collect();
  args.push(format!("dir={}", dir.display()));
  let (ok, r) = scenario("compress-setup", &args);
  assert!(ok, "setup: {r}");
  let (ok, r) = scenario("compress-prove", &args);
  assert!(ok, "prove: {r}");
  assert!(dir.join("private/checkpoint.bin").exists());
  // delete the prover's private checkpoint before verification
  fs::remove_dir_all(dir.join("private")).unwrap();
  assert!(!dir.join("private").exists());
  let mut cold = args.clone();
  cold.push("mode=cold".into());
  let (ok, r) = scenario("compress-verify", &cold);
  assert!(ok, "verify (cold): {r}");
  assert_eq!(r["fields"]["verification_ok"], Value::Bool(true));
  assert_eq!(
    r["details"]["files_read"],
    serde_json::json!([
      "public/setup.json",
      "public/material.knvm",
      "public/proof.kncp"
    ])
  );
  let mut warm = args.clone();
  warm.push("mode=warm".into());
  warm.push("reps=1".into());
  let (ok, r) = scenario("compress-verify", &warm);
  assert!(ok, "verify (warm): {r}");

  // a flipped byte in the proof file is rejected by the separate verifier
  let proof = dir.join("public/proof.kncp");
  let good = fs::read(&proof).unwrap();
  let mut bad = good.clone();
  let mid = bad.len() / 2;
  bad[mid] ^= 1;
  fs::write(&proof, &bad).unwrap();
  let (ok, r) = scenario("compress-verify", &cold);
  assert!(!ok, "tampered proof accepted: {r}");
  // a truncated file too
  fs::write(&proof, &good[..good.len() - 7]).unwrap();
  let (ok, r) = scenario("compress-verify", &cold);
  assert!(!ok, "truncated proof accepted: {r}");
  assert!(r["error"].as_str().unwrap().contains("Format"), "{r}");
  fs::write(&proof, &good).unwrap();
  // the verifier pinned to another setup digest rejects the material
  let setup = dir.join("public/setup.json");
  let s = fs::read_to_string(&setup).unwrap();
  let mut v: Value = serde_json::from_str(&s).unwrap();
  let d = v["pp_digest"].as_str().unwrap().to_string();
  let flipped = format!("{}{}", if &d[..1] == "0" { "1" } else { "0" }, &d[1..]);
  v["pp_digest"] = Value::String(flipped);
  fs::write(&setup, v.to_string()).unwrap();
  let (ok, r) = scenario("compress-verify", &cold);
  assert!(!ok, "other pinned digest accepted: {r}");
  assert!(r["error"].as_str().unwrap().contains("Material"), "{r}");
  fs::write(&setup, s).unwrap();
  let _ = fs::remove_dir_all(dir);
}

#[test]
fn compress_cli_checkpoint_deleted_chain() {
  let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("p7-cli-chain");
  flow(
    &dir,
    &["kind=chain", "variant=direct", "K=2", "T=3", "seed=101"],
  );
}

#[test]
fn compress_cli_checkpoint_deleted_tree() {
  let dir = Path::new(env!("CARGO_TARGET_TMPDIR")).join("p7-cli-tree");
  flow(
    &dir,
    &["kind=tree", "variant=direct", "a=2", "L=3", "seed=101"],
  );
}
