//! Runner tests on calibration scenarios only (no proving), so they are fast in any profile.
use kn_run::record::{validate, FIELDS};
use serde_json::{Map, Value};
use std::{path::PathBuf, process::Command};

fn out_file(name: &str) -> PathBuf {
  let p = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!("kn-run-{name}.jsonl"));
  let _ = std::fs::remove_file(&p);
  p
}

/// Runs `kn-run <args> --out <file>` and returns (exit success, records appended).
fn kn_run(name: &str, args: &[&str]) -> (bool, Vec<Map<String, Value>>) {
  let out = out_file(name);
  let status = Command::new(env!("CARGO_BIN_EXE_kn-run"))
    .args(args)
    .arg("--out")
    .arg(&out)
    .env("KN_SCENARIO_BIN", env!("CARGO_BIN_EXE_kn-scenario"))
    .output()
    .expect("run kn-run");
  let records = std::fs::read_to_string(&out)
    .unwrap_or_default()
    .lines()
    .map(|l| {
      serde_json::from_str::<Value>(l)
        .unwrap()
        .as_object()
        .unwrap()
        .clone()
    })
    .collect();
  (status.status.success(), records)
}

fn one(name: &str, args: &[&str]) -> (bool, Map<String, Value>) {
  let (ok, mut recs) = kn_run(name, args);
  assert_eq!(recs.len(), 1, "exactly one record per run");
  let r = recs.pop().unwrap();
  validate(&r).unwrap();
  (ok, r)
}

#[test]
fn schema_lists_exactly_the_record_fields() {
  let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../results/schema.json");
  let schema: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
  let props: Vec<&str> = schema["properties"]
    .as_object()
    .unwrap()
    .keys()
    .map(String::as_str)
    .collect();
  let required: Vec<&str> = schema["required"]
    .as_array()
    .unwrap()
    .iter()
    .map(|v| v.as_str().unwrap())
    .collect();
  let mut fields = FIELDS.to_vec();
  let mut props_sorted = props.clone();
  fields.sort();
  props_sorted.sort();
  assert_eq!(props_sorted, fields);
  assert_eq!(required, FIELDS);
  assert_eq!(schema["additionalProperties"], false);
}

#[test]
fn noop_success_record() {
  let (ok, r) = one("noop", &["scenario", "noop"]);
  assert!(ok);
  assert_eq!(r["status"], "success");
  assert_eq!(r["threads"], 1);
  assert_eq!(r["threads_requested"], 1);
  assert!(r["peak_rss_bytes"].as_u64().unwrap() > 0);
  assert!(r["wall_ms"].as_f64().unwrap() > 0.0);
  assert!(r["config_hash"].as_str().unwrap().len() == 64);
  // Non-applicable fields are null with a reason, never 0.
  assert!(r["K"].is_null() && r["null_reasons"]["K"].is_string());
  assert!(r["compression_ms"].is_null());
}

#[test]
fn same_config_same_hashes() {
  let (_, a) = one("det-a", &["scenario", "sleep", "ms=1"]);
  let (_, b) = one("det-b", &["scenario", "sleep", "ms=1"]);
  let (_, c) = one("det-c", &["scenario", "sleep", "ms=2"]);
  for k in ["config_hash", "input_digest", "result_digest"] {
    assert_eq!(a[k], b[k], "{k}");
    assert_ne!(a[k], c[k], "{k}");
  }
  assert_ne!(a["run_id"], b["run_id"]);
}

#[test]
fn threads_request_is_recorded_as_actual() {
  let (_, r) = one("threads", &["scenario", "noop", "--threads", "3"]);
  assert_eq!(r["threads_requested"], 3);
  assert_eq!(r["threads"], 3);
}

#[test]
fn sleep_wall_time_boundary() {
  let (ok, r) = one("sleep", &["scenario", "sleep", "ms=100"]);
  assert!(ok);
  let wall = r["wall_ms"].as_f64().unwrap();
  let inproc = r["details"]["sleep_ms_measured"].as_f64().unwrap();
  assert!(
    inproc >= 100.0 && wall >= inproc,
    "wall={wall} inproc={inproc}"
  );
}

#[test]
fn panic_is_a_recorded_failure() {
  let (ok, r) = one("fail", &["scenario", "fail"]);
  assert!(!ok);
  assert_eq!(r["status"], "failure");
  assert!(r["exit_code"].as_i64().unwrap() != 0);
  assert!(r["error_message"]
    .as_str()
    .unwrap()
    .contains("deliberate failure"));
}

#[test]
fn timeout_is_a_recorded_timeout() {
  let (ok, r) = one(
    "timeout",
    &["scenario", "sleep", "ms=5000", "--timeout-s", "1"],
  );
  assert!(!ok);
  assert_eq!(r["status"], "timeout");
  assert_eq!(r["signal"], libc::SIGKILL);
  assert!(r["wall_ms"].as_f64().unwrap() < 3000.0);
}

#[test]
fn bad_arguments_are_recorded_failures() {
  let (_, r) = one("unknown", &["scenario", "no-such-scenario"]);
  assert_eq!(r["status"], "failure");
  let (_, r) = one("missing-arg", &["scenario", "sleep"]);
  assert_eq!(r["status"], "failure");
  assert!(r["error_message"]
    .as_str()
    .unwrap()
    .contains("missing argument ms"));
}

#[test]
fn records_append_and_never_rewrite() {
  let out = out_file("append");
  for _ in 0..2 {
    let st = Command::new(env!("CARGO_BIN_EXE_kn-run"))
      .args(["scenario", "noop", "--out"])
      .arg(&out)
      .env("KN_SCENARIO_BIN", env!("CARGO_BIN_EXE_kn-scenario"))
      .status()
      .unwrap();
    assert!(st.success());
  }
  let n = std::fs::read_to_string(&out).unwrap().lines().count();
  assert_eq!(n, 2);
}
