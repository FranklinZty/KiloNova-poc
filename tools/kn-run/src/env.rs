//! Capture of the run environment: source revision, dependency locks, toolchain and machine.
use crate::sha256_hex;
use serde_json::{json, Value};
use std::{path::Path, process::Command};

/// Environment facts recorded once per run. A missing fact is `None` with a reason.
#[derive(Clone, Debug)]
pub struct RunEnv {
  pub implementation_commit: Option<String>,
  pub implementation_dirty: Option<bool>,
  pub dependency_lock_hash: Option<String>,
  pub cargo_lock_hash: Option<String>,
  pub rust_version: Option<String>,
  pub machine_id: String,
  pub machine: Value,
}

fn cmd_stdout(program: &str, args: &[&str], cwd: &Path) -> Option<String> {
  let out = Command::new(program)
    .args(args)
    .current_dir(cwd)
    .output()
    .ok()?;
  if !out.status.success() {
    return None;
  }
  let s = String::from_utf8_lossy(&out.stdout).trim().to_string();
  (!s.is_empty()).then_some(s)
}

fn file_hash(path: &Path) -> Option<String> {
  std::fs::read(path).ok().map(|b| sha256_hex(&b))
}

fn cpu_model(root: &Path) -> Option<String> {
  if cfg!(target_os = "macos") {
    cmd_stdout("sysctl", &["-n", "machdep.cpu.brand_string"], root)
  } else {
    std::fs::read_to_string("/proc/cpuinfo").ok().and_then(|s| {
      s.lines()
        .find(|l| l.starts_with("model name"))
        .and_then(|l| l.split(':').nth(1))
        .map(|v| v.trim().to_string())
    })
  }
}

fn mem_total_bytes(root: &Path) -> Option<u64> {
  if cfg!(target_os = "macos") {
    cmd_stdout("sysctl", &["-n", "hw.memsize"], root).and_then(|s| s.parse().ok())
  } else {
    std::fs::read_to_string("/proc/meminfo").ok().and_then(|s| {
      s.lines()
        .find(|l| l.starts_with("MemTotal:"))
        .and_then(|l| l.split_whitespace().nth(1))
        .and_then(|kb| kb.parse::<u64>().ok())
        .map(|kb| kb * 1024)
    })
  }
}

impl RunEnv {
  pub fn capture(root: &Path) -> Self {
    let implementation_commit = cmd_stdout("git", &["rev-parse", "HEAD"], root);
    let implementation_dirty = Command::new("git")
      .args(["status", "--porcelain", "--untracked-files=no"])
      .current_dir(root)
      .output()
      .ok()
      .filter(|o| o.status.success())
      .map(|o| !o.stdout.is_empty());

    let machine = json!({
      "hostname": cmd_stdout("hostname", &[], root),
      "os": cmd_stdout("uname", &["-sr"], root),
      "arch": std::env::consts::ARCH,
      "cpu_model": cpu_model(root),
      "logical_cpus": std::thread::available_parallelism().ok().map(|n| n.get()),
      "mem_total_bytes": mem_total_bytes(root),
    });
    let machine_id = sha256_hex(machine.to_string().as_bytes())[..16].to_string();

    Self {
      implementation_commit,
      implementation_dirty,
      dependency_lock_hash: file_hash(&root.join("versions.lock")),
      cargo_lock_hash: file_hash(&root.join("Cargo.lock")),
      rust_version: cmd_stdout("rustc", &["-V"], root),
      machine_id,
      machine,
    }
  }
}
