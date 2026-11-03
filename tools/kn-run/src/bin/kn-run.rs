//! `kn-run`: process-isolated runner for KiloNova scenarios and tests (PLAN.md §3 P1).
//!
//! ```text
//! kn-run scenario <name> [key=value ...] [options]
//! kn-run test <libtest test path> [--include-ignored] [options]
//! kn-run selfcheck [--quick] [options]
//!
//! options: --experiment ID   (default "adhoc"; selfcheck: "p1-selfcheck")
//!          --seed N          (bootstrap/chain default 101)
//!          --threads N       (RAYON_NUM_THREADS for the child, default 1)
//!          --timeout-s N     (default 1800)
//!          --mem-cap-mb N    (RLIMIT_AS, enforced on Linux only)
//!          --repetition N    (default 0)   --warmup
//!          --out PATH        (default results/raw/<experiment>.jsonl)
//! ```
use kn_run::{
  env::RunEnv,
  proc::{run_child, RunSpec},
  random_hex, record, repo_root, sha256_hex, utc_timestamp, RESULT_PREFIX,
};
use serde_json::{Map, Value};
use std::{
  collections::BTreeMap,
  path::{Path, PathBuf},
  process::Command,
  sync::OnceLock,
  time::{Duration, SystemTime},
};

#[derive(Clone, Debug)]
struct Opts {
  experiment: Option<String>,
  seed: Option<u64>,
  threads: usize,
  timeout_s: u64,
  mem_cap_mb: Option<u64>,
  repetition: u64,
  warmup: bool,
  out: Option<PathBuf>,
  include_ignored: bool,
  quick: bool,
}

impl Default for Opts {
  fn default() -> Self {
    Self {
      experiment: None,
      seed: None,
      threads: 1,
      timeout_s: 1800,
      mem_cap_mb: None,
      repetition: 0,
      warmup: false,
      out: None,
      include_ignored: false,
      quick: false,
    }
  }
}

/// What to run in the child process.
enum Target {
  Scenario { name: String, args: Vec<String> },
  Test { path: String },
}

fn usage() -> ! {
  eprintln!(
    "usage: kn-run scenario <name> [key=value ...] [options]\n       kn-run test <test path> [--include-ignored] [options]\n       kn-run selfcheck [--quick] [options]\n(see the header of tools/kn-run/src/bin/kn-run.rs for options)"
  );
  std::process::exit(2)
}

fn parse(argv: &[String]) -> Result<(Opts, Vec<String>), String> {
  let mut o = Opts::default();
  let mut pos = Vec::new();
  let mut it = argv.iter();
  while let Some(a) = it.next() {
    let mut val = |name: &str| -> Result<String, String> {
      it.next()
        .cloned()
        .ok_or_else(|| format!("{name} needs a value"))
    };
    let num = |s: String, name: &str| -> Result<u64, String> {
      s.parse()
        .map_err(|_| format!("{name}: '{s}' is not a number"))
    };
    match a.as_str() {
      "--experiment" => o.experiment = Some(val(a)?),
      "--seed" => o.seed = Some(num(val(a)?, a)?),
      "--threads" => o.threads = num(val(a)?, a)? as usize,
      "--timeout-s" => o.timeout_s = num(val(a)?, a)?,
      "--mem-cap-mb" => o.mem_cap_mb = Some(num(val(a)?, a)?),
      "--repetition" => o.repetition = num(val(a)?, a)?,
      "--warmup" => o.warmup = true,
      "--out" => o.out = Some(PathBuf::from(val(a)?)),
      "--include-ignored" => o.include_ignored = true,
      "--quick" => o.quick = true,
      s if s.starts_with("--") => return Err(format!("unknown option {s}")),
      _ => pos.push(a.clone()),
    }
  }
  if o.threads == 0 {
    return Err("--threads must be >= 1".into());
  }
  Ok((o, pos))
}

fn run_env() -> &'static RunEnv {
  static ENV: OnceLock<RunEnv> = OnceLock::new();
  ENV.get_or_init(|| RunEnv::capture(&repo_root()))
}

fn scenario_bin() -> PathBuf {
  if let Some(p) = std::env::var_os("KN_SCENARIO_BIN") {
    return PathBuf::from(p);
  }
  let exe = std::env::current_exe().expect("current_exe");
  exe.with_file_name("kn-scenario")
}

/// Builds (if needed) and locates the nova-snark lib test binary.
fn test_bin() -> Result<PathBuf, String> {
  if let Some(p) = std::env::var_os("KN_TEST_BIN") {
    return Ok(PathBuf::from(p));
  }
  let out = Command::new(std::env::var("CARGO").unwrap_or_else(|_| "cargo".into()))
    .args([
      "test",
      "-p",
      "nova-snark",
      "--release",
      "--lib",
      "--no-run",
      "--message-format=json",
    ])
    .current_dir(repo_root())
    .output()
    .map_err(|e| format!("cannot run cargo: {e}"))?;
  if !out.status.success() {
    return Err(format!(
      "cargo test --no-run failed: {}",
      tail(&String::from_utf8_lossy(&out.stderr), 20)
    ));
  }
  String::from_utf8_lossy(&out.stdout)
    .lines()
    .filter_map(|l| serde_json::from_str::<Value>(l).ok())
    .filter(|v| v["reason"] == "compiler-artifact" && v["profile"]["test"] == true)
    .filter(|v| v["target"]["name"] == "nova_snark")
    .find_map(|v| v["executable"].as_str().map(PathBuf::from))
    .ok_or_else(|| "nova-snark lib test executable not found in cargo output".into())
}

fn tail(s: &str, lines: usize) -> String {
  let v: Vec<&str> = s.lines().collect();
  let t = v[v.len().saturating_sub(lines)..].join("\n");
  if t.len() > 4000 {
    t[t.len() - 4000..].to_string()
  } else {
    t
  }
}

/// libtest summary counts: (passed, failed, ignored).
fn libtest_counts(stdout: &str) -> Option<(u64, u64, u64)> {
  let line = stdout
    .lines()
    .rev()
    .find(|l| l.starts_with("test result:"))?;
  let count = |label: &str| -> Option<u64> {
    line
      .split(';')
      .find(|p| p.trim_end().ends_with(label))
      .and_then(|p| p.split_whitespace().rev().nth(1))
      .and_then(|n| n.parse().ok())
  };
  Some((count("passed")?, count("failed")?, count("ignored")?))
}

fn out_path(opts: &Opts, experiment: &str) -> PathBuf {
  opts.out.clone().unwrap_or_else(|| {
    repo_root()
      .join("results/raw")
      .join(format!("{experiment}.jsonl"))
  })
}

fn rel(p: &Path) -> String {
  let root = repo_root().canonicalize().unwrap_or_else(|_| repo_root());
  let p = p.canonicalize().unwrap_or_else(|_| p.to_path_buf());
  p.strip_prefix(&root)
    .map(|r| r.display().to_string())
    .unwrap_or_else(|_| p.display().to_string())
}

/// Runs one target in a fresh process, appends its record, and returns the record.
fn execute(target: &Target, opts: &Opts, default_experiment: &str) -> Map<String, Value> {
  let env = run_env();
  let experiment = opts
    .experiment
    .clone()
    .unwrap_or_else(|| default_experiment.to_string());
  let out_file = out_path(opts, &experiment);
  let logs = out_file.parent().unwrap_or(Path::new(".")).join("logs");
  let _ = std::fs::create_dir_all(&logs);

  let now = SystemTime::now();
  let ts = utc_timestamp(now);
  // `YYYYMMDDTHHMMSSZ-<8 hex>`, sortable by start time.
  let compact: String = ts.chars().filter(|c| c.is_ascii_alphanumeric()).collect();
  let run_id = format!("{}Z-{}", &compact[..15], random_hex(4));
  let log_out = logs.join(format!("{run_id}.out"));
  let log_err = logs.join(format!("{run_id}.err"));

  let mut rec = record::Record::new();
  rec.set("run_id", run_id.clone());
  rec.set("timestamp", ts);
  rec.set("experiment_id", experiment.clone());
  rec.set("repetition", opts.repetition);
  rec.set("warmup", opts.warmup);
  rec.set("threads_requested", opts.threads);
  rec.set("timeout_s", opts.timeout_s);
  rec.set_opt(
    "mem_cap_bytes",
    opts.mem_cap_mb.map(|m| m * 1024 * 1024),
    "no memory cap requested",
  );
  rec.set_opt(
    "implementation_commit",
    env.implementation_commit.clone(),
    "git rev-parse HEAD failed",
  );
  rec.set_opt(
    "implementation_dirty",
    env.implementation_dirty,
    "git status failed",
  );
  rec.set_opt(
    "dependency_lock_hash",
    env.dependency_lock_hash.clone(),
    "versions.lock not readable",
  );
  rec.set_opt(
    "cargo_lock_hash",
    env.cargo_lock_hash.clone(),
    "Cargo.lock not readable",
  );
  rec.set_opt("rust_version", env.rust_version.clone(), "rustc -V failed");
  rec.set("machine_id", env.machine_id.clone());
  rec.set("machine", env.machine.clone());
  rec.set("log_stdout", rel(&log_out));
  rec.set("log_stderr", rel(&log_err));

  // Program, arguments and the canonical configuration (hashed into config_hash).
  let mut config = BTreeMap::new();
  config.insert("threads", opts.threads.to_string());
  config.insert("timeout_s", opts.timeout_s.to_string());
  config.insert(
    "mem_cap_mb",
    opts.mem_cap_mb.map(|m| m.to_string()).unwrap_or_default(),
  );
  let (program, args, seed) = match target {
    Target::Scenario { name, args } => {
      let mut args = args.clone();
      args.sort();
      let seed = opts.seed.or(match name.as_str() {
        "bootstrap" | "chain" | "ccs" => Some(101),
        _ => None,
      });
      if let Some(s) = seed {
        args.retain(|a| !a.starts_with("seed="));
        args.push(format!("seed={s}"));
      }
      config.insert("mode", "scenario".into());
      config.insert("name", name.clone());
      config.insert("args", args.join(" "));
      rec.set("mode", "scenario");
      let mut argv = vec![name.clone()];
      argv.extend(args);
      (Ok(scenario_bin()), argv, seed)
    }
    Target::Test { path } => {
      config.insert("mode", "test".into());
      config.insert("name", path.clone());
      config.insert("include_ignored", opts.include_ignored.to_string());
      rec.set("mode", "test");
      rec.set("workload", format!("test:{path}"));
      let mut argv = vec![path.clone(), "--exact".into(), "--test-threads=1".into()];
      if opts.include_ignored {
        argv.push("--include-ignored".into());
      }
      (test_bin(), argv, opts.seed)
    }
  };
  rec.set_opt("seed", seed, "run takes no seed");
  let config_json = serde_json::to_string(&config).unwrap();
  rec.set("config_hash", sha256_hex(config_json.as_bytes()));
  rec.set("details", Value::Object(Map::new()));

  let program = match program {
    Ok(p) => p,
    Err(e) => return finish_without_child(rec, &out_file, &e),
  };
  rec.set(
    "command",
    std::iter::once(rel(&program))
      .chain(args.iter().cloned())
      .collect::<Vec<_>>()
      .join(" "),
  );

  let child_env = vec![
    ("RAYON_NUM_THREADS".to_string(), opts.threads.to_string()),
    ("RUST_BACKTRACE".to_string(), "0".to_string()),
  ];
  let spec = RunSpec {
    program: &program,
    args: &args,
    env: &child_env,
    cwd: &repo_root(),
    stdout: &log_out,
    stderr: &log_err,
    timeout: Duration::from_secs(opts.timeout_s),
    mem_cap_bytes: opts.mem_cap_mb.map(|m| m * 1024 * 1024),
  };
  let outcome = match run_child(&spec) {
    Ok(o) => o,
    Err(e) => {
      return finish_without_child(rec, &out_file, &format!("spawn {}: {e}", program.display()))
    }
  };

  rec.set("wall_ms", outcome.wall_ms);
  rec.set("cpu_user_ms", outcome.cpu_user_ms);
  rec.set("cpu_sys_ms", outcome.cpu_sys_ms);
  rec.set("peak_rss_bytes", outcome.peak_rss_bytes);
  rec.set_opt(
    "exit_code",
    outcome.exit_code,
    "child was terminated by a signal",
  );
  rec.set_opt("signal", outcome.signal, "child exited normally");
  rec.set("mem_cap_enforced", outcome.mem_cap_enforced);

  let stdout = std::fs::read_to_string(&log_out).unwrap_or_default();
  let stderr = std::fs::read_to_string(&log_err).unwrap_or_default();

  // Interpret the child's own report.
  let mut child_ok = false;
  let mut child_error: Option<String> = None;
  match target {
    Target::Scenario { .. } => {
      let line = stdout.lines().rev().find(|l| l.starts_with(RESULT_PREFIX));
      match line.map(|l| serde_json::from_str::<Value>(&l[RESULT_PREFIX.len()..])) {
        Some(Ok(v)) => {
          let empty = Map::new();
          let fields = v["fields"].as_object().unwrap_or(&empty);
          let reasons = v["null_reasons"].as_object().unwrap_or(&empty);
          if let Err(e) = rec.merge_scenario(fields, reasons) {
            child_error = Some(e);
          } else {
            child_ok = v["ok"] == true;
            child_error = v["error"].as_str().map(String::from);
          }
          let mut details = v["details"].as_object().cloned().unwrap_or_default();
          if let Some(t) = details.remove("threads_actual") {
            rec.set("threads", t);
          }
          rec.set("details", Value::Object(details));
        }
        Some(Err(e)) => child_error = Some(format!("unparsable result line: {e}")),
        None => {
          child_error = Some(format!(
            "no KN-RESULT line on stdout; stderr tail:\n{}",
            tail(&stderr, 20)
          ))
        }
      }
    }
    Target::Test { path } => {
      rec.null(
        "threads",
        "libtest run: compute threads are not reported by the test binary",
      );
      match libtest_counts(&stdout) {
        Some((passed, failed, ignored)) => {
          rec.set(
            "details",
            serde_json::json!({"passed": passed, "failed": failed, "ignored": ignored}),
          );
          child_ok = passed == 1 && failed == 0;
          if !child_ok {
            child_error = Some(if passed + failed == 0 && ignored > 0 {
              format!("'{path}' is #[ignore]d and did not run; pass --include-ignored to run it")
            } else if passed + failed == 0 {
              format!("0 tests ran: no test named exactly '{path}'")
            } else {
              format!(
                "libtest: {passed} passed, {failed} failed, {ignored} ignored\n{}",
                tail(&stdout, 30)
              )
            });
          }
        }
        None => child_error = Some("no libtest summary line".into()),
      }
    }
  }

  let killed_by_os = outcome.signal == Some(libc::SIGKILL) && !outcome.timed_out;
  let alloc_failed = stderr.contains("memory allocation of") || stderr.contains("out of memory");
  let status = if outcome.timed_out {
    "timeout"
  } else if killed_by_os || alloc_failed {
    "oom"
  } else if outcome.exit_code == Some(0) && child_ok {
    "success"
  } else {
    "failure"
  };
  rec.set("status", status);
  match status {
    "success" => rec.null("error_message", "run succeeded"),
    "timeout" => rec.set(
      "error_message",
      format!("killed by kn-run after the {} s timeout", opts.timeout_s),
    ),
    "oom" => rec.set(
      "error_message",
      format!(
        "out of memory (signal {:?}); stderr tail:\n{}",
        outcome.signal,
        tail(&stderr, 10)
      ),
    ),
    _ => rec.set(
      "error_message",
      child_error.unwrap_or_else(|| {
        format!(
          "exit {:?}, signal {:?}; stderr tail:\n{}",
          outcome.exit_code,
          outcome.signal,
          tail(&stderr, 20)
        )
      }),
    ),
  }

  let fallback = match target {
    Target::Scenario { name, .. } => format!("not reported by scenario '{name}'"),
    Target::Test { .. } => "libtest run: no structured result".to_string(),
  };
  let done = rec.finish(&fallback);
  write_record(&out_file, &done);
  done
}

fn finish_without_child(mut rec: record::Record, out_file: &Path, err: &str) -> Map<String, Value> {
  rec.set("status", "failure");
  rec.set("error_message", err.to_string());
  let done = rec.finish("the child process was not started");
  write_record(out_file, &done);
  done
}

fn write_record(out_file: &Path, rec: &Map<String, Value>) {
  if let Err(e) = record::validate(rec) {
    eprintln!("[kn-run] BUG: invalid record: {e}");
  }
  if let Err(e) = record::append_jsonl(out_file, rec) {
    eprintln!("[kn-run] cannot append to {}: {e}", out_file.display());
    std::process::exit(3);
  }
  eprintln!(
    "[kn-run] {} {} {} wall={:.1}ms peak_rss={:.1}MiB -> {}",
    rec["run_id"].as_str().unwrap_or("?"),
    rec["command"].as_str().unwrap_or("?"),
    rec["status"].as_str().unwrap_or("?"),
    rec["wall_ms"].as_f64().unwrap_or(f64::NAN),
    rec["peak_rss_bytes"].as_f64().unwrap_or(f64::NAN) / (1024.0 * 1024.0),
    rel(out_file)
  );
}

// ---------------------------------------------------------------------------------------------
// selfcheck: the P1 acceptance checks (docs/P1-plan.md §4)

struct Checks {
  results: Vec<(String, bool, String)>,
}

impl Checks {
  fn check(&mut self, name: &str, ok: bool, detail: String) {
    eprintln!(
      "[selfcheck] {} {name}: {detail}",
      if ok { "PASS" } else { "FAIL" }
    );
    self.results.push((name.to_string(), ok, detail));
  }
}

fn scenario(name: &str, args: &[&str]) -> Target {
  Target::Scenario {
    name: name.into(),
    args: args.iter().map(|s| s.to_string()).collect(),
  }
}

fn f(rec: &Map<String, Value>, k: &str) -> f64 {
  rec[k].as_f64().unwrap_or(f64::NAN)
}

fn s<'a>(rec: &'a Map<String, Value>, k: &str) -> &'a str {
  rec[k].as_str().unwrap_or("")
}

fn selfcheck(opts: &Opts) -> bool {
  const MIB: f64 = 1024.0 * 1024.0;
  let mut c = Checks {
    results: Vec::new(),
  };
  let exp = "p1-selfcheck";
  let mut all = Vec::new();

  // Timing and RSS boundaries. The first exec of a freshly built binary can be slow (on macOS
  // the first launch is checked by the OS), so a warm-up noop runs first and is recorded as such.
  let mut warm = opts.clone();
  warm.warmup = true;
  let cold = execute(&scenario("noop", &[]), &warm, exp);
  eprintln!(
    "[selfcheck] INFO warm-up noop: wall={:.1}ms",
    f(&cold, "wall_ms")
  );
  all.push(cold);
  let noop = execute(&scenario("noop", &[]), opts, exp);
  c.check(
    "noop succeeds in < 100 ms (spawn + exit)",
    s(&noop, "status") == "success" && f(&noop, "wall_ms") < 100.0,
    format!(
      "wall={:.1}ms rss={:.1}MiB",
      f(&noop, "wall_ms"),
      f(&noop, "peak_rss_bytes") / MIB
    ),
  );
  let base_rss = f(&noop, "peak_rss_bytes");
  all.push(noop);

  let sleep = execute(&scenario("sleep", &["ms=200"]), opts, exp);
  let measured = sleep["details"]["sleep_ms_measured"]
    .as_f64()
    .unwrap_or(f64::NAN);
  c.check(
    "sleep 200ms: wall in [200, 350] ms, in-process timer in [200, 210] ms",
    s(&sleep, "status") == "success"
      && (200.0..=350.0).contains(&f(&sleep, "wall_ms"))
      && (200.0..=210.0).contains(&measured),
    format!("wall={:.1}ms inproc={measured:.2}ms", f(&sleep, "wall_ms")),
  );
  all.push(sleep);

  for mib in [128u64, 512] {
    let n = (mib * 1024 * 1024) as f64;
    let r = execute(
      &scenario("alloc", &[&format!("bytes={}", mib * 1024 * 1024)]),
      opts,
      exp,
    );
    let delta = f(&r, "peak_rss_bytes") - base_rss;
    c.check(
      &format!("alloc {mib} MiB: peak RSS - noop in [0.95N, 1.10N + 8 MiB]"),
      s(&r, "status") == "success" && delta >= 0.95 * n && delta <= 1.10 * n + 8.0 * MIB,
      format!("delta={:.1}MiB", delta / MIB),
    );
    all.push(r);
  }

  // Every outcome produces a record with a status.
  let fail = execute(&scenario("fail", &[]), opts, exp);
  c.check(
    "panicking scenario -> failure with message",
    s(&fail, "status") == "failure" && s(&fail, "error_message").contains("deliberate failure"),
    s(&fail, "error_message")
      .lines()
      .last()
      .unwrap_or("")
      .to_string(),
  );
  all.push(fail);

  let mut short = opts.clone();
  short.timeout_s = 1;
  let to = execute(&scenario("sleep", &["ms=5000"]), &short, exp);
  c.check(
    "sleep 5s with 1s timeout -> timeout",
    s(&to, "status") == "timeout" && f(&to, "wall_ms") < 2500.0,
    format!("wall={:.1}ms", f(&to, "wall_ms")),
  );
  all.push(to);

  let unknown = execute(&scenario("no-such-scenario", &[]), opts, exp);
  c.check(
    "unknown scenario -> failure",
    s(&unknown, "status") == "failure",
    s(&unknown, "error_message").to_string(),
  );
  all.push(unknown);

  if cfg!(target_os = "linux") {
    let mut capped = opts.clone();
    capped.mem_cap_mb = Some(256);
    let oom = execute(
      &scenario("alloc", &[&format!("bytes={}", 1u64 << 30)]),
      &capped,
      exp,
    );
    c.check(
      "alloc 1 GiB under a 256 MiB RLIMIT_AS -> oom",
      s(&oom, "status") == "oom",
      s(&oom, "status").to_string(),
    );
    all.push(oom);
  } else {
    eprintln!("[selfcheck] SKIP oom classification: RLIMIT_AS is not enforced on this OS");
  }

  if !opts.quick {
    // Determinism: the same configuration gives the same semantic inputs and results.
    let same = |a: &Map<String, Value>, b: &Map<String, Value>| {
      ["config_hash", "input_digest", "result_digest"]
        .iter()
        .all(|k| a[*k] == b[*k] && !a[*k].is_null())
    };
    for (name, args) in [
      ("constraints", vec!["variant=direct"]),
      ("bootstrap", vec!["variant=direct"]),
    ] {
      let mut o = opts.clone();
      o.seed = None;
      let r1 = execute(&scenario(name, &args), &o, exp);
      let r2 = execute(&scenario(name, &args), &o, exp);
      c.check(
        &format!("{name} direct twice -> success, identical config/input/result digests"),
        s(&r1, "status") == "success" && s(&r2, "status") == "success" && same(&r1, &r2),
        format!(
          "{} / {}; m_aug={} setup_iterations={} threads={}",
          s(&r1, "status"),
          s(&r2, "status"),
          r1["m_aug"],
          r1["setup_iterations"],
          r1["threads"]
        ),
      );
      c.check(
        &format!("{name}: actual thread count recorded and equals the request"),
        r1["threads"].as_u64() == Some(opts.threads as u64),
        format!("threads={}", r1["threads"]),
      );
      if name == "bootstrap" {
        let mut o2 = opts.clone();
        o2.seed = Some(202);
        let r3 = execute(&scenario(name, &args), &o2, exp);
        c.check(
          "bootstrap seed 202 -> success, different input_digest than seed 101",
          s(&r3, "status") == "success" && r3["input_digest"] != r1["input_digest"],
          s(&r3, "status").to_string(),
        );
        all.push(r3);
      }
      all.push(r1);
      all.push(r2);
    }

    let span = execute(&scenario("constraints", &["variant=span"]), opts, exp);
    c.check(
      "constraints span -> success",
      s(&span, "status") == "success",
      format!("m_aug={}", span["m_aug"]),
    );
    all.push(span);

    let chain = execute(
      &scenario("chain", &["variant=direct", "steps=2"]),
      opts,
      exp,
    );
    c.check(
      "chain steps=2 -> failure recorded with the B15 message",
      s(&chain, "status") == "failure" && s(&chain, "error_message").contains("B15"),
      s(&chain, "error_message").to_string(),
    );
    all.push(chain);

    let t = execute(
      &Target::Test {
        path: "kilonova::tests::no_such_test".into(),
      },
      opts,
      exp,
    );
    c.check(
      "kn-run test with no matching test -> failure",
      s(&t, "status") == "failure",
      s(&t, "error_message").to_string(),
    );
    all.push(t);
  }

  let invalid = all
    .iter()
    .filter_map(|r| record::validate(r).err())
    .collect::<Vec<_>>();
  c.check(
    "every record has all schema fields, a status, and a reason for each null",
    invalid.is_empty(),
    format!(
      "{} records, {} invalid {:?}",
      all.len(),
      invalid.len(),
      invalid
    ),
  );

  let failed = c.results.iter().filter(|r| !r.1).count();
  eprintln!("[selfcheck] {} checks, {} failed", c.results.len(), failed);
  failed == 0
}

fn main() {
  let argv: Vec<String> = std::env::args().skip(1).collect();
  let (opts, pos) = parse(&argv).unwrap_or_else(|e| {
    eprintln!("kn-run: {e}");
    usage()
  });
  let Some(cmd) = pos.first() else { usage() };
  let rec = match cmd.as_str() {
    "scenario" => {
      let Some(name) = pos.get(1) else { usage() };
      execute(
        &Target::Scenario {
          name: name.clone(),
          args: pos[2..].to_vec(),
        },
        &opts,
        "adhoc",
      )
    }
    "test" => {
      let Some(path) = pos.get(1) else { usage() };
      execute(&Target::Test { path: path.clone() }, &opts, "adhoc")
    }
    "selfcheck" => std::process::exit(if selfcheck(&opts) { 0 } else { 1 }),
    _ => usage(),
  };
  println!("{}", serde_json::to_string(&rec).unwrap());
  std::process::exit(if rec["status"] == "success" { 0 } else { 1 });
}
