//! Child-process execution with `wait4` resource accounting, timeout and an optional memory cap.
use std::{
  fs::File,
  path::Path,
  process::{Command, Stdio},
  time::{Duration, Instant},
};

/// How a child process ended, as seen by the runner.
#[derive(Clone, Debug)]
pub struct ChildOutcome {
  /// Wall time from spawn to reap, in milliseconds. Includes process start-up.
  pub wall_ms: f64,
  /// Peak resident set size of the child, in bytes (`ru_maxrss`, normalised).
  pub peak_rss_bytes: u64,
  pub cpu_user_ms: f64,
  pub cpu_sys_ms: f64,
  pub exit_code: Option<i32>,
  pub signal: Option<i32>,
  /// The runner killed the child because it exceeded the timeout.
  pub timed_out: bool,
  /// The memory cap was applied with `RLIMIT_AS` (Linux only).
  pub mem_cap_enforced: bool,
}

/// Options for one child run.
pub struct RunSpec<'a> {
  pub program: &'a Path,
  pub args: &'a [String],
  pub env: &'a [(String, String)],
  pub cwd: &'a Path,
  pub stdout: &'a Path,
  pub stderr: &'a Path,
  pub timeout: Duration,
  pub mem_cap_bytes: Option<u64>,
}

fn timeval_ms(tv: libc::timeval) -> f64 {
  tv.tv_sec as f64 * 1e3 + tv.tv_usec as f64 / 1e3
}

/// `ru_maxrss` is in bytes on macOS and in KiB on Linux and the BSDs.
fn maxrss_bytes(ru_maxrss: libc::c_long) -> u64 {
  let v = ru_maxrss.max(0) as u64;
  if cfg!(target_os = "macos") {
    v
  } else {
    v * 1024
  }
}

#[cfg(target_os = "linux")]
fn apply_mem_cap(cmd: &mut Command, cap: Option<u64>) -> bool {
  use std::os::unix::process::CommandExt;
  let Some(cap) = cap else { return false };
  // SAFETY: setrlimit is async-signal-safe and touches no allocator state.
  unsafe {
    cmd.pre_exec(move || {
      let lim = libc::rlimit {
        rlim_cur: cap as libc::rlim_t,
        rlim_max: cap as libc::rlim_t,
      };
      if libc::setrlimit(libc::RLIMIT_AS, &lim) != 0 {
        return Err(std::io::Error::last_os_error());
      }
      Ok(())
    });
  }
  true
}

#[cfg(not(target_os = "linux"))]
fn apply_mem_cap(_cmd: &mut Command, _cap: Option<u64>) -> bool {
  // macOS does not enforce RLIMIT_AS; the cap is recorded as not enforced.
  false
}

/// Spawns the child, waits for it with `wait4` and returns its outcome. stdout and stderr go
/// to the given files. Only spawn failures are returned as `Err`.
pub fn run_child(spec: &RunSpec<'_>) -> std::io::Result<ChildOutcome> {
  let mut cmd = Command::new(spec.program);
  cmd
    .args(spec.args)
    .current_dir(spec.cwd)
    .stdin(Stdio::null())
    .stdout(File::create(spec.stdout)?)
    .stderr(File::create(spec.stderr)?);
  for (k, v) in spec.env {
    cmd.env(k, v);
  }
  let mem_cap_enforced = apply_mem_cap(&mut cmd, spec.mem_cap_bytes);

  let start = Instant::now();
  let child = cmd.spawn()?;
  let pid = child.id() as libc::pid_t;
  // The child is reaped with wait4 below; std's handle must not wait on it again.
  drop(child);

  let deadline = start + spec.timeout;
  let mut timed_out = false;
  let mut status: libc::c_int = 0;
  // SAFETY: rusage is plain old data.
  let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
  loop {
    // SAFETY: valid pointers to locals; pid is our own unreaped child.
    let r = unsafe { libc::wait4(pid, &mut status, libc::WNOHANG, &mut usage) };
    if r == pid {
      break;
    }
    if r < 0 {
      let err = std::io::Error::last_os_error();
      if err.kind() == std::io::ErrorKind::Interrupted {
        continue;
      }
      return Err(err);
    }
    if !timed_out && Instant::now() >= deadline {
      timed_out = true;
      // SAFETY: the child has not been reaped yet, so the pid cannot have been reused.
      unsafe { libc::kill(pid, libc::SIGKILL) };
    }
    // Fine polling while short runs finish, so wall_ms stays accurate for calibration.
    let poll = if start.elapsed() < Duration::from_millis(100) {
      Duration::from_millis(1)
    } else {
      Duration::from_millis(10)
    };
    std::thread::sleep(poll);
  }
  let wall_ms = start.elapsed().as_secs_f64() * 1e3;

  let (exit_code, signal) = if libc::WIFEXITED(status) {
    (Some(libc::WEXITSTATUS(status)), None)
  } else if libc::WIFSIGNALED(status) {
    (None, Some(libc::WTERMSIG(status)))
  } else {
    (None, None)
  };

  Ok(ChildOutcome {
    wall_ms,
    peak_rss_bytes: maxrss_bytes(usage.ru_maxrss),
    cpu_user_ms: timeval_ms(usage.ru_utime),
    cpu_sys_ms: timeval_ms(usage.ru_stime),
    exit_code,
    signal,
    timed_out,
    mem_cap_enforced,
  })
}
