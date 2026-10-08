//! KiloNova P1 experiment harness (PLAN.md §3 P1, §7, §8).
//!
//! `kn-run` runs one named scenario (`kn-scenario`) or one libtest test in a fresh process,
//! measures wall time and the child's peak RSS with `wait4`, and appends one JSON record per
//! run to `results/raw/*.jsonl`. The record layout is `results/schema.json`.
pub mod env;
pub mod proc;
pub mod record;

use sha2::{Digest, Sha256};
use std::path::PathBuf;

/// Prefix of the single result line a scenario prints on stdout.
pub const RESULT_PREFIX: &str = "KN-RESULT ";

/// Repository root: `KN_REPO_ROOT` if set, otherwise the checkout this crate was built from.
pub fn repo_root() -> PathBuf {
  std::env::var_os("KN_REPO_ROOT")
    .map(PathBuf::from)
    .unwrap_or_else(|| PathBuf::from(concat!(env!("CARGO_MANIFEST_DIR"), "/../..")))
}

/// Lower-case hex SHA-256 of `data`.
pub fn sha256_hex(data: &[u8]) -> String {
  hex(&Sha256::digest(data))
}

pub fn hex(bytes: &[u8]) -> String {
  bytes.iter().map(|b| format!("{b:02x}")).collect()
}

/// UTC timestamp `YYYY-MM-DDTHH:MM:SS.mmmZ` (RFC 3339).
pub fn utc_timestamp(t: std::time::SystemTime) -> String {
  let d = t.duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
  let secs = d.as_secs() as i64;
  let (days, rem) = (secs.div_euclid(86_400), secs.rem_euclid(86_400));
  // Civil-from-days (H. Hinnant).
  let z = days + 719_468;
  let era = z.div_euclid(146_097);
  let doe = z - era * 146_097;
  let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
  let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
  let mp = (5 * doy + 2) / 153;
  let day = doy - (153 * mp + 2) / 5 + 1;
  let month = if mp < 10 { mp + 3 } else { mp - 9 };
  let year = yoe + era * 400 + i64::from(month <= 2);
  format!(
    "{year:04}-{month:02}-{day:02}T{:02}:{:02}:{:02}.{:03}Z",
    rem / 3600,
    rem % 3600 / 60,
    rem % 60,
    d.subsec_millis()
  )
}

/// `n` random bytes from the OS, hex encoded.
pub fn random_hex(n: usize) -> String {
  use std::io::Read;
  let mut buf = vec![0u8; n];
  if std::fs::File::open("/dev/urandom")
    .and_then(|mut f| f.read_exact(&mut buf))
    .is_err()
  {
    let nanos = std::time::SystemTime::now()
      .duration_since(std::time::UNIX_EPOCH)
      .unwrap_or_default()
      .as_nanos();
    let seed = format!("{nanos}-{}", std::process::id());
    buf.copy_from_slice(&Sha256::digest(seed.as_bytes())[..n]);
  }
  hex(&buf)
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::time::{Duration, UNIX_EPOCH};

  #[test]
  fn timestamp_known_values() {
    assert_eq!(utc_timestamp(UNIX_EPOCH), "1970-01-01T00:00:00.000Z");
    assert_eq!(
      utc_timestamp(UNIX_EPOCH + Duration::from_millis(1_791_331_200_123)),
      "2026-10-07T00:00:00.123Z"
    );
    assert_eq!(
      utc_timestamp(UNIX_EPOCH + Duration::from_secs(951_782_400)),
      "2000-02-29T00:00:00.000Z"
    );
  }
}
