//! The JSONL run record (PLAN.md §8). `results/schema.json` lists the same fields.
use serde_json::{Map, Value};
use std::{fs::OpenOptions, io::Write, path::Path};

/// Version of the record layout. Bump it when `FIELDS` or a field's meaning changes.
pub const RECORD_VERSION: u64 = 1;

/// Every key of a record, in output order. All keys are always present; a key that does not
/// apply is `null` and has an entry in `null_reasons`.
pub const FIELDS: &[&str] = &[
  "record_version",
  "run_id",
  "timestamp",
  "experiment_id",
  "config_hash",
  "mode",
  "command",
  "scheme",
  "implementation_commit",
  "implementation_dirty",
  "dependency_lock_hash",
  "cargo_lock_hash",
  "protocol_version",
  "transcript_version",
  "machine_id",
  "machine",
  "rust_version",
  "build_flags",
  "threads",
  "threads_requested",
  "security_profile",
  "workload",
  "input_digest",
  "result_digest",
  "seed",
  "repetition",
  "warmup",
  "K",
  "T",
  "L",
  "a",
  "mu",
  "nu",
  "d",
  "t",
  "q",
  "m_app",
  "n_app",
  "w_app",
  "m_aug",
  "n_aug",
  "padding",
  "N_total",
  "setup_iterations",
  "setup_ms",
  "witness_ms",
  "recursive_ms",
  "compression_ms",
  "verify_warm_ms",
  "verify_cold_ms",
  "wall_ms",
  "cpu_user_ms",
  "cpu_sys_ms",
  "peak_rss_bytes",
  "checkpoint_bytes",
  "public_state_bytes",
  "proof_bytes",
  "statement_bytes",
  "vk_bytes",
  "verification_ok",
  "status",
  "error_message",
  "exit_code",
  "signal",
  "timeout_s",
  "mem_cap_bytes",
  "mem_cap_enforced",
  "log_stdout",
  "log_stderr",
  "null_reasons",
  "details",
];

/// Fields a scenario may set through its `KN-RESULT` line. Everything else is owned by the
/// runner, so a scenario cannot overwrite measurement or provenance fields.
pub const SCENARIO_FIELDS: &[&str] = &[
  "scheme",
  "protocol_version",
  "transcript_version",
  "build_flags",
  "security_profile",
  "workload",
  "input_digest",
  "result_digest",
  "K",
  "T",
  "L",
  "a",
  "mu",
  "nu",
  "d",
  "t",
  "q",
  "m_app",
  "n_app",
  "w_app",
  "m_aug",
  "n_aug",
  "padding",
  "N_total",
  "setup_iterations",
  "setup_ms",
  "witness_ms",
  "recursive_ms",
  "compression_ms",
  "verify_warm_ms",
  "verify_cold_ms",
  "checkpoint_bytes",
  "public_state_bytes",
  "proof_bytes",
  "statement_bytes",
  "vk_bytes",
  "verification_ok",
];

/// Reasons for fields that are null in every P1 record unless a scenario fills them.
fn default_null_reason(field: &str) -> Option<&'static str> {
  Some(match field {
    "compression_ms" | "proof_bytes" | "verify_cold_ms" | "statement_bytes" | "vk_bytes" => {
      "not implemented before P7 (compression and independent final verifier)"
    }
    "public_state_bytes" => {
      "no public uncompressed state is separated from the private checkpoint before P7"
    }
    "witness_ms" => "witness generation is inside recursive_ms and not separately timed in P1",
    "L" | "a" => "no PCD tree before P6",
    _ => return None,
  })
}

/// A run record under construction.
pub struct Record {
  map: Map<String, Value>,
  reasons: Map<String, Value>,
}

impl Default for Record {
  fn default() -> Self {
    Self::new()
  }
}

impl Record {
  pub fn new() -> Self {
    let mut map = Map::new();
    for f in FIELDS {
      map.insert((*f).to_string(), Value::Null);
    }
    map.insert("record_version".into(), RECORD_VERSION.into());
    Self {
      map,
      reasons: Map::new(),
    }
  }

  pub fn set(&mut self, field: &str, value: impl Into<Value>) {
    assert!(
      FIELDS.contains(&field) && field != "null_reasons",
      "unknown record field {field}"
    );
    self.map.insert(field.to_string(), value.into());
  }

  pub fn get(&self, field: &str) -> &Value {
    &self.map[field]
  }

  /// Sets `field` to `value`, or to null with `reason` when `value` is `None`.
  pub fn set_opt<T: Into<Value>>(&mut self, field: &str, value: Option<T>, reason: &str) {
    match value {
      Some(v) => self.set(field, v),
      None => self.null(field, reason),
    }
  }

  /// Marks `field` as not applicable.
  pub fn null(&mut self, field: &str, reason: &str) {
    self.set(field, Value::Null);
    self.reasons.insert(field.to_string(), reason.into());
  }

  /// Merges a scenario's `fields` and `null_reasons`. Unknown or runner-owned keys are an error.
  pub fn merge_scenario(
    &mut self,
    fields: &Map<String, Value>,
    reasons: &Map<String, Value>,
  ) -> Result<(), String> {
    for (k, v) in fields {
      if !SCENARIO_FIELDS.contains(&k.as_str()) {
        return Err(format!("scenario set field '{k}', which it does not own"));
      }
      self.set(k, v.clone());
    }
    for (k, v) in reasons {
      if !FIELDS.contains(&k.as_str()) {
        return Err(format!(
          "scenario gave a null reason for unknown field '{k}'"
        ));
      }
      self.reasons.insert(k.clone(), v.clone());
    }
    Ok(())
  }

  /// Fills `null_reasons` for every remaining null field and returns the finished record.
  pub fn finish(mut self, fallback: &str) -> Map<String, Value> {
    let mut reasons = Map::new();
    for f in FIELDS {
      if *f == "null_reasons" || !self.map[*f].is_null() {
        continue;
      }
      let reason = self
        .reasons
        .get(*f)
        .cloned()
        .or_else(|| default_null_reason(f).map(Value::from))
        .unwrap_or_else(|| Value::from(fallback));
      reasons.insert((*f).to_string(), reason);
    }
    self
      .map
      .insert("null_reasons".into(), Value::Object(reasons));
    self.map
  }
}

/// Appends one record as a single line. Records are never rewritten.
pub fn append_jsonl(path: &Path, record: &Map<String, Value>) -> std::io::Result<()> {
  if let Some(dir) = path.parent() {
    std::fs::create_dir_all(dir)?;
  }
  let mut line = serde_json::to_string(record).map_err(std::io::Error::other)?;
  line.push('\n');
  let mut f = OpenOptions::new().create(true).append(true).open(path)?;
  f.write_all(line.as_bytes())
}

/// Checks the invariants every record must satisfy: exactly the `FIELDS` keys, a status, and a
/// reason for every null field.
pub fn validate(record: &Map<String, Value>) -> Result<(), String> {
  for f in FIELDS {
    if !record.contains_key(*f) {
      return Err(format!("missing field {f}"));
    }
  }
  if let Some(k) = record.keys().find(|k| !FIELDS.contains(&k.as_str())) {
    return Err(format!("unexpected field {k}"));
  }
  match record["status"].as_str() {
    Some("success" | "failure" | "timeout" | "oom") => {}
    other => return Err(format!("invalid status {other:?}")),
  }
  let reasons = record["null_reasons"]
    .as_object()
    .ok_or("null_reasons is not an object")?;
  for f in FIELDS {
    if *f != "null_reasons" && record[*f].is_null() && !reasons.contains_key(*f) {
      return Err(format!("null field {f} has no reason"));
    }
  }
  Ok(())
}
