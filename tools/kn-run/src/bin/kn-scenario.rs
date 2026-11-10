//! `kn-scenario <name> [key=value ...]`: runs one named scenario in this process and prints a
//! single `KN-RESULT {json}` line on stdout. It is normally started by `kn-run`, which owns the
//! wall-time, RSS and provenance fields. Phase timings here cover only the named call.
use ff::{Field, PrimeField};
use kn_run::{hex, sha256_hex, RESULT_PREFIX};
use nova_snark::{
  constants::{NUM_CHALLENGE_BITS, NUM_HASH_BITS},
  kilonova::{self, test_utils::ExamplePredicates, transcript::HFS_TRANSCRIPT_VERSION},
  provider::{PallasEngine, VestaEngine},
  traits::{snark::default_ck_hint, Engine},
};
use rand_chacha::ChaCha20Rng;
use rand_core::{RngCore, SeedableRng};
use serde_json::{json, Map, Value};
use std::{collections::BTreeMap, time::Instant};

type E1 = PallasEngine;
type E2 = VestaEngine;
type F1 = <E1 as Engine>::Scalar;

/// Name of the predicate family used by the kilonova scenarios.
const FAMILY: &str = "example-k3";
const FAMILY_K: usize = 3;

struct Output {
  fields: Map<String, Value>,
  null_reasons: Map<String, Value>,
  details: Map<String, Value>,
}

impl Output {
  fn new() -> Self {
    Self {
      fields: Map::new(),
      null_reasons: Map::new(),
      details: Map::new(),
    }
  }
  fn f(&mut self, k: &str, v: impl Into<Value>) {
    self.fields.insert(k.into(), v.into());
  }
  fn why(&mut self, k: &str, reason: &str) {
    self.null_reasons.insert(k.into(), reason.into());
  }
  fn d(&mut self, k: &str, v: impl Into<Value>) {
    self.details.insert(k.into(), v.into());
  }
}

type Args = BTreeMap<String, String>;

fn parse_args(raw: &[String]) -> Result<Args, String> {
  raw
    .iter()
    .map(|a| {
      a.split_once('=')
        .map(|(k, v)| (k.to_string(), v.to_string()))
        .ok_or_else(|| format!("argument '{a}' is not key=value"))
    })
    .collect()
}

fn arg<T: std::str::FromStr>(args: &Args, key: &str, default: Option<T>) -> Result<T, String> {
  match args.get(key) {
    Some(v) => v
      .parse()
      .map_err(|_| format!("invalid value for {key}: '{v}'")),
    None => default.ok_or_else(|| format!("missing argument {key}=...")),
  }
}

/// Canonical digest of a scenario's semantic inputs.
fn digest_of(name: &str, parts: &[(&str, String)]) -> String {
  let mut s = name.to_string();
  for (k, v) in parts {
    s.push('|');
    s.push_str(k);
    s.push('=');
    s.push_str(v);
  }
  sha256_hex(s.as_bytes())
}

fn fe_hex<F: PrimeField>(f: &F) -> String {
  hex(f.to_repr().as_ref())
}

fn ms(t: Instant) -> f64 {
  t.elapsed().as_secs_f64() * 1e3
}

fn harness_reasons(out: &mut Output, scenario: &str) {
  let r = format!("harness calibration scenario '{scenario}' runs no protocol");
  for k in [
    "scheme",
    "K",
    "T",
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
    "recursive_ms",
    "verify_warm_ms",
    "checkpoint_bytes",
    "verification_ok",
  ] {
    out.why(k, &r);
  }
}

fn scenario_noop(out: &mut Output) {
  harness_reasons(out, "noop");
  out.f("workload", "calibration:noop");
  out.f("input_digest", digest_of("noop", &[]));
  out.f("result_digest", digest_of("noop", &[]));
}

fn scenario_sleep(out: &mut Output, args: &Args) -> Result<(), String> {
  let ms_req: u64 = arg(args, "ms", None)?;
  let t = Instant::now();
  std::thread::sleep(std::time::Duration::from_millis(ms_req));
  out.d("sleep_ms_requested", ms_req);
  out.d("sleep_ms_measured", ms(t));
  harness_reasons(out, "sleep");
  out.f("workload", "calibration:sleep");
  let digest = digest_of("sleep", &[("ms", ms_req.to_string())]);
  out.f("input_digest", digest.clone());
  out.f("result_digest", digest);
  Ok(())
}

fn scenario_alloc(out: &mut Output, args: &Args) -> Result<(), String> {
  let bytes: usize = arg(args, "bytes", None)?;
  let t = Instant::now();
  let mut buf = vec![0u8; bytes];
  // vec![0; n] may map lazily-zeroed pages; write one byte per page so all of them are resident.
  for i in (0..bytes).step_by(4096) {
    buf[i] = 1;
  }
  let touched = std::hint::black_box(&buf)
    .iter()
    .step_by(4096)
    .map(|b| *b as usize)
    .sum::<usize>();
  out.d("alloc_bytes", bytes);
  out.d("pages_touched", touched);
  out.d("alloc_ms", ms(t));
  drop(buf);
  harness_reasons(out, "alloc");
  out.f("workload", "calibration:alloc");
  let digest = digest_of("alloc", &[("bytes", bytes.to_string())]);
  out.f("input_digest", digest.clone());
  out.f("result_digest", digest);
  Ok(())
}

fn common_protocol_fields(out: &mut Output, variant: &str) {
  out.f("scheme", format!("kilonova-{variant}"));
  out.f("workload", FAMILY);
  out.f("K", FAMILY_K);
  // R1CS viewed as CCS: t = 3 matrices, q = 2 products (A·B and C), d = 2 (configs/common.toml).
  out.f("t", 3);
  out.f("q", 2);
  out.f("d", 2);
  out.f("mu", 1);
  out.f("nu", 1);
}

fn shape_json(s: &kilonova::ShapeSummary) -> Value {
  serde_json::to_value(s).unwrap()
}

/// Fills the size fields from a setup report and the predicate-only counts.
fn size_fields(
  out: &mut Output,
  report: &kilonova::SetupReport,
  app: &[kilonova::CountingSummary],
  arity: usize,
) {
  out.f(
    "m_app",
    app.iter().map(|c| c.num_constraints).max().unwrap(),
  );
  // Full assignment columns of the predicate alone: state inputs, internal witness, constant.
  out.f(
    "n_app",
    app.iter().map(|c| arity + c.num_aux + 1).max().unwrap(),
  );
  out.f("w_app", app.iter().map(|c| c.num_aux).max().unwrap());
  out.f(
    "m_aug",
    report.primary_raw.iter().map(|s| s.num_cons).max().unwrap(),
  );
  out.f(
    "n_aug",
    report
      .primary_raw
      .iter()
      .map(|s| s.num_vars + 1 + s.num_io)
      .max()
      .unwrap(),
  );
  out.f(
    "padding",
    json!({
      "primary_cons_padded": report.primary_padded.iter().map(|s| s.num_cons).max(),
      "primary_vars_padded": report.primary_padded.iter().map(|s| s.num_vars).max(),
      "secondary_cons_padded": report.secondary_padded.num_cons,
      "secondary_vars_padded": report.secondary_padded.num_vars,
    }),
  );
  out.f(
    "N_total",
    report.primary_raw.iter().map(|s| s.nnz).sum::<usize>(),
  );
  out.f("setup_iterations", report.iterations.len());
  out.d(
    "predicates",
    Value::Array(
      (0..app.len())
        .map(|id| {
          json!({
            "id": id,
            "app": serde_json::to_value(app[id]).unwrap(),
            "primary_raw": shape_json(&report.primary_raw[id]),
            "primary_padded": shape_json(&report.primary_padded[id]),
          })
        })
        .collect(),
    ),
  );
  out.d(
    "secondary",
    json!({
      "raw": shape_json(&report.secondary_raw),
      "padded": shape_json(&report.secondary_padded),
    }),
  );
  out.d("setup_report", serde_json::to_value(report).unwrap());
}

/// Seeded semantic inputs: z0 and the predicate trace.
fn seeded_inputs(seed: u64, steps: usize) -> (F1, Vec<usize>) {
  let mut rng = ChaCha20Rng::seed_from_u64(seed);
  let z0 = F1::random(&mut rng);
  let trace = (0..steps)
    .map(|_| (rng.next_u32() as usize) % FAMILY_K)
    .collect();
  (z0, trace)
}

macro_rules! protocol_scenarios {
  ($modname:ident, $variant:literal, $path:path) => {
    mod $modname {
      use super::*;
      use $path as v;

      type PS = ExamplePredicates<F1>;
      type PP = v::PublicParams<E1, E2, PS>;
      type Snark = v::RecursiveSNARK<E1, E2, PS>;

      fn setup(out: &mut Output) -> Result<(PP, kilonova::SetupReport), String> {
        let predicates = PS::default();
        let t = Instant::now();
        let (pp, report) =
          PP::setup_with_report(&predicates, &*default_ck_hint(), &*default_ck_hint())
            .map_err(|e| format!("setup failed: {e}"))?;
        out.f("setup_ms", ms(t));
        let app = (0..FAMILY_K)
          .map(|id| v::predicate_constraint_counts(&predicates, id))
          .collect::<Result<Vec<_>, _>>()
          .map_err(|e| format!("predicate count failed: {e}"))?;
        size_fields(out, &report, &app, 1);
        out.d("pp_digest", fe_hex(&pp.digest()));
        Ok((pp, report))
      }

      pub fn constraints(out: &mut Output) -> Result<(), String> {
        common_protocol_fields(out, $variant);
        let (pp, report) = setup(out)?;
        let r = "constraints scenario runs setup only";
        for k in ["T", "recursive_ms", "verify_warm_ms", "checkpoint_bytes", "verification_ok"] {
          out.why(k, r);
        }
        out.f(
          "input_digest",
          digest_of("constraints", &[("variant", $variant.into()), ("family", FAMILY.into())]),
        );
        let semantic = json!({
          "pp_digest": fe_hex(&pp.digest()),
          "report": serde_json::to_value(&report).unwrap(),
          "predicates": out.details["predicates"].clone(),
        });
        out.f("result_digest", sha256_hex(semantic.to_string().as_bytes()));
        Ok(())
      }

      /// setup, `RecursiveSNARK::new`, then `steps - 1` calls to `prove_step`, then `verify`.
      pub fn chain(out: &mut Output, seed: u64, steps: usize) -> Result<(), String> {
        if steps == 0 {
          return Err("steps must be >= 1".into());
        }
        common_protocol_fields(out, $variant);
        let predicates = PS::default();
        let (z0, trace) = seeded_inputs(seed, steps);
        out.f("T", steps);
        out.f(
          "input_digest",
          digest_of(
            "chain",
            &[
              ("variant", $variant.into()),
              ("family", FAMILY.into()),
              ("seed", seed.to_string()),
              ("z0", fe_hex(&z0)),
              ("trace", format!("{trace:?}")),
            ],
          ),
        );
        out.d("trace", format!("{trace:?}"));
        let (pp, _report) = setup(out)?;

        let t = Instant::now();
        let mut snark = Snark::new(&pp, &predicates, &[z0], trace[0])
          .map_err(|e| format!("RecursiveSNARK::new failed: {e}"))?;
        for (step, id) in trace.iter().enumerate().skip(1) {
          snark
            .prove_step(&pp, &predicates, *id)
            .map_err(|e| format!("prove_step {} failed: {e}", step + 1))?;
        }
        out.f("recursive_ms", ms(t));

        let checkpoint = bincode::serde::encode_to_vec(&snark, bincode::config::legacy())
          .map_err(|e| format!("serialize: {e}"))?;
        out.f("checkpoint_bytes", checkpoint.len());
        out.d(
          "checkpoint_note",
          "bincode(legacy) of RecursiveSNARK; private: includes folded witnesses",
        );

        let t = Instant::now();
        let res = snark.verify(&pp, steps, &[z0], &trace);
        out.f("verify_warm_ms", ms(t));
        let zn = res.map_err(|e| format!("verify failed: {e}"))?;

        let mut expected = vec![z0];
        for id in &trace {
          expected = predicates.output(*id, &expected);
        }
        let ok = zn == expected;
        out.f("verification_ok", ok);
        if !ok {
          return Err("verified output differs from native evaluation".into());
        }
        let zn_hex = zn.iter().map(fe_hex).collect::<Vec<_>>();
        out.d("zn", zn_hex.clone());
        let semantic = json!({
          "pp_digest": fe_hex(&pp.digest()),
          "zn": zn_hex,
          "checkpoint_bytes": checkpoint.len(),
        });
        out.f("result_digest", sha256_hex(semantic.to_string().as_bytes()));
        Ok(())
      }
    }
  };
}

protocol_scenarios!(direct, "direct", nova_snark::kilonova);
protocol_scenarios!(span, "span", nova_snark::kilonova::span);

/// P2: the fifth-power chain as native degree-5 CCS and as the equivalent R1CS, both checked
/// by the kn-ccs reference oracle. The input x0 is derived from the seed.
fn scenario_ccs(out: &mut Output, args: &Args) -> Result<(), String> {
  use kn_ccs::{encode::encode, gen};
  let steps: usize = arg(args, "steps", Some(64))?;
  let seed: u64 = arg(args, "seed", None)?;
  if steps == 0 {
    return Err("steps must be >= 1".into());
  }
  let x0 = F1::random(&mut ChaCha20Rng::seed_from_u64(seed));

  let t = Instant::now();
  let (native, a) = gen::fifth_power_native(steps, Some(x0)).map_err(|e| e.to_string())?;
  let native_build_ms = ms(t);
  let t = Instant::now();
  let (r1cs, b) = gen::fifth_power_r1cs(steps, Some(x0)).map_err(|e| e.to_string())?;
  let r1cs_build_ms = ms(t);
  let (a, b) = (a.unwrap(), b.unwrap());

  let t = Instant::now();
  let native_ok = native.is_satisfied(&a.z());
  let native_check_ms = ms(t);
  let t = Instant::now();
  let r1cs_ok = r1cs.is_satisfied(&b.z());
  let r1cs_check_ms = ms(t);
  let ok = native_ok.is_ok() && r1cs_ok.is_ok() && a.io == b.io;

  out.f("scheme", "kn-ccs-oracle");
  out.f("workload", "fifth-power-chain");
  out.f("T", steps);
  out.f("d", native.degree());
  out.f("t", native.t());
  out.f("q", native.q());
  out.f("m_app", native.m);
  out.f("n_app", native.n());
  out.f("w_app", native.num_w);
  out.f("N_total", native.nnz());
  out.f("verification_ok", ok);
  let r = "P2 oracle scenario: no folding, recursion or setup";
  for k in [
    "K",
    "mu",
    "nu",
    "m_aug",
    "n_aug",
    "padding",
    "setup_iterations",
    "setup_ms",
    "recursive_ms",
    "verify_warm_ms",
    "checkpoint_bytes",
  ] {
    out.why(k, r);
  }
  out.d(
    "native",
    json!({"m": native.m, "n": native.n(), "w": native.num_w, "nnz": native.nnz(),
           "t": native.t(), "q": native.q(), "d": native.degree(),
           "multiset0": native.template.multisets[0],
           "build_ms": native_build_ms, "check_ms": native_check_ms}),
  );
  out.d(
    "r1cs",
    json!({"m": r1cs.m, "n": r1cs.n(), "w": r1cs.num_w, "nnz": r1cs.nnz(),
           "t": r1cs.t(), "q": r1cs.q(), "d": r1cs.degree(),
           "build_ms": r1cs_build_ms, "check_ms": r1cs_check_ms}),
  );
  out.d(
    "r1cs_over_native",
    json!({"m": r1cs.m as f64 / native.m as f64,
           "w": r1cs.num_w as f64 / native.num_w.max(1) as f64,
           "nnz": r1cs.nnz() as f64 / native.nnz() as f64}),
  );
  out.f(
    "input_digest",
    digest_of(
      "ccs",
      &[
        ("steps", steps.to_string()),
        ("seed", seed.to_string()),
        ("x0", fe_hex(&x0)),
      ],
    ),
  );
  let mut sem = encode(&native);
  sem.extend(encode(&r1cs));
  for v in &a.io {
    sem.extend_from_slice(v.to_repr().as_ref());
  }
  out.f("result_digest", sha256_hex(&sem));
  if !ok {
    return Err(format!(
      "oracle rejected: native {native_ok:?}, r1cs {r1cs_ok:?}"
    ));
  }
  Ok(())
}

/// P3: native-field HFS (transcript v2) without recursion. Folds `steps` fresh instances of the
/// two-predicate wiring-pair family (alternating k = 0, 1) into one running instance: step 0 is
/// a (μ, ν) = (0, 1) fold, every later step a (1, 1) fold. Each step runs the prover, the
/// succinct verifier (whose output must equal the prover's), the native decider and the
/// independent kn-ccs oracle (plus the index opening). Times are per call, in process.
fn scenario_hfs(out: &mut Output, args: &Args) -> Result<(), String> {
  use kn_ccs::r#gen::PairTemplate;
  use nova_snark::kilonova::hfs::{Direct, Span};
  let tpl = match arg(args, "template", Some("r1cs".to_string()))?.as_str() {
    "r1cs" => PairTemplate::R1cs,
    "power5" => PairTemplate::Power5,
    t => return Err(format!("unknown template {t} (r1cs | power5)")),
  };
  let steps: usize = arg(args, "steps", Some(100))?;
  let reps: usize = arg(args, "reps", Some(1))?;
  let seed: u64 = arg(args, "seed", None)?;
  if steps == 0 || reps == 0 {
    return Err("steps and reps must be >= 1".into());
  }
  match arg(args, "variant", Some("direct".to_string()))?.as_str() {
    "direct" => hfs::run::<Direct>(out, tpl, steps, reps, seed),
    "span" => hfs::run::<Span>(out, tpl, steps, reps, seed),
    v => Err(format!("unknown variant {v}")),
  }
}

mod hfs {
  use super::*;
  use kn_ccs::{
    accs::check_accs,
    r#gen::{wiring_pair, PairTemplate},
    AccsInstance, Family,
  };
  use nova_snark::kilonova::hfs::{
    decide, CcsShape, CcsTemplate, HfsParams, IncomingInstance, RunningInstance, RunningWitness,
    Variant, NIFS,
  };

  fn bytes<T: serde::Serialize>(v: &T) -> Result<Vec<u8>, String> {
    bincode::serde::encode_to_vec(v, bincode::config::legacy()).map_err(|e| e.to_string())
  }

  fn stats(v: &[f64]) -> Value {
    let mut s = v.to_vec();
    s.sort_by(|a, b| a.partial_cmp(b).unwrap());
    let n = s.len();
    json!({
      "sum": s.iter().sum::<f64>(),
      "median": if n % 2 == 1 { s[n / 2] } else { (s[n / 2 - 1] + s[n / 2]) / 2.0 },
      "min": s[0],
      "max": s[n - 1],
    })
  }

  fn oracle<V: Variant<E1>>(
    pp: &HfsParams<E1>,
    fam: &Family<F1>,
    u: &RunningInstance<E1, V>,
    w: &RunningWitness<E1>,
  ) -> Result<(), String> {
    let accs = AccsInstance {
      comm_w: u.comm_w,
      u: u.u,
      io: u.io.clone(),
      lambda: w.lambda.clone(),
      r_x: u.r_x.clone(),
      r_y: u.r_y.clone(),
      v: u.v.clone(),
    };
    check_accs(fam, &accs, &w.w, |x| pp.commit_w(x).unwrap()).map_err(|e| e.to_string())?;
    V::check_opening(pp, &u.index, &w.lambda).map_err(|e| e.to_string())
  }

  pub fn run<V: Variant<E1>>(
    out: &mut Output,
    tpl: PairTemplate,
    steps: usize,
    reps: usize,
    seed: u64,
  ) -> Result<(), String> {
    let members = (0..2)
      .map(|k| wiring_pair::<F1>(tpl, k, reps, None).map(|c| c.0))
      .collect::<Result<Vec<_>, _>>()
      .map_err(|e| e.to_string())?;
    let fam = Family::new(members).map_err(|e| e.to_string())?;
    let c0 = fam.member(0);
    let shapes = (0..2)
      .map(|k| {
        let c = fam.member(k);
        let mats = c.matrices.iter().map(|m| m.entries().to_vec()).collect();
        CcsShape::new(c.m, c.num_w, c.num_io, mats)
      })
      .collect::<Result<Vec<_>, _>>()
      .map_err(|e| e.to_string())?;
    let template = CcsTemplate::new(
      c0.template.t,
      c0.template.multisets.clone(),
      c0.template.coeffs.clone(),
    )
    .map_err(|e| e.to_string())?;

    out.f("scheme", format!("kilonova-hfs-v2-{}", V::NAME));
    out.f("workload", format!("wiring-pair-{}-reps{reps}", tpl.name()));
    out.f("protocol_version", 2);
    out.f("transcript_version", 2);
    out.f(
      "security_profile",
      format!(
        "pallas (E1) native-field HFS v2, no recursion; pedersen; poseidon RO2 over E1::Scalar (D1 option (a) assumption); challenge {NUM_CHALLENGE_BITS} bits; non-ZK"
      ),
    );
    out.f("K", 2);
    out.f("T", steps);
    out.f("mu", 1);
    out.f("nu", 1);
    out.d(
      "mu_nu_note",
      "step 0 is a (mu, nu) = (0, 1) fold, steps 1.. are (1, 1)",
    );
    out.f("d", c0.degree());
    out.f("t", c0.t());
    out.f("q", c0.q());
    out.f("m_app", c0.m);
    out.f("n_app", c0.n());
    out.f("w_app", c0.num_w);
    out.f("N_total", c0.nnz() + fam.member(1).nnz());
    let r = "P3 native folding: no augmented circuit, no recursion";
    for k in ["m_aug", "n_aug", "padding", "setup_iterations"] {
      out.why(k, r);
    }
    out.why(
      "recursive_ms",
      "no recursion in P3; per-fold prover/verifier/decider times are in details.per_step",
    );
    out.why(
      "verify_warm_ms",
      "no RecursiveSNARK::verify in P3; per-fold verifier and decider times are in details.per_step",
    );
    out.why(
      "checkpoint_bytes",
      "no RecursiveSNARK checkpoint in P3; running witness bytes are in details",
    );
    out.why(
      "proof_bytes",
      "proof_bytes is the P7 compressed proof; per-fold NIFS proof bytes (bincode legacy) are in details.per_step.nifs_proof_bytes",
    );
    out.why(
      "public_state_bytes",
      "no recursive public state before P5; running-instance bytes are in details.per_step.instance_bytes",
    );

    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let xs: Vec<F1> = (0..steps).map(|_| F1::random(&mut rng)).collect();
    out.f(
      "input_digest",
      digest_of(
        "hfs",
        &[
          ("variant", V::NAME.into()),
          ("template", tpl.name().into()),
          ("reps", reps.to_string()),
          ("steps", steps.to_string()),
          ("seed", seed.to_string()),
          ("x0", fe_hex(&xs[0])),
        ],
      ),
    );

    let t = Instant::now();
    let pp = HfsParams::<E1>::new(template, shapes).map_err(|e| e.to_string())?;
    out.f("setup_ms", ms(t));
    out.d("hfs_digest", fe_hex(&pp.digest()));
    out.d(
      "dims",
      json!({"m": pp.m(), "n": pp.n(), "s": pp.s(), "s_prime": pp.s_prime(),
             "deg_x": pp.template().deg_x(), "num_w": pp.num_w(), "num_io": pp.num_io()}),
    );

    let (mut witness_ms, mut ok) = (0.0, true);
    let mut per = (
      Vec::new(),
      Vec::new(),
      Vec::new(),
      Vec::new(),
      Vec::new(),
      Vec::new(),
    );
    let mut acc: Option<(RunningInstance<E1, V>, RunningWitness<E1>)> = None;
    let mut result = Vec::new();
    let mut failure = None;
    for (step, x) in xs.iter().enumerate() {
      let k = step % 2;
      let t = Instant::now();
      let (_, a) = wiring_pair(tpl, k, reps, Some(*x)).map_err(|e| e.to_string())?;
      let a = a.ok_or("no assignment")?;
      let inc = IncomingInstance::new(&pp, k, &a.w, a.io.clone()).map_err(|e| e.to_string())?;
      witness_ms += ms(t);
      let (ru, rw): (Vec<_>, Vec<_>) = acc.iter().cloned().unzip();

      let t = Instant::now();
      let po = NIFS::<E1, V>::prove(&pp, &ru, &rw, std::slice::from_ref(&inc), &[a.w])
        .map_err(|e| format!("step {step}: prove: {e}"))?;
      per.0.push(ms(t));
      let pb = bytes(&po.proof)?;
      per.4.push(pb.len());
      result.extend_from_slice(&pb);

      let t = Instant::now();
      let ver = NIFS::<E1, V>::verify(&pp, &ru, std::slice::from_ref(&inc), &po.proof);
      per.1.push(ms(t));
      let t = Instant::now();
      let dec = decide(&pp, &po.instance, &po.witness);
      per.2.push(ms(t));
      let t = Instant::now();
      let ora = oracle(&pp, &fam, &po.instance, &po.witness);
      per.3.push(ms(t));
      per.5.push(bytes(&po.instance)?.len());
      let step_ok = match &ver {
        Ok((u, ch)) => *u == po.instance && *ch == po.challenges,
        Err(_) => false,
      } && dec.is_ok()
        && ora.is_ok();
      if !step_ok && failure.is_none() {
        failure = Some(format!(
          "step {step}: verifier {:?}, decider {dec:?}, oracle {ora:?}",
          ver.as_ref().map(|_| ())
        ));
      }
      ok &= step_ok;
      acc = Some((po.instance, po.witness));
    }
    let (u, w) = acc.unwrap();
    out.f("witness_ms", witness_ms);
    out.f("verification_ok", ok);
    out.d(
      "per_step",
      json!({
        "prove_ms": per.0, "verify_ms": per.1, "decide_ms": per.2, "oracle_ms": per.3,
        "nifs_proof_bytes": per.4, "instance_bytes": per.5,
      }),
    );
    out.d(
      "summary",
      json!({
        "prove_ms": stats(&per.0), "verify_ms": stats(&per.1), "decide_ms": stats(&per.2),
        "oracle_ms": stats(&per.3),
        "nifs_proof_bytes_first": per.4[0], "nifs_proof_bytes_last": per.4[steps - 1],
        "running_witness_bytes": bytes(&w)?.len(),
      }),
    );
    out.d(
      "timing_note",
      "in-process Instant timers per call; development machine, no performance claim",
    );
    result.extend_from_slice(&bytes(&u)?);
    out.f("result_digest", sha256_hex(&result));
    match failure {
      None => Ok(()),
      Some(e) => Err(e),
    }
  }
}

fn scenario_ivc(out: &mut Output, args: &Args) -> Result<(), String> {
  use nova_snark::kilonova::{
    hfs::{Direct, Span},
    ivc::PrimaryTemplate,
  };
  let tpl = match arg(args, "template", Some("r1cs".to_string()))?.as_str() {
    "r1cs" => PrimaryTemplate::R1cs,
    "pow5" => PrimaryTemplate::R1csPow5,
    t => return Err(format!("unknown template {t} (r1cs | pow5)")),
  };
  let k: usize = arg(args, "K", Some(2))?;
  let steps: usize = arg(args, "steps", Some(16))?;
  let every: usize = arg(args, "verify_every", Some(0))?;
  let seed: u64 = arg(args, "seed", None)?;
  if !(1..=16).contains(&k) || steps == 0 {
    return Err("need 1 <= K <= 16 and steps >= 1".into());
  }
  match arg(args, "variant", Some("direct".to_string()))?.as_str() {
    "direct" => ivc::run::<Direct>(out, tpl, k, steps, every, seed),
    "span" => ivc::run::<Span>(out, tpl, k, steps, every, seed),
    v => Err(format!("unknown variant {v}")),
  }
}

/// P5: the non-uniform recursive chain on HFS v2 + CycleFold (`kilonova::ivc`).
mod ivc {
  use super::*;
  use nova_snark::kilonova::{
    ivc::{
      breakdown::primary_breakdown, fixtures::ChainPredicates, primary_constraint_counts,
      IvcVariant, PrimaryTemplate, PublicParams, RecursiveSNARK, IVC_VERSION,
    },
    predicate_constraint_counts,
  };

  fn bytes<T: serde::Serialize>(v: &T) -> Result<Vec<u8>, String> {
    bincode::serde::encode_to_vec(v, bincode::config::legacy()).map_err(|e| e.to_string())
  }

  pub fn run<V: IvcVariant<E1>>(
    out: &mut Output,
    tpl: PrimaryTemplate,
    k: usize,
    steps: usize,
    every: usize,
    seed: u64,
  ) -> Result<(), String> {
    let preds = ChainPredicates::<F1>::new(k, tpl == PrimaryTemplate::R1csPow5).program();
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let app0 = vec![F1::from(rng.next_u64()), F1::from(rng.next_u64())];
    // every member once, then a seeded schedule
    let ids: Vec<usize> = (0..steps)
      .map(|i| {
        if i < k {
          i
        } else {
          (rng.next_u32() as usize) % k
        }
      })
      .collect();
    // P4: the schedule is a program in the initial state; φ runs it in-circuit
    let z0 = preds
      .z0(&app0, &ids)
      .ok_or("the schedule does not fit the program register")?;

    out.f("scheme", format!("kilonova-ivc-v2-{}", V::NAME));
    out.f(
      "workload",
      format!(
        "chain-predicates-k{k}-{}",
        if tpl == PrimaryTemplate::R1csPow5 {
          "pow5"
        } else {
          "r1cs"
        }
      ),
    );
    out.f("protocol_version", 2);
    out.f("transcript_version", 2);
    out.f(
      "security_profile",
      format!(
        "pallas/vesta; HFS v2 in-circuit over E1::Scalar + CycleFold over E2::Scalar (D1 = (a)); IVC v{IVC_VERSION} (family digest, in-circuit phi, verifier without schedule); pedersen; poseidon; challenge {NUM_CHALLENGE_BITS} bits; hash {NUM_HASH_BITS} bits; non-ZK; uncompressed (verify reads the final witnesses, G2)"
      ),
    );
    out.f("K", k);
    out.f("T", steps);
    out.f("mu", 1);
    out.f("nu", 1);
    out.f(
      "input_digest",
      digest_of(
        "ivc",
        &[
          ("variant", V::NAME.into()),
          ("template", format!("{tpl:?}")),
          ("K", k.to_string()),
          ("steps", steps.to_string()),
          ("seed", seed.to_string()),
          ("z0", z0.iter().map(fe_hex).collect::<String>()),
          ("ids", format!("{ids:?}")),
        ],
      ),
    );
    out.d("schedule", json!(ids));

    let t = Instant::now();
    let (pp, report) =
      PublicParams::<E1, E2, V>::setup(&preds, tpl).map_err(|e| format!("setup: {e}"))?;
    out.f("setup_ms", ms(t));
    out.f("setup_iterations", report.iterations.len());
    out.d("setup_report", serde_json::to_value(&report).unwrap());
    let hfs = pp.hfs();
    out.f("d", hfs.template().degree());
    out.f("t", hfs.t());
    out.f("q", hfs.template().q());
    out.f("m_aug", hfs.m());
    out.f("n_aug", hfs.n());
    let raw_max = report
      .primary_raw
      .iter()
      .map(|r| r.r1cs_rows + r.pow_rows)
      .max()
      .unwrap_or(0);
    out.f("padding", hfs.m() - raw_max);
    out.f(
      "N_total",
      hfs.shapes().iter().map(|s| s.nnz()).sum::<usize>(),
    );
    let mut app = Vec::new();
    let mut breakdown = Vec::new();
    for id in 0..k {
      let a = predicate_constraint_counts(&preds, id).map_err(|e| e.to_string())?;
      app.push(json!({"id": id, "constraints": a.num_constraints, "aux": a.num_aux}));
      let b = primary_breakdown(&pp, &preds, id).map_err(|e| e.to_string())?;
      let c = primary_constraint_counts(&pp, &preds, id).map_err(|e| e.to_string())?;
      if b.total != c.num_constraints || b.by_category.values().sum::<usize>() != b.total {
        return Err("breakdown does not sum to the CountingCS total".into());
      }
      breakdown.push(serde_json::to_value(&b).unwrap());
    }
    out.f(
      "m_app",
      app
        .iter()
        .map(|a| a["constraints"].as_u64().unwrap())
        .max()
        .unwrap(),
    );
    out.f(
      "w_app",
      app
        .iter()
        .map(|a| a["aux"].as_u64().unwrap())
        .max()
        .unwrap(),
    );
    out.why(
      "n_app",
      "the application has no stand-alone shape here; constraints and aux per predicate are in details.application",
    );
    out.d("application", json!(app));
    out.d("constraint_breakdown", json!(breakdown));
    out.d(
      "cyclefold",
      json!({
        "num_inputs": pp.cyclefold_num_inputs(),
        "raw_cons_vars_io": report.cyclefold_raw,
        "padded_cons_vars": report.cyclefold_padded,
      }),
    );
    out.d("pp_digest", fe_hex(&pp.digest()));
    out.d("family_digest", fe_hex(&pp.family().digest()));
    out.d("family_ids", json!(pp.family().ids()));

    let mut per_step = Vec::with_capacity(steps);
    let mut spot = Vec::new();
    let t_all = Instant::now();
    let t = Instant::now();
    let mut snark =
      RecursiveSNARK::<E1, E2, V>::new(&pp, &preds, &z0).map_err(|e| format!("step 1: {e}"))?;
    per_step.push(ms(t));
    let mut ok = true;
    for n in 2..=steps {
      let t = Instant::now();
      if snark.next_predicate(&preds) != Some(ids[n - 1]) {
        return Err(format!("step {n}: phi does not follow the program"));
      }
      snark
        .prove_step(&pp, &preds)
        .map_err(|e| format!("step {n}: {e}"))?;
      per_step.push(ms(t));
      if every > 0 && n % every == 0 && n < steps {
        let t = Instant::now();
        let r = snark.verify_schedule(&pp, n, &z0, &ids[..n]);
        spot.push(json!({"step": n, "ok": r.is_ok(), "verify_ms": ms(t)}));
        ok &= r.is_ok();
      }
    }
    out.f("recursive_ms", ms(t_all));
    let t = Instant::now();
    // the verifier takes no schedule; the recovered trace is then compared with `ids`
    let res = snark.verify(&pp, steps, &z0);
    out.f("verify_warm_ms", ms(t));
    let expected = preds.inner().run(&app0, &ids);
    let trace_ok = matches!(&res, Ok(o) if o.trace == pp.trace_of(&ids));
    let final_ok = trace_ok && matches!(&res, Ok(o) if o.zn[..2] == expected[..]);
    if let Ok(o) = &res {
      out.d("recovered_trace", fe_hex(&o.trace));
      out.d("last_id", o.last_id);
    }
    ok &= final_ok;
    out.f("verification_ok", ok);
    out.f("checkpoint_bytes", bytes(&snark)?.len());
    out.why(
      "witness_ms",
      "witness generation is part of each prove_step (circuit synthesis); see details.per_step_prove_ms",
    );
    out.why(
      "public_state_bytes",
      "no compressed public statement before P7; checkpoint_bytes is the uncompressed RecursiveSNARK",
    );
    out.d("per_step_prove_ms", json!(per_step));
    out.d("spot_verify", json!(spot));
    let mut sorted = per_step[1..].to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap());
    if !sorted.is_empty() {
      out.d("prove_step_ms_median", sorted[sorted.len() / 2]);
    }
    out.d(
      "timing_note",
      "in-process Instant timers; development machine, orientation only, no performance claim",
    );
    let mut result = Vec::new();
    for z in snark.outputs() {
      result.extend_from_slice(z.to_repr().as_ref());
    }
    out.f("result_digest", sha256_hex(&result));
    match res {
      Ok(_) if final_ok => Ok(()),
      Ok(_) => Err("verify returned a wrong z_n".into()),
      Err(e) => Err(format!("verify: {e} (layer {:?})", e.layer())),
    }
  }
}

/// P4: index-span support growth and preprocessing/memory overhead versus K.
///
/// - `source=synthetic`: K satisfiable R1CS members over one shared assignment (m rows,
///   `n = m` columns, s non-zeros per row in A and B), with an overlap pattern: `shared` (every
///   row reuses member 0's positions), `partial` (half of the rows do), `low` (fresh random
///   positions). T native HFS folds (every member first, then seeded) track the explicit folded
///   matrix step by step and cross-check explicit = weighted = protocol claims.
/// - `source=ivc`: the real recursive family (the K primary augmented circuits of the chain
///   program, Direct, R1CS); setup, then the support statistics, the family-digest time and
///   the explicit-vs-weighted evaluation at a random point with a dense λ.
mod family {
  use super::*;
  use nova_snark::kilonova::{
    family::{support_stats, weighted_eval, FoldedMatrices, PredicateFamily},
    hfs::{
      decide, CcsShape, CcsTemplate, Direct, HfsParams, IncomingInstance, RunningInstance,
      RunningWitness, Span, Variant, NIFS,
    },
    ivc::{fixtures::ChainPredicates, PredicateProgram, PrimaryTemplate, PublicParams},
    PredicateSet,
  };

  type Entries = Vec<(usize, usize, F1)>;

  /// One member satisfied by `z` (u = 1 at column `u_col`): rows `(A z)(B z) = C z`, A and B
  /// with `s` entries per row, C with `s − 1` random entries plus the u-column entry that makes
  /// the row hold. With probability `p` a row reuses the positions of `base`.
  fn member(
    z: &[F1],
    m: usize,
    u_col: usize,
    s: usize,
    base: Option<&[Vec<Vec<usize>>; 3]>,
    p: f64,
    rng: &mut ChaCha20Rng,
  ) -> ([Entries; 3], [Vec<Vec<usize>>; 3]) {
    let n = z.len();
    let mut mats: [Entries; 3] = Default::default();
    let mut cols: [Vec<Vec<usize>>; 3] = Default::default();
    for row in 0..m {
      let reuse = base.is_some() && (rng.next_u64() as f64 / u64::MAX as f64) < p;
      let mut vals = [F1::ZERO; 3];
      for j in 0..3 {
        let want = if j == 2 { s.saturating_sub(1) } else { s };
        let cs: Vec<usize> = match (reuse, base) {
          (true, Some(b)) => b[j][row].clone(),
          _ => {
            let mut v: Vec<usize> = (0..want).map(|_| (rng.next_u64() as usize) % n).collect();
            v.retain(|&c| c != u_col || j != 2);
            v
          }
        };
        for &c in &cs {
          let x = F1::random(&mut *rng);
          vals[j] += x * z[c];
          mats[j].push((row, c, x));
        }
        cols[j].push(cs);
      }
      // C's u entry: c_u · 1 = A·B − partial C
      mats[2].push((row, u_col, vals[0] * vals[1] - vals[2]));
    }
    (mats, cols)
  }

  fn shape(mats: [Entries; 3], m: usize, num_w: usize) -> Result<CcsShape<F1>, String> {
    CcsShape::new(m, num_w, 1, mats.to_vec()).map_err(|e| e.to_string())
  }

  pub fn run(out: &mut Output, args: &Args) -> Result<(), String> {
    let k: usize = arg(args, "K", Some(4))?;
    let seed: u64 = arg(args, "seed", None)?;
    match arg(args, "source", Some("synthetic".to_string()))?.as_str() {
      "synthetic" => match arg(args, "variant", Some("span".to_string()))?.as_str() {
        "direct" => synthetic::<Direct>(out, args, k, seed),
        "span" => synthetic::<Span>(out, args, k, seed),
        v => Err(format!("unknown variant {v}")),
      },
      "ivc" => ivc_family(out, k, seed),
      s => Err(format!("unknown source {s} (synthetic | ivc)")),
    }
  }

  fn stats_json(st: &nova_snark::kilonova::family::SupportStats) -> Value {
    serde_json::to_value(st).unwrap()
  }

  fn common(out: &mut Output, k: usize) {
    out.f("K", k);
    out.f("protocol_version", 2);
    out.f("transcript_version", 2);
    out.f("d", 2);
    out.f("t", 3);
    out.f("q", 2);
    out.why(
      "checkpoint_bytes",
      "family/index-span measurement: no RecursiveSNARK checkpoint; byte sizes of the base matrices, the explicit folded matrix and λ are in details.support",
    );
  }

  fn synthetic<V: Variant<E1>>(
    out: &mut Output,
    args: &Args,
    k: usize,
    seed: u64,
  ) -> Result<(), String> {
    let m: usize = arg(args, "m", Some(1024))?;
    let s: usize = arg(args, "s", Some(3))?;
    let steps: usize = arg(args, "steps", Some(2 * k.max(8)))?;
    let overlap = arg(args, "overlap", Some("low".to_string()))?;
    let p = match overlap.as_str() {
      "shared" => 1.0,
      "partial" => 0.5,
      "low" => 0.0,
      o => return Err(format!("unknown overlap {o} (shared | partial | low)")),
    };
    if k == 0 || m < 2 || s == 0 || steps == 0 {
      return Err("need K >= 1, m >= 2, s >= 1, steps >= 1".into());
    }
    common(out, k);
    out.f("scheme", format!("kilonova-family-synthetic-{}", V::NAME));
    out.f("workload", format!("w1-r1cs-m{m}-s{s}-{overlap}"));
    out.f("T", steps);
    out.f("mu", 1);
    out.f("nu", 1);
    out.f("m_app", m);
    out.f("n_app", m);
    let num_w = m - 2; // n = num_w + 1 + 1 = m
    out.f("w_app", num_w);
    let r = "native folding of a synthetic family: no augmented circuit, no recursion";
    for f in [
      "m_aug",
      "n_aug",
      "padding",
      "setup_iterations",
      "recursive_ms",
      "verify_warm_ms",
    ] {
      out.why(f, r);
    }
    out.f(
      "input_digest",
      digest_of(
        "family",
        &[
          ("source", "synthetic".into()),
          ("variant", V::NAME.into()),
          ("K", k.to_string()),
          ("m", m.to_string()),
          ("s", s.to_string()),
          ("overlap", overlap.clone()),
          ("steps", steps.to_string()),
          ("seed", seed.to_string()),
        ],
      ),
    );

    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let w: Vec<F1> = (0..num_w).map(|_| F1::random(&mut rng)).collect();
    let io = vec![F1::random(&mut rng)];
    let z = [w.as_slice(), &[F1::ONE], &io].concat();
    let t = Instant::now();
    let mut shapes = Vec::with_capacity(k);
    let (m0, base) = member(&z, m, num_w, s, None, 0.0, &mut rng);
    shapes.push(shape(m0, m, num_w)?);
    for _ in 1..k {
      let (mk, _) = member(&z, m, num_w, s, Some(&base), p, &mut rng);
      shapes.push(shape(mk, m, num_w)?);
    }
    let gen_ms = ms(t);
    let support = support_stats(&shapes);
    out.f("N_total", support.sum_nnz);

    let t = Instant::now();
    let fam = PredicateFamily::new(
      format!("w1-{overlap}"),
      (0..k).map(|i| format!("w1/m{i}")).collect(),
      1,
      b"none".to_vec(),
      CcsTemplate::r1cs(),
      shapes,
    )
    .map_err(|e| e.to_string())?;
    let digest_ms = ms(t);
    let t = Instant::now();
    let pp = HfsParams::<E1>::from_family(&fam).map_err(|e| e.to_string())?;
    out.f("setup_ms", digest_ms + ms(t));

    let ids: Vec<usize> = (0..steps)
      .map(|i| {
        if i < k {
          i
        } else {
          (rng.next_u32() as usize) % k
        }
      })
      .collect();
    let mut acc: Option<(RunningInstance<E1, V>, RunningWitness<E1>)> = None;
    let mut explicit = FoldedMatrices::<F1>::zero(3, k);
    let (mut nnz, mut fold_ms, mut ex_ms, mut wt_ms, mut prove_ms) =
      (Vec::new(), Vec::new(), Vec::new(), Vec::new(), Vec::new());
    let mut ok = true;
    for &id in &ids {
      let inc = IncomingInstance::new(&pp, id, &w, io.clone()).map_err(|e| e.to_string())?;
      let (ru, rw): (Vec<_>, Vec<_>) = acc.iter().cloned().unzip();
      let t = Instant::now();
      let po = NIFS::<E1, V>::prove(&pp, &ru, &rw, std::slice::from_ref(&inc), &[w.clone()])
        .map_err(|e| e.to_string())?;
      prove_ms.push(ms(t));
      let (u, ch) = NIFS::<E1, V>::verify(&pp, &ru, std::slice::from_ref(&inc), &po.proof)
        .map_err(|e| e.to_string())?;
      let weight = if acc.is_some() { ch.rho } else { F1::ONE };
      let t = Instant::now();
      explicit.fold(fam.shapes(), weight, id);
      fold_ms.push(ms(t));
      let t = Instant::now();
      let ex = explicit.eval(&u.r_x, &u.r_y);
      ex_ms.push(ms(t));
      let t = Instant::now();
      let wt = weighted_eval(fam.shapes(), &po.witness.lambda, &u.r_x, &u.r_y);
      wt_ms.push(ms(t));
      ok &= u == po.instance
        && ex == wt
        && ex[..] == u.v[..3]
        && explicit.lambda() == po.witness.lambda.as_slice()
        && decide(&pp, &u, &po.witness).is_ok();
      nnz.push(explicit.nnz());
      acc = Some((u, po.witness));
    }
    out.f("verification_ok", ok);
    out.f("witness_ms", 0.0);
    let dense_step = acc.as_ref().and_then(|_| {
      nnz
        .iter()
        .position(|&x| x == support.union_nnz)
        .map(|i| i + 1)
    });
    out.d("support", stats_json(&support));
    out.d(
      "per_step",
      json!({"ids": ids, "explicit_nnz": nnz, "explicit_fold_ms": fold_ms,
             "explicit_eval_ms": ex_ms, "weighted_eval_ms": wt_ms, "prove_ms": prove_ms}),
    );
    out.d(
      "summary",
      json!({"generate_ms": gen_ms, "family_digest_ms": digest_ms,
             "explicit_reaches_union_at_step": dense_step,
             "final_explicit_nnz": nnz.last(), "union_nnz": support.union_nnz,
             "final_explicit_bytes": explicit.bytes(),
             "explicit_over_member": explicit.nnz() as f64 / support.max_nnz as f64,
             "family_digest": fe_hex(&fam.digest())}),
    );
    out.d(
      "timing_note",
      "in-process Instant timers; development machine, no performance claim",
    );
    let mut sem = Vec::new();
    for e in (0..3).flat_map(|j| explicit.matrix(j).to_vec()) {
      sem.extend_from_slice(e.2.to_repr().as_ref());
    }
    out.f("result_digest", sha256_hex(&sem));
    if ok {
      Ok(())
    } else {
      Err("explicit and weighted paths disagree".into())
    }
  }

  fn ivc_family(out: &mut Output, k: usize, seed: u64) -> Result<(), String> {
    if !(1..=16).contains(&k) {
      return Err("source=ivc needs 1 <= K <= 16".into());
    }
    common(out, k);
    out.f("scheme", "kilonova-family-ivc-direct");
    out.f("workload", format!("chain-predicates-k{k}-r1cs-augmented"));
    out.f(
      "input_digest",
      digest_of(
        "family",
        &[
          ("source", "ivc".into()),
          ("K", k.to_string()),
          ("seed", seed.to_string()),
        ],
      ),
    );
    let r = "family measurement after setup: no chain is proven (chains: scenario ivc)";
    for f in [
      "T",
      "mu",
      "nu",
      "recursive_ms",
      "verify_warm_ms",
      "m_app",
      "n_app",
      "w_app",
    ] {
      out.why(f, r);
    }
    let prog = ChainPredicates::<F1>::new(k, false).program();
    let t = Instant::now();
    let (pp, report) = PublicParams::<E1, E2, Direct>::setup(&prog, PrimaryTemplate::R1cs)
      .map_err(|e| format!("setup: {e}"))?;
    out.f("setup_ms", ms(t));
    out.f("setup_iterations", report.iterations.len());
    let hfs = pp.hfs();
    out.f("m_aug", hfs.m());
    out.f("n_aug", hfs.n());
    let raw_max = report
      .primary_raw
      .iter()
      .map(|r| r.r1cs_rows + r.pow_rows)
      .max()
      .unwrap_or(0);
    out.f("padding", hfs.m() - raw_max);
    let shapes = hfs.shapes();
    let t = Instant::now();
    let support = support_stats(shapes);
    let support_ms = ms(t);
    out.f("N_total", support.sum_nnz);
    // the family digest from scratch (canonical encodings streamed through SHA3)
    let t = Instant::now();
    let fam = PredicateFamily::new(
      prog.family_label(),
      (0..k).map(|i| prog.member_id(i)).collect(),
      prog.arity(),
      prog.selector_descriptor(),
      hfs.template().clone(),
      shapes.to_vec(),
    )
    .map_err(|e| e.to_string())?;
    let digest_ms = ms(t);
    let digest_ok = fam.digest() == pp.family().digest();
    drop(fam);
    // a dense λ and a random point: explicit vs weighted evaluation
    let mut rng = ChaCha20Rng::seed_from_u64(seed);
    let lambda: Vec<F1> = (0..k).map(|_| F1::random(&mut rng)).collect();
    let r_x: Vec<F1> = (0..hfs.s()).map(|_| F1::random(&mut rng)).collect();
    let r_y: Vec<F1> = (0..hfs.s_prime()).map(|_| F1::random(&mut rng)).collect();
    let t = Instant::now();
    let explicit = FoldedMatrices::from_lambda(shapes, &lambda);
    let build_ms = ms(t);
    let t = Instant::now();
    let ex = explicit.eval(&r_x, &r_y);
    let ex_ms = ms(t);
    let t = Instant::now();
    let wt = weighted_eval(shapes, &lambda, &r_x, &r_y);
    let wt_ms = ms(t);
    let ok = digest_ok && ex == wt && explicit.nnz() == support.union_nnz;
    out.f("verification_ok", ok);
    out.d("support", stats_json(&support));
    out.d(
      "summary",
      json!({"support_stats_ms": support_ms, "family_digest_ms": digest_ms,
             "explicit_build_ms": build_ms, "explicit_eval_ms": ex_ms, "weighted_eval_ms": wt_ms,
             "explicit_nnz": explicit.nnz(), "explicit_bytes": explicit.bytes(),
             "family_digest": fe_hex(&pp.family().digest()), "digest_recomputed_equal": digest_ok,
             "per_member_raw_rows": report.primary_raw.iter().map(|r| r.r1cs_rows).collect::<Vec<_>>()}),
    );
    out.d(
      "timing_note",
      "in-process Instant timers; development machine, no performance claim",
    );
    out.f("result_digest", fe_hex(&pp.family().digest()));
    if ok {
      Ok(())
    } else {
      Err("family digest or explicit/weighted evaluation mismatch".into())
    }
  }
}

fn run(name: &str, args: &Args, out: &mut Output) -> Result<(), String> {
  let variant = || -> Result<String, String> { arg(args, "variant", Some("direct".to_string())) };
  let seed = || -> Result<u64, String> { arg(args, "seed", Some(101)) };
  match name {
    "noop" => {
      scenario_noop(out);
      Ok(())
    }
    "sleep" => scenario_sleep(out, args),
    "alloc" => scenario_alloc(out, args),
    "fail" => panic!("kn-scenario: deliberate failure (scenario 'fail')"),
    "constraints" => match variant()?.as_str() {
      "direct" => direct::constraints(out),
      "span" => span::constraints(out),
      v => Err(format!("unknown variant {v}")),
    },
    "bootstrap" | "chain" => {
      let steps = if name == "bootstrap" {
        1
      } else {
        arg(args, "steps", None)?
      };
      match variant()?.as_str() {
        "direct" => direct::chain(out, seed()?, steps),
        "span" => span::chain(out, seed()?, steps),
        v => Err(format!("unknown variant {v}")),
      }
    }
    "ccs" => scenario_ccs(out, args),
    "hfs" => scenario_hfs(out, args),
    "ivc" => scenario_ivc(out, args),
    "family" => family::run(out, args),
    other => Err(format!("unknown scenario '{other}'")),
  }
}

fn main() {
  let argv: Vec<String> = std::env::args().skip(1).collect();
  let Some(name) = argv.first().cloned() else {
    eprintln!(
      "usage: kn-scenario <noop|sleep|alloc|fail|constraints|bootstrap|chain|ccs|hfs|ivc|family> [key=value ...]"
    );
    std::process::exit(2);
  };
  let args = match parse_args(&argv[1..]) {
    Ok(a) => a,
    Err(e) => {
      eprintln!("kn-scenario: {e}");
      std::process::exit(2);
    }
  };

  let mut out = Output::new();
  out.f("protocol_version", HFS_TRANSCRIPT_VERSION);
  out.f("transcript_version", HFS_TRANSCRIPT_VERSION);
  out.f(
    "build_flags",
    format!(
      "profile={}; RUSTFLAGS={}",
      if cfg!(debug_assertions) {
        "debug"
      } else {
        "release"
      },
      option_env!("RUSTFLAGS").unwrap_or("")
    ),
  );
  out.f(
    "security_profile",
    format!(
      "pallas/vesta; pedersen; poseidon RO; challenge {NUM_CHALLENGE_BITS} bits; hash {NUM_HASH_BITS} bits; non-ZK"
    ),
  );
  out.d("threads_actual", rayon::current_num_threads());
  out.d("args", serde_json::to_value(&args).unwrap());

  let res = run(&name, &args, &mut out);
  // The result line is printed even on failure, so partial timings are kept.
  let line = json!({
    "ok": res.is_ok(),
    "error": res.as_ref().err(),
    "fields": out.fields,
    "null_reasons": out.null_reasons,
    "details": out.details,
  });
  println!("{RESULT_PREFIX}{line}");
  if let Err(e) = res {
    eprintln!("kn-scenario {name}: {e}");
    std::process::exit(1);
  }
}
