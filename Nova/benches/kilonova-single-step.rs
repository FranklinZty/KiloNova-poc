#![allow(non_snake_case)]

use core::time::Duration;
use criterion::*;
use nova_snark::{
  kilonova::test_utils::{
    build_direct_secondary_single_step_snark_with_predicates,
    build_span_secondary_single_step_snark_with_predicates,
  },
  provider::{ipa_pc::EvaluationEngine, VestaEngine},
  spartan::snark::RelaxedR1CSSNARK,
  traits::snark::RelaxedR1CSSNARKTrait,
};

type BenchEngine = VestaEngine;
type BenchSNARK = RelaxedR1CSSNARK<BenchEngine, EvaluationEngine<BenchEngine>>;

cfg_if::cfg_if! {
  if #[cfg(feature = "flamegraph")] {
    criterion_group! {
      name = kilonova_single_step;
      config = Criterion::default()
        .warm_up_time(Duration::from_millis(3000))
        .sample_size(10)
        .with_profiler(pprof2::criterion::PProfProfiler::new(
          100,
          pprof2::criterion::Output::Flamegraph(None),
        ));
      targets = bench_kilonova_single_step
    }
  } else {
    criterion_group! {
      name = kilonova_single_step;
      config = Criterion::default()
        .warm_up_time(Duration::from_millis(3000))
        .sample_size(10);
      targets = bench_kilonova_single_step
    }
  }
}

criterion_main!(kilonova_single_step);

fn bench_kilonova_single_step(c: &mut Criterion) {
  for &num_predicates in &[2usize, 4, 8, 16] {
    let direct = build_direct_secondary_single_step_snark_with_predicates(num_predicates);
    let span = build_span_secondary_single_step_snark_with_predicates(num_predicates);

    let direct_folded = direct.folded_index_commitments();
    let span_folded = span.reconstruct_folded_index_commitments();
    assert_eq!(span_folded, span.expected_folded_index_commitments());

    eprintln!(
      "predicate_count={} direct constraints={} aux={} inputs={}",
      num_predicates,
      direct.num_constraints(),
      direct.num_aux(),
      direct.num_inputs()
    );
    eprintln!(
      "predicate_count={} span constraints={} aux={} inputs={}",
      num_predicates,
      span.num_constraints(),
      span.num_aux(),
      span.num_inputs()
    );
    eprintln!(
      "predicate_count={} direct folded index commitments: {:?}",
      num_predicates, direct_folded
    );
    eprintln!(
      "predicate_count={} span reconstructed folded index commitments: {:?}",
      num_predicates, span_folded
    );

    let (direct_pk, direct_vk) = BenchSNARK::setup(direct.ck(), direct.shape()).unwrap();
    let direct_proof = BenchSNARK::prove(
      direct.ck(),
      &direct_pk,
      direct.shape(),
      direct.relaxed_instance(),
      direct.relaxed_witness(),
    )
    .unwrap();
    direct_proof
      .verify(&direct_vk, direct.relaxed_instance())
      .unwrap();

    let (span_pk, span_vk) = BenchSNARK::setup(span.ck(), span.shape()).unwrap();
    let span_proof = BenchSNARK::prove(
      span.ck(),
      &span_pk,
      span.shape(),
      span.relaxed_instance(),
      span.relaxed_witness(),
    )
    .unwrap();
    span_proof
      .verify(&span_vk, span.relaxed_instance())
      .unwrap();

    let mut direct_group = c.benchmark_group(format!(
      "predicates-{num_predicates}/direct-secondary-single-step"
    ));
    direct_group.bench_function("prove", |b| {
      b.iter(|| {
        BenchSNARK::prove(
          black_box(direct.ck()),
          black_box(&direct_pk),
          black_box(direct.shape()),
          black_box(direct.relaxed_instance()),
          black_box(direct.relaxed_witness()),
        )
        .unwrap()
      })
    });
    direct_group.bench_function("verify_snark_only", |b| {
      b.iter(|| {
        black_box(&direct_proof)
          .verify(black_box(&direct_vk), black_box(direct.relaxed_instance()))
          .unwrap();
      })
    });
    direct_group.bench_function("verify_combined", |b| {
      b.iter(|| {
        black_box(&direct_proof)
          .verify(black_box(&direct_vk), black_box(direct.relaxed_instance()))
          .unwrap();
      })
    });
    direct_group.finish();

    let mut span_group = c.benchmark_group(format!(
      "predicates-{num_predicates}/span-secondary-single-step"
    ));
    span_group.bench_function("prove", |b| {
      b.iter(|| {
        BenchSNARK::prove(
          black_box(span.ck()),
          black_box(&span_pk),
          black_box(span.shape()),
          black_box(span.relaxed_instance()),
          black_box(span.relaxed_witness()),
        )
        .unwrap()
      })
    });
    span_group.bench_function("verify_snark_only", |b| {
      b.iter(|| {
        black_box(&span_proof)
          .verify(black_box(&span_vk), black_box(span.relaxed_instance()))
          .unwrap();
      })
    });
    span_group.bench_function("verify_local_reconstruct_only", |b| {
      b.iter(|| black_box(span.reconstruct_folded_index_commitments()))
    });
    span_group.bench_function("verify_combined", |b| {
      b.iter(|| {
        let reconstructed = black_box(span.reconstruct_folded_index_commitments());
        black_box(reconstructed);
        black_box(&span_proof)
          .verify(black_box(&span_vk), black_box(span.relaxed_instance()))
          .unwrap();
      })
    });
    span_group.finish();
  }
}
