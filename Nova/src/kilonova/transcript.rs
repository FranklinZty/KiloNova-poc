//! Domain-separation tags and helpers shared by the native HFS verifier and its gadget.
//!
//! The order of absorptions is frozen in `docs/protocol-spec.md` §3 (HFS transcript v1).
//! Every change here must be mirrored byte-for-byte in `nifs.rs`, `span/nifs.rs`,
//! `circuit/r1cs.rs` and `span/circuit/r1cs.rs`; `tests::test_transcript_native_matches_gadget`
//! in `nifs.rs` / `span/nifs.rs` guards this.
use crate::{
  frontend::{num::AllocatedNum, ConstraintSystem, SynthesisError},
  traits::{Engine, ROCircuitTrait, ROTrait},
};

/// Version of the frozen HFS transcript layout.
pub const HFS_TRANSCRIPT_VERSION: u64 = 1;

/// Tag absorbed first by the direct (committed-index) HFS transcript. ASCII "KNHFS" || v1 || 1.
pub(crate) const HFS_TAG_INPUT: u64 = 0x4b4e_4846_5301_0001;
/// Tag absorbed first by the span (public-lambda) HFS transcript.
pub(crate) const HFS_TAG_INPUT_SPAN: u64 = 0x4b4e_4846_5301_0002;
/// Tag absorbed before the X-phase helper claims (sigma, tau).
pub(crate) const HFS_TAG_X_CLAIMS: u64 = 0x4b4e_4846_5301_0003;
/// Tag absorbed before the Y-phase helper claims (epsilon, theta).
pub(crate) const HFS_TAG_Y_CLAIMS: u64 = 0x4b4e_4846_5301_0004;

/// Absorb a domain-separation tag into a native random oracle.
pub(crate) fn absorb_tag<E: Engine>(ro: &mut E::RO, tag: u64) {
  ro.absorb(E::Base::from(tag));
}

/// Absorb a domain-separation tag into an in-circuit random oracle. The tag is allocated
/// and constrained to the constant, so the shape fixes its value.
pub(crate) fn absorb_domain_tag<E: Engine, CS: ConstraintSystem<E::Base>>(
  mut cs: CS,
  ro: &mut E::ROCircuit,
  tag: u64,
) -> Result<(), SynthesisError> {
  let value = E::Base::from(tag);
  let t = AllocatedNum::alloc(cs.namespace(|| "tag"), || Ok(value))?;
  cs.enforce(
    || "tag is constant",
    |lc| lc + t.get_variable() - (value, CS::one()),
    |lc| lc + CS::one(),
    |lc| lc,
  );
  ro.absorb(&t);
  Ok(())
}
