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

/// Version of the frozen HFS transcript layout used by the v1 path (`nifs.rs`, `span/`, the
/// gadgets and `RecursiveSNARK`). The native-field HFS of P3 uses [`v2`].
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

/// HFS transcript **v2** (P3, native-field HFS in `kilonova::hfs`). The absorption order is
/// frozen in `docs/protocol-spec.md` §8.
///
/// D1 assumption (option (a) of `docs/P3.0-decision.md`, not yet confirmed by the maintainer):
/// the HFS for instances committed on `E` is verified natively in a circuit over `E::Scalar`.
/// The sponge is therefore Poseidon over `E::Scalar` (`E::RO2`, circuit twin `E::RO2Circuit`).
/// Commitments on `E` have coordinates in `E::Base`, which is non-native there, so each
/// coordinate is absorbed as `BN_N_LIMBS` limbs of `BN_LIMB_WIDTH` bits, least significant limb
/// first, followed by the infinity flag (the encoding of `Commitment::absorb_in_ro2`).
pub mod v2 {
  use crate::{
    constants::{BN_LIMB_WIDTH, BN_N_LIMBS},
    gadgets::utils::to_bignat_repr,
    traits::{commitment::CommitmentTrait, Engine, ROTrait},
    Commitment,
  };
  use ff::Field;

  /// Version of the v2 transcript layout.
  pub const HFS_TRANSCRIPT_VERSION: u64 = 2;

  /// Tag absorbed first by the Direct (committed-index) transcript: "KNHFS" ‖ v2 ‖ 1.
  pub const TAG_INPUT_DIRECT: u64 = 0x4b4e_4846_5302_0001;
  /// Tag absorbed first by the Span (public-λ) transcript.
  pub const TAG_INPUT_SPAN: u64 = 0x4b4e_4846_5302_0002;
  /// Tag absorbed before the X-phase claims (σ, τ).
  pub const TAG_X_CLAIMS: u64 = 0x4b4e_4846_5302_0003;
  /// Tag absorbed before the Y-phase claims (ε, θ).
  pub const TAG_Y_CLAIMS: u64 = 0x4b4e_4846_5302_0004;

  /// Number of sponge elements one commitment contributes.
  pub const COMMITMENT_ABSORB_LEN: usize = 2 * BN_N_LIMBS + 1;

  /// Absorbs a domain-separation tag.
  pub fn absorb_tag<E: Engine>(ro: &mut E::RO2, tag: u64) {
    ro.absorb(E::Scalar::from(tag));
  }

  /// Absorbs a commitment on `E`: `x` limbs, `y` limbs (4 × 64 bits each, least significant
  /// first), then `is_infinity ∈ {0, 1}`.
  pub fn absorb_commitment<E: Engine>(ro: &mut E::RO2, c: &Commitment<E>) {
    debug_assert_eq!(BN_LIMB_WIDTH * BN_N_LIMBS, 256);
    let (x, y, is_infinity) = c.to_coordinates();
    for limb in to_bignat_repr::<E::Base, E::Scalar>(&x)
      .into_iter()
      .chain(to_bignat_repr::<E::Base, E::Scalar>(&y))
    {
      ro.absorb(limb);
    }
    ro.absorb(if is_infinity {
      E::Scalar::ONE
    } else {
      E::Scalar::ZERO
    });
  }
}
