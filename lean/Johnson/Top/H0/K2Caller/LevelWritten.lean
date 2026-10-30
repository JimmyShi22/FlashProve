-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/LevelWritten.lean: the level at a place of the code switch over the WRITTEN
rounds: with the bits of work among a round's challenges, each of the block's two counts, as a share
of all written challenges of its round, is at most 2⁻¹ ^ target.

Level.lean has Err.BelowG: a count is at most c * 2 ^ b * (the number of the bare round's
challenges). Iop/Grind.lean has the list of rounds with bits of work (Shape.grind: a round's
challenge is the old one with b bits) and the same counts over it (Err.grind); Iop/GrindProofs.lean
has Err.below_grind_iff: Err.Below of the one is Err.BelowG of the other. Here the two are laid
together.
  inv_two_pow: ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ = 2⁻¹ ^ n
  Letters.written: Err.Below (Err.grind (bitsAt X) (the caller's errors)) (2⁻¹ ^ target), for all
      letters and every type of nonces
  written_small, written_full: at each of the 5 and the 25 written records; there the target is 128
      and the bits are 0 and 20 (Level.lean: small_works, full_works)
Limits: those of Level.lean. A statement on numbers: that only challenges whose bits of work are all
0 help a prover is InteractiveOracleProof.Sound.grind's (Iop/GrindProofs.lean), which is not called here. A bound on
each round, not on a sum over rounds. Nothing on soundness of the protocol. On hiding nothing.

-/
import Johnson.Top.H0.K2Caller.Level
import Iop.GrindProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open OnBytes OnBytes.Slice OnBytes.Params OnBytes.Plan Cb Iop IOR
open scoped ENNReal

theorem inv_two_pow (n : ℕ) : ENNReal.ofReal ((2 : ℝ) ^ n)⁻¹ = (2 : ℝ≥0∞)⁻¹ ^ n := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num),
      ENNReal.ofReal_ofNat, ENNReal.inv_pow]

/-- **The level over the written rounds**, for all letters. W: the type of the nonces. -/
theorem Letters.written (W : Type) [Inhabited W] {r : SwRow} (h : r.ok = true) (hL : r.levelOK =
    true) (X : Letters r (r.ok_says h)) :
    Err.Below (Err.grind (W := W) (bitsAt X) (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^
        r.set.target) := by
  rw [← inv_two_pow]
  exact (Err.below_grind_iff (W := W) (bitsAt X) _ _).2 (Letters.level h hL X)

/-- **At the 5 switches of the small example.** -/
theorem written_small (W : Type) [Inhabited W] (r : SwRow) (hr : r ∈ tableSmallLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableSmallLit_ok r hr))) :
    Err.Below (Err.grind (W := W) (bitsAt X) (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^
        r.set.target) :=
  Letters.written W (List.all_eq_true.1 tableSmallLit_ok r hr) (List.all_eq_true.1 small_level_ok r
      hr) X

/-- **At the 25 switches of the full example.** -/
theorem written_full (W : Type) [Inhabited W] (r : SwRow) (hr : r ∈ tableFullLit)
    (X : Letters r (r.ok_says (List.all_eq_true.1 tableFullLit_ok r hr))) :
    Err.Below (Err.grind (W := W) (bitsAt X) (Cb.Pv.SendLocRide.eps X.caller)) ((2 : ℝ≥0∞)⁻¹ ^
        r.set.target) :=
  Letters.written W (List.all_eq_true.1 tableFullLit_ok r hr) (List.all_eq_true.1 full_level_ok r
      hr) X

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.inv_two_pow
#print axioms VerifiableInference.Desc.First.K2Caller.Letters.written
#print axioms VerifiableInference.Desc.First.K2Caller.written_small
#print axioms VerifiableInference.Desc.First.K2Caller.written_full
