-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/CountAtFrame.lean: the compiled verifier's own count of typed queries (`tVC`,
Johnson/TypedOracleCompiler/RecCompile/Cms.lean) at the wiring of the input whose rounds' data and two decisions are
letters (`wireOfFull`, `wireOfSmall`, Johnson/Flat/WiresAtSizes.lean), as a plain function of the
data; and a closed error `epsFrame s v`, free of the wiring, that under premises on numbers lies
above `soundnessBoundOverTypedOracles W εs (t + (8 + n)) 0 + epsCode (t + (8 + n))` and at s ≤ 55, v ≤ 2^63 is at most one
quarter up to 2^64 and 2^64. (“the frame”: Johnson/Flat/TwoSizesAt.lean)

Why. The bounds on `soundnessBoundOverTypedOracles` that are general in the wiring (Johnson/TypedOracleCompiler/RecCompile/ClosedAns.lean)
keep "tVC W ≤ v" as a premise, and no bound on `tVC` at a named wiring of this form was given.
Johnson/Top/Pub/CountsTop.lean has the three arms' counts at the makers' wiring; its `cntWhole` and
`length_sh` are general in the data and are called here.

Three definitions, eleven theorems, one check by rfl (Small for Full at the small size).
  `tVC_add_four`: at every wiring W: tVC W + 4 = tVT W + tVL W + tVB W, the three arms' counts.
  `tVT_wireOfFull`, `tVB_wireOfFull`: `cntWhole` of the key file's | the proof file's data at the
    depth of its request tree. `tVL_wireOfFull`: 13545 (small: 7975).
  `cntFrameFull DK DP depthReq depthReqT`; `tVC_wireOfFull`: tVC at that wiring is that number. No
    premise: K, the salt, the decisions and the records are not read.
  `epsFrame s v t n`: levelAt s (5 (t + (8 + n) + v + 1) + 1) + epsCode (t + (8 + n)). It is
    `closedFormSoundnessErrorBound s v (t + (8 + n))` (Johnson/Top/InnerCompiledVerifierNumbers.lean), by unfolding.
  `bound_of_numbers`: under a + s = 128, εs ≤ c · 2^-a, c ≤ 1 + 1/4 and tVC W ≤ v, at ALL t, n:
    soundnessBoundOverTypedOracles W εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ epsFrame s v t n. One call of
    `epsA_le_levelAt`.
  `ceil_of_numbers`: at s ≤ 55 and v ≤ 2^63, for t ≤ 2^64 and n ≤ 2^64: epsFrame s v t n ≤ 1/4.

Limits. ARITHMETIC ON DEFINITIONS: no probability, nothing on soundness; that `soundnessBoundOverTypedOracles` bounds anything
is not said here. NO COUNT IS EVALUATED: DK and DP are letters, and that any data have a count of at
most 2^63 is not shown. The counts are bounds as `tVQB` counts (every opening at the greatest
depth), in typed queries: not calls of the hash function, and not what a run asks. WHERE 5 (t + (8 +
n) + v + 1) + 1 IS ABOVE 2^(126 - s), `epsFrame` IS ⊤ (`levelAt`, Johnson/Thin/K/Level/LevelAt.lean)
AND `bound_of_numbers` SAYS NOTHING: at s = 55 from t + n + v near 2^68.7 on. s ≤ 55 is a ≥ 73:
every round's error at most (1 + 1/4) · 2^-73. THE SAME εs STANDS IN keySound AND proofSound
(Johnson/Top/InnerCompiledVerifier.lean): a smaller εs makes these bounds easier and those two harder; it also
stands in entrySound and seedLaw, which Johnson/Flat/TwoSizesAt.lean pays at every εs ≥ 2^-128: so
the window is 2^-128 ≤ εs ≤ (1 + 1/4) · 2^-73; nothing here says that they can be met at such an εs.
At the edge (t = n = 2^64, v = 2^63; by arithmetic outside Lean) the written error is at most one
quarter from a = 70 on, and `epsFrame` from a = 72 on; `ceil_of_numbers` asks a ≥ 73: three bits are
given away, one each by the step function, by halving the quarter between the two terms, and by this
proof's 2^69 where 2^68 would do. "One quarter up to 2^64 queries" is a bar on an error, no security
level. The 8 stands for a number of public readings that a caller adds to the parser's queries: here
it is a numeral. GENERAL IN THE FRAME'S LETTERS: NO VALUE OF THIS FRAME HAS RUN ON A REAL PROOF.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.WiresAtSizes
import Johnson.Top.Pub.CountsTop
import Johnson.TypedOracleCompiler.RecCompile.ClosedAns
import Johnson.Top.FrontGeneral
import Johnson.Top.InnerCompiledVerifierNumbers
import OnBytes.TypedOracleCompiler.Slice.EntryFullNum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice OnBytes.RunA OnBytes.Maker _root_.Run
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.K.Arm (cntWhole length_sh)
open TypedOracleCompiler.Slice (half_pow_eq)
open _root_.TopC (levelAt levelAt_le)

/-- At every wiring the compiled verifier's count and the sum of the three arms' counts differ by
four. -/
theorem tVC_add_four {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) :
    tVC W + 4 = tVT W + tVL W + tVB W := by
  unfold tVC tVT tVL tVB
  omega

/-- The count at the full size, as a function of the two whole files' data and the two depths. -/
def cntFrameFull (DK DP : WholeD) (depthReq depthReqT : ℕ) : ℕ :=
  cntWhole (DK.at frS.P.T.a) depthReqT + 13541 + cntWhole (DP.at frS.P.T.a) depthReq

/-- The count at the small size. -/
def cntFrameSmall (DK DP : WholeD) (depthReq depthReqT : ℕ) : ℕ :=
  cntWhole (DK.at srS.P.T.a) depthReqT + 7971 + cntWhole (DP.at srS.P.T.a) depthReq

/-! ## The full size -/

section
variable {X : Type} (A : (frS.toDecR frZ 402653181).Claims X)
  (R : (frS.toDecR frZ 402653181).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecFull → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecFull → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecFull) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsWithFixedLinkAtFullSize A R DK DP runK runP rK rP depthReq early salt).Provers) (K depthReqT : ℕ)

/-- The key file's arm's count at the frame's wiring, at every data and decision. -/
theorem tVT_wireOfFull :
    tVT (wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT) =
      cntWhole (DK.at frS.P.T.a) depthReqT := by
  show 2 + (((chainsOf (ckP .two) (DK.at frS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty).sh.length + 1) + (nOpenW (DK.at frS.P.T.a) *
      (maxDepthW (DK.at frS.P.T.a) + 1) + (depthReqT + 1))) = _
  rw [length_sh]
  rfl

/-- The entry file's arm's count there is a number. -/
theorem tVL_wireOfFull :
    tVL (wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT) = 13545 := by
  rw [wireOfFull_eq_sib]
  haveI : Nonempty (Fin 1 → (Fin 29 → GE) × OnBytes.Slice.NZ) :=
    ⟨fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)⟩
  exact (tVL_wSib (restOfFull A R DK DP runK runP rK rP depthReq early salt P) K (chalP .two K) _ _
    depthReq depthReqT 0 _ sibF_len sibF_nOpen sibF_stored sibF_max).trans (by norm_num)

/-- The proof file's arm's count there, at every data and decision. -/
theorem tVB_wireOfFull :
    tVB (wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT) =
      cntWhole (DP.at frS.P.T.a) depthReq := by
  show 2 + (((chainsOf (ckP .two) (DP.at frS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty).sh.length + 1) + (nOpenW (DP.at frS.P.T.a) *
      (maxDepthW (DP.at frS.P.T.a) + 1) + (depthReq + 1))) = _
  rw [length_sh]
  rfl

/-- **The compiled verifier's own count of typed queries at the frame's wiring is a plain function
of the two whole files' data and the two depths.** No premise. -/
theorem tVC_wireOfFull :
    tVC (wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT) =
      cntFrameFull DK DP depthReq depthReqT := by
  have h := tVC_add_four (wireOfFull A R DK DP runK runP rK rP depthReq early salt P K depthReqT)
  rw [tVT_wireOfFull, tVL_wireOfFull, tVB_wireOfFull] at h
  unfold cntFrameFull
  omega

end

/-! ## The small size -/

section
variable {X : Type} (A : (srS.toDecR srZ 524285).Claims X)
  (R : (srS.toDecR srZ 524285).RelationsAndEncoding A) (DK DP : WholeD)
  (runK : RecSmall → PQ.View → PQ.View → PQ.View → Bool)
  (runP : X × RecSmall → PQ.View → PQ.View → PQ.View → Bool) (rK rP : RecSmall) (depthReq : ℕ)
  (early : X → X) (salt : ℕ)
  (P : (threeProtocolsWithFixedLinkAtSmallSize A R DK DP runK runP rK rP depthReq early salt).Provers) (K depthReqT : ℕ)

/-- The key file's arm's count at the frame's wiring, at every data and decision. -/
theorem tVT_wireOfSmall :
    tVT (wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT) =
      cntWhole (DK.at srS.P.T.a) depthReqT := by
  show 2 + (((chainsOf (ckP .two) (DK.at srS.P.T.a) (front₀ rK) (join₀ rK)
    ByteArray.empty).sh.length + 1) + (nOpenW (DK.at srS.P.T.a) *
      (maxDepthW (DK.at srS.P.T.a) + 1) + (depthReqT + 1))) = _
  rw [length_sh]
  rfl

/-- The entry file's arm's count there is a number. -/
theorem tVL_wireOfSmall :
    tVL (wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT) = 7975 := by
  rw [wireOfSmall_eq_sib]
  haveI : Nonempty (Fin 1 → (Fin 19 → GE) × OnBytes.Slice.NZ) :=
    ⟨fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)⟩
  exact (tVL_wSib (restOfSmall A R DK DP runK runP rK rP depthReq early salt P) K (chalP .two K) _ _
    depthReq depthReqT 0 _ sibS_len sibS_nOpen sibS_stored sibS_max).trans (by norm_num)

/-- The proof file's arm's count there, at every data and decision. -/
theorem tVB_wireOfSmall :
    tVB (wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT) =
      cntWhole (DP.at srS.P.T.a) depthReq := by
  show 2 + (((chainsOf (ckP .two) (DP.at srS.P.T.a) (front₀ rP) (join₀ rP)
    ByteArray.empty).sh.length + 1) + (nOpenW (DP.at srS.P.T.a) *
      (maxDepthW (DP.at srS.P.T.a) + 1) + (depthReq + 1))) = _
  rw [length_sh]
  rfl

/-- **The compiled verifier's own count of typed queries at the frame's wiring is a plain function
of the two whole files' data and the two depths.** No premise. -/
theorem tVC_wireOfSmall :
    tVC (wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT) =
      cntFrameSmall DK DP depthReq depthReqT := by
  have h := tVC_add_four (wireOfSmall A R DK DP runK runP rK rP depthReq early salt P K depthReqT)
  rw [tVT_wireOfSmall, tVL_wireOfSmall, tVB_wireOfSmall] at h
  unfold cntFrameSmall
  omega

end

/-! ## The error -/

/-- A closed error in which no wiring stands: s: 128 less the bits of a round's error; v: a bound on
the compiled verifier's own count; t, n: two numbers of queries. -/
def epsFrame (s v t n : ℕ) : ℝ≥0∞ :=
  levelAt s ((t + (8 + n) + v + 1) * 5 + 1) + epsCode (t + (8 + n))

/-- It is the closed bound `closedFormSoundnessErrorBound`, at t + (8 + n) queries. -/
example (s v t n : ℕ) : epsFrame s v t n = closedFormSoundnessErrorBound s v (t + (8 + n)) := rfl

/-- **It lies above the written error, at all t and n**; beyond `levelAt`'s range it is ⊤. -/
theorem bound_of_numbers {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
    {aL : RoundSplits L.link.shape} (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (εs c : ℝ≥0∞) (a s v : ℕ)
    (has : a + s = 128) (he : εs ≤ c * ((2 : ℝ≥0∞) ^ a)⁻¹) (hc : c ≤ 1 + (4 : ℝ≥0∞)⁻¹)
    (hV : tVC W ≤ v) (t n : ℕ) :
    soundnessBoundOverTypedOracles W εs (t + (8 + n)) 0 + epsCode (t + (8 + n)) ≤ epsFrame s v t n :=
  add_le_add (epsA_le_levelAt W εs c a s v (t + (8 + n)) 0 has he hc hV) le_rfl

/-- **It is at most one quarter up to 2^64 and 2^64**, at s ≤ 55 and v ≤ 2^63. -/
theorem ceil_of_numbers (s v : ℕ) (hs : s ≤ 55) (hv : v ≤ 2 ^ 63) (t n : ℕ) (ht : t ≤ 2 ^ 64)
    (hn : n ≤ 2 ^ 64) : epsFrame s v t n ≤ (4 : ℝ≥0∞)⁻¹ := by
  have e63 : (2 : ℕ) ^ 63 = 9223372036854775808 := by norm_num
  have e64 : (2 : ℕ) ^ 64 = 18446744073709551616 := by norm_num
  have e66 : (2 : ℕ) ^ 66 = 73786976294838206464 := by norm_num
  have e69 : (2 : ℕ) ^ 69 = 590295810358705651712 := by norm_num
  have hN : (t + (8 + n) + v + 1) * 5 + 1 ≤ 2 ^ 69 := by omega
  have h1 : levelAt s ((t + (8 + n) + v + 1) * 5 + 1) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 3 := by
    refine le_trans (levelAt_le s _ 69 hN (by omega)) ?_
    rw [← ENNReal.inv_pow]
    exact ENNReal.inv_le_inv.2 (pow_le_pow_right₀ (by norm_num) (by omega))
  have h2 : epsCode (t + (8 + n)) ≤ ((2 : ℝ≥0∞)⁻¹) ^ 3 := by
    have hX : (t + (8 + n) + 2) ^ 2 ≤ 2 ^ (256 - 3) :=
      le_trans (Nat.pow_le_pow_left (show t + (8 + n) + 2 ≤ 2 ^ 66 by omega) 2) (by norm_num)
    unfold epsCode
    rw [half_pow_eq 3 256 (by norm_num)]
    refine ENNReal.div_le_div_right ?_ _
    exact_mod_cast hX
  have h4 : ((2 : ℝ≥0∞)⁻¹) ^ 3 + ((2 : ℝ≥0∞)⁻¹) ^ 3 = (4 : ℝ≥0∞)⁻¹ := by
    have e4 : (4 : ℝ≥0∞)⁻¹ = ((2 : ℝ≥0∞)⁻¹) ^ 2 := by
      rw [← ENNReal.inv_pow]
      norm_num
    rw [e4, half_pow_eq 3 256 (by norm_num), half_pow_eq 2 256 (by norm_num),
      ENNReal.div_add_div_same]
    congr 1
    norm_num
  exact h4 ▸ add_le_add h1 h2

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.tVC_add_four
#print axioms VerifiableInference.OnPublicFiles.tVC_wireOfFull
#print axioms VerifiableInference.OnPublicFiles.tVC_wireOfSmall
#print axioms VerifiableInference.OnPublicFiles.bound_of_numbers
#print axioms VerifiableInference.OnPublicFiles.ceil_of_numbers
