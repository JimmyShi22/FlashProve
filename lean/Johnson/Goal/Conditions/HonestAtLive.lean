-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/HonestAtLive.lean: **HonestWithin (Ladder.lean) AT theHome
(Johnson/Goal/Conditions/WiderHome.lean), IN SCOPE, WHERE protocolDataWellFormed SAYS YES.** The sum is a numeral;
OF NUMBERS THE THREE PATHS' LENGTHS ALONE ARE PREMISES; that the prover's program is the one named
below is a premise too. The honest prover's program is proveForm (Johnson/Prover/Home/Defs.lean)
over the told record of the goals' description, carried by the first-block exit (carryF,
Johnson/Prover/Home/CountF.lean) at the test firstBlockTestAtDescriptionData and at caps of 2^(work + 6) tries. A theorem
about the goals' own definition at a member of theWider. This file states no goal.

Main names.
  count₀_live     in scope, where protocolDataWellFormed says yes, the written committer's count is 8589982777.
  honest_number   the sum: 0 + (2 + 8589982777) + (8 + 7068035999651) + 7 + 1 =
    7076625982446 ≤ honestBudget = 2^48.
  honestWithin_home_live   THE STATEMENT.

What it asks. The public files are read and in scope · protocolDataWellFormed says yes at them · AT THESE FILES the
letter pf of theHome IS proveForm at the letters named above (an equation; strategies, printer, the
committer's coins and the draws stay letters) · every draw's three paths have the lengths 0, 0, 6.

What pays what. The data are the written data: key_built_written, proof_built_written
(Johnson/Goal/Description/KeyWritten.lean, ProofWritten.lean). The number of blocks: kf_written
(Johnson/Goal/Skeleton/LiveOfReturns.lean). The prover's numeral: allF_written
(Johnson/Goal/Conditions/HonestNumber.lean). The premises of the count: firstIs_layoutsByPublicReading, passFits_layoutsByPublicReading
(Johnson/Goal/Conditions/HonestAtDescriptionDataAtFiles.lean). The frame: honestWithin_theHome
(Johnson/Goal/Conditions/HonestAtWider.lean).

Limits. That protocolDataWellFormed accepts is proved in Lean, in the side library (outside the main library and
with that library's own limits), at the written copy of the full-size example's files under every
acceptance policy in scope (theLive_zAt, AtFullSide/Top/LiveAtPolicies.lean; owner:
Johnson/Goal/Conditions/HomeLast.lean, limit 4); that theorem is not called here. The scope is wider
than these files; elsewhere in it that protocolDataWellFormed accepts stays a premise. THE PATHS' LENGTHS ARE
PREMISES HERE: they are the depths of the three request trees at these files (depthReqT_the,
Johnson/Goal/Conditions/KeyDepthAtThe.lean; depth_the, Johnson/Goal/Numbers/DepthAtThe.lean; the
copy's file's by unfolding): called in Johnson/Goal/Conditions/HonestAtHome.lean. THE CAPS ARE OF
OUR CHOOSING: that a search within them finds a nonce is completeness' matter, not this file's. NO
COMPLETENESS: nothing here says that a verifier accepts. theHome's limits travel whole
(WiderHome.lean).
Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Conditions.HonestAtWider
import Johnson.Goal.Conditions.HonestNumber
import Johnson.Goal.Description.KeyWritten
import Johnson.Goal.Description.ProofWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

/- No default table of scales is available: a statement that reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace FlashProve
open VerifierAndGoals VerifierAndGoals.Fit FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles Rom
open OnBytes.Prover TypedOracleCompiler.Compile.Batch.Cms

/-- The letters of the goals' description at Z. -/
abbrev sAt (Z : PublicFiles) : DescriptionDataAtFiles (asDescriptionFiles Z) := dataAtFiles flashProveData Z

section
/- Lean compares these names and does not unfold them. -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF FlashProve.thePlan FlashProve.theItem

/-- **The written committer's count, as a numeral.** -/
theorem count₀_live (Z : PublicFiles) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    count₀ Z = 8589982777 := by
  have hd : (R₀ Z).queryLayout.depth = 32 := Johnson.G.fr_a
  have hk : (R₀ Z).queryLayout.K = 24087 := congrArg (· + 1)
    (wireBlocksButOne_atWrittenRounds (sAt Z) (key_built_written Z scope live) (proof_built_written Z scope live))
  unfold count₀
  rw [hd, hk]
  norm_num

end

/-- The sum. -/
theorem honest_number :
    0 + (2 + 8589982777) + (8 + 7068035999651) + 7 + 1 ≤ honestBudget := by
  have h : honestBudget = 2 ^ 48 := rfl
  rw [h]
  norm_num

variable {B N : ℕ} (Rand : Type) (ρOf : Fin (B + 1) → Rand)
  (pf : PublicFiles → (s : IntegerTransformer.Settings) → ModelWeights s → Rand → List Token →
    List Token → Fin (N + 1) → Rom.OComp (rom 256) FormBytes)
  (ra : (Z : PublicFiles) → Rand → Fin ((riDigits Z).n + 1)) (sb : Rand → ℕ → ByteArray)

set_option maxHeartbeats 1600000 in
/-- **HonestWithin at theHome, in scope, where protocolDataWellFormed says yes.** -/
theorem honestWithin_home_live (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy) (hr : readFiles Z = .ok pp)
    (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {Kap : Type}
    (b₀ : (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).LeafBody)
    (st : Strats (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).protocol Kap)
    (iskOf : ModelWeights (settingsOfRead pp) → Rand → ((sAt Z).layoutsByPublicReading allZeroDigest []).D →
      (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).Index ×
        (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).protocol.EncodingRandomness × (ℕ → Bits))
    (xOf : List Token → List Token → (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).Instance)
    (drawOf : Rand → Fin (N + 1) → ((sAt Z).layoutsByPublicReading allZeroDigest []).D →
      Draw 256 (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).protocol
        (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).LeafBody (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).offlineRoundSplits
        (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).linkRoundSplits Kap)
    (print : ModelWeights (settingsOfRead pp) → Rand → List Token → List Token → Fin (N + 1) →
      ((sAt Z).layoutsByPublicReading allZeroDigest []).D → Raw 256 (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).protocol
        (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).offlineRoundSplits (innerCompilerInputAtFullSize ((sAt Z).inputFieldsAtReadings allZeroDigest [])).linkRoundSplits →
      FormBytes)
    (hpf : ∀ w ρ p t a, pf Z (settingsOfRead pp) w ρ p t a =
      proveForm ((sAt Z).layoutsByPublicReading allZeroDigest []) b₀ st (capT (sAt Z)) capL (capB (sAt Z))
        (fun d => carryF ((sAt Z).layoutsByPublicReading allZeroDigest []) (fun _ => firstBlockTestAtDescriptionData (sAt Z) allZeroDigest []) d)
        (iskOf w ρ) (xOf p t) (drawOf ρ a) (print w ρ p t a))
    (paths : ∀ ρ a d, (drawOf ρ a d).coT.path.length = 0 ∧ (drawOf ρ a d).coL.path.length = 0 ∧
      (drawOf ρ a d).coB.path.length = 6) :
    HonestWithin (atSecondHashFunction (theHome Rand ρOf pf ra sb)) Z (settingsOfRead pp) := by
  refine honestWithin_theHome Rand ρOf pf ra sb Z pp hr (8 + 7068035999651) (fun w ρ p t a => ?_) ?_
  · rw [hpf]
    exact honestProverQueryBound_layoutsByPublicReading (sAt Z) allZeroDigest [] b₀ st (capT (sAt Z)) capL (capB (sAt Z)) (iskOf w ρ)
      (xOf p t) (drawOf ρ a) (print w ρ p t a) 7068035999651
      (pub8_queries OnBytes.Tie.recordGround (asDescriptionFiles Z).pol (asDescriptionFiles Z).KL (asDescriptionFiles Z).lay)
      fun d => le_of_eq (allF_written (sAt Z) allZeroDigest [] (key_built_written Z scope live)
        (proof_built_written Z scope live) (drawOf ρ a d) (paths ρ a d).1 (paths ρ a d).2.1
        (paths ρ a d).2.2)
  · rw [count₀_live Z scope live]
    exact honest_number

end FlashProve

#print axioms FlashProve.count₀_live
#print axioms FlashProve.honest_number
#print axioms FlashProve.honestWithin_home_live
