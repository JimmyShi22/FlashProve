-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K8R/KeyFitOf.lean: THE SMALLNESS TEST: AT EVERY STATE THAT THE FIRST CHAIN's OWN BLOCKS
REACH IN FRONT OF A SEGMENT's BATCHING: `digitsLive` (Johnson/Desc/K8/Honest/DigitsFew.lean) FROM
FOUR PREMISES ON WHAT THE DIGITS' LOOKUP HAS HEARD ALONE: THE THREE TESTS ON PUBLIC NUMBERS OF
`digits_of_silence` (Johnson/P1K8R/DigitsOfSilence.lean) ARE PAID BY `public_at_batch`
(Johnson/P1K8R/PublicAtBatch.lean). Lemmas; NONE OF THE LIBRARY's GOALS. Nothing on completeness,
soundness or hiding.

  `keyFit_of_B`   the test with code `keyFitB` (Johnson/Desc/K8/Honest/PublicOfPieces.lean) gives
      `KeyFit`
  **`digits_at_batch`**   in the goals' scope, at l < 25, at every (z, s) reached at 14 l + 9, or
      347 at the head's segment: s holds data tl, and: tl.heard = some g; g agrees with `lookHeardAt
      tl.f9 0 own` in the eleven fields; a yes of `goodK3Out (faceOf tl.f9) own`; the form of the
      key side's end names no entry: then `digitsLive tl` says yes
Limits. The four premises on g are not shown of any state here. Nothing on `planesLive`. Nothing on
any measure.
-/
import Johnson.P1K8R.DigitsOfSilence
import Johnson.P1K8R.PublicAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K8
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open Johnson.Desc.First.Walk.Tied (Reach)
open ProofFile.Honest.K3 (goodK3Out lookHeardAt OpenSame)

/-- The test with code gives the sentence by name. -/
theorem keyFit_of_B (tl : HTailF2) (h : keyFitB tl = true) : KeyFit tl := by
  unfold keyFitB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_cons,
    List.not_mem_nil, or_false] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hq : ∀ q, q < 2 → q = 0 ∨ q = 1 := fun q hq => by omega
  exact ⟨h1, h2, h3, fun q hq' => (h4 q (hq q hq')).1, fun q hq' => (h4 q (hq q hq')).2⟩

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`digitsLive` at a state reached in front of the batching, from what was heard alone.** -/
theorem digits_at_batch (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : ℕ} (hl : l < 25)
    {z : ProofFile.InstPub} {s : S}
    (h : Reach 0 c.blocksInOrder (ProofFile.startS Z) (14 * l + (if l = 24 then 11 else 9)) (z, s)) :
    ∃ tl, s.tl? = some tl ∧ ∀ (g : Forest.Heard) (own : List Fmt.Drawn), tl.heard = some g →
      OpenSame g (lookHeardAt tl.f9 0 own) → goodK3Out (K3.faceOf tl.f9) own = true →
      g.cEnd.ents.isEmpty = true → digitsLive tl = true := by
  obtain ⟨tl, hts, h1, h2, h3⟩ := public_at_batch hS hR O hl h
  exact ⟨tl, hts, fun g own hg ho hs hc =>
    digits_of_silence tl g own hg ho hs hc (keyFit_of_B tl h3) h2 (cover_of_laid tl h1)⟩

end

end P1K8

#print axioms P1K8.keyFit_of_B
#print axioms P1K8.digits_at_batch
