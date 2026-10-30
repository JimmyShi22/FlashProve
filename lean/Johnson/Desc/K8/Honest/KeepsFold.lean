-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/Honest/KeepsFold.lean: THE SMALLNESS TEST: BEHIND THE DRAW's MEMBER NO DRAW IS
COUNTED YET IN THE TEST's DATA: the count `foldDrawn` is 0 there: out of the kind's clause of the
letter keeps alone (`K8Keeps`, Johnson/Desc/K8/Honest/Keeps.lean): the draw's own yes tests that the
count is 0 in front, and the draw lays the matrix and its first columns alone. For whoever lays a
sentence on that count from the draw's member on. Lemmas on the verifier's own text; none of the
library's goals.

  **`K8Keeps.fold0`**, `K8KeepsM.fold0`   ∃ tl', s'.tl? = some tl' ∧ tl'.foldDrawn = 0
  **`K8Keeps.fold0_head`**, `K8KeepsM.fold0_head`   IN THE FORM OF A SENTENCE ON THE OUTPUT HEAD's
                   OWN PART: ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.tl.foldDrawn = 0
  `fold0_of_step`   so behind every accepting step of a block that is seated over the draw's block
NO DEVICE. TACTICS THAT SEARCH: `simp [a list]` on two lines, on what `S.tl?` reads and `S.putTl`
lays at the head's segment.
Limits. From the clause, or a yes, alone. That the chain stands in the head's segment in front of
the member is a premise of the second form. What later members make of the count is not looked at
here: Johnson/Desc/K8/Honest/FoldAtHeadSeg.lean walks it to the front of the head's segment's
batching.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.K8.Honest.KeepsMark

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes.Model VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8
open Johnson.Desc.First.Walk.Tied (StepYes)

/-- **Behind the member the count is 0.** -/
theorem K8Keeps.fold0 {s s' : S} (h : K8Keeps s s') :
    ∃ tl', s'.tl? = some tl' ∧ tl'.foldDrawn = 0 := by
  obtain ⟨tl, cf, first, ht, -, -, -, h0, rfl⟩ := h
  exact ⟨{ tl with cfF := cf, cfFirst := first }, tlP_lawful.get_set s _ tl ht, h0⟩

theorem K8KeepsM.fold0 {s s' : S} (h : K8KeepsM s s') :
    ∃ tl', s'.tl? = some tl' ∧ tl'.foldDrawn = 0 := h.1.fold0

/-- **The same as a sentence on the output head's own part.** -/
theorem K8Keeps.fold0_head {s s' : S} (h : K8Keeps s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.tl.foldDrawn = 0 := by
  intro a ha
  obtain ⟨tl, cf, first, ht, -, -, -, h0, rfl⟩ := h
  have ho : a.opened = true := by
    by_contra hn
    simp [S.tl?, ha, hn] at ht
  exact ⟨{ a with tl := { tl with cfF := cf, cfFirst := first } }, by simp [S.putTl, ha, ho], h0⟩

theorem K8KeepsM.fold0_head {s s' : S} (h : K8KeepsM s s') :
    ∀ a, s.here = .head a → ∃ a', s'.here = .head a' ∧ a'.tl.foldDrawn = 0 := h.1.fold0_head

/-- So behind every accepting step of a block that is seated over the draw's block. -/
theorem fold0_of_step {Cl : Type} {p : Par} {ft : Nat} {blk : Block S Cl} {s s' : S}
    (hs : Seats blk (approximateRangeProofDrawKind (Cl := Cl) atS p)) (hy : StepYes ft blk s s') :
    ∃ tl', s'.tl? = some tl' ∧ tl'.foldDrawn = 0 := (keepsM_of_step hs hy).fold0

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.fold0
#print axioms VerifiableInference.Desc.First.K8.Honest.K8KeepsM.fold0
#print axioms VerifiableInference.Desc.First.K8.Honest.K8Keeps.fold0_head
#print axioms VerifiableInference.Desc.First.K8.Honest.K8KeepsM.fold0_head
#print axioms VerifiableInference.Desc.First.K8.Honest.fold0_of_step
