-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/HeldRides.lean: KIND K11 (THE MERGE): ONE PREMISE OF ITS SECOND TIE, PAID AT
THE COMPOSED MEANING: "held" RIDES OVER AN ACCEPTING MERGE. NO SOUNDNESS.

`merge_t2` (Johnson/Top/H0/MergeLaw/TieOneTwo.lean) has a premise hHeld on the meaning's letter
`held`: at every sampled tenant whose pin is open at the border in front, if `held` accepts at the
verifier's state in front of the merge, it accepts at the state behind. At `mgAll D Mg`
(Johnson/Desc/Sound/MgAll.lean) that letter is `smpHeld a.2.st a.2.book j t` (`mgAll_held`, by rfl):
it reads the statement and the book alone, and an accepting merge leaves both (`yes_keeps`,
TieOneTwo.lean, from `isLocal`).
  `merge_held_eq`: behind an accepting merge the letter's value is what it was in front: an
    equation, at every tenant (j, t) and every public part z.
  `merge_hHeld`: **the premise hHeld of merge_t2 to the letter**, at `mgAll D Mg`, at ANY numbers,
    links, places and border.
  `merge_hHeld_full`: the same at the full size's written values: links := linksFull,
    ps := flatPlacesOf linksFull true, k := 346.
Statements and proofs.
Limits. Where the merge rejects, nothing is said. Nothing on what `smpHeld` means, nor on whether it
accepts anywhere: the list of sampled tenants at border 346 is evaluated nowhere here, and the
statement would hold of an empty list too. The other premises of merge_t2 stand. D and Mg stand
under "for all": eight parameters of D are still open by its owner's word. Of completeness's kind:
no error term; nothing on soundness; nothing on hiding.

-/
import Johnson.Top.H0.MergeLaw.TieOneTwo
import Johnson.Desc.Sound.MgAll
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers)
open VerifiableInference.Desc.First.MergeLaw
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- Behind an accepting merge "held" is what it was in front. -/
theorem merge_held_eq (Pm : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (hd : headMergeDecide Pm s rs = .ok s') (z : P) (j t : ℕ) :
    (mgAll D Mg).held j t (z, s') = (mgAll D Mg).held j t (z, s) := by
  obtain ⟨k1, k2, _⟩ := yes_keeps Pm hd
  rw [mgAll_held D Mg]
  show smpHeld s'.st s'.book j t = smpHeld s.st s.book j t
  rw [k1, k2]

/-- **merge_t2's premise hHeld, at the composed meaning.** -/
theorem merge_hHeld (Pm : HeadMergeP) (Nn : Numbers) (links : List ModelPart) (ps : List Place) (k : ℕ)
    (z : P) {Str : Type} (a b : S × Str) (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) :
    ∀ x ∈ First.sampledIn Nn ((First.openSets links ps (First.start links))[k]?.getD []),
      (mgAll D Mg).held x.1 x.2 (z, a.1) = true → (mgAll D Mg).held x.1 x.2 (z, b.1) = true := by
  obtain ⟨rs, hd⟩ := hy
  intro x _ h
  rw [merge_held_eq D Mg Pm hd z x.1 x.2]
  exact h

/-- The same at the full size's written values. -/
theorem merge_hHeld_full (Pm : HeadMergeP) (Nn : Numbers) (z : P) {Str : Type} (a b : S × Str)
    (hy : ∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) :
    ∀ x ∈ First.sampledIn Nn ((First.openSets linksFull (First.flatPlacesOf linksFull true)
        (First.start linksFull))[346]?.getD []),
      (mgAll D Mg).held x.1 x.2 (z, a.1) = true → (mgAll D Mg).held x.1 x.2 (z, b.1) = true :=
  merge_hHeld D Mg Pm Nn linksFull (First.flatPlacesOf linksFull true) 346 z a b hy

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.merge_held_eq
#print axioms VerifiableInference.Desc.Sound.merge_hHeld
#print axioms VerifiableInference.Desc.Sound.merge_hHeld_full
