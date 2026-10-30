-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/PileWithin.lean: TWO PUBLIC ITEMS OF THE LAYER fillK13Plus (FillK13.lean)
("K13.pileWithin", "K13.oneRow": Johnson/Desc/K13/PubK13.lean, Johnson/Desc/K13/Law/MasksDoor.lean):
what their tests say, in the laws' words; who earns "K13.oneRow"; the riders at kind K13's block.
Statements with their proofs. What is owed stands as Props in OwedWithin.lean.
  `rowsWithinC_iff`: the test on the rows' mask entries, in the laws' word (`tableSize`).
  `oneRowC_of_stand`: KIND-FREE: WHERE THE CHAIN DOES NOT STAND AT ITS END THE ITEM SAYS NOTHING: so
  a block in front of kind K13's pays the item's riding at the record BEHIND, out of where the
  promise says that the chain stands there, reading nothing in front.
  `atM3_oneRow`: **kind K13's block earns it**, whatever stood in front: by `rowMasks`
  (RowMasks.lean).
  `rider3_oneRow`: the item is a rider at that block.
  `rider3_pileWithin`: so is "K13.pileWithin" at kind K13's block, FROM `OwedWithinM3`.
What is not claimed. That any other block keeps "K13.pileWithin". Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.FillFromSentences
import Johnson.Desc.K13.Law.RowMasks
import Johnson.Desc.K13.Law.OwedWithin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model OnBytes.Slice
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.First (S Pub Meaning Numbers)

/-- The test on the rows' mask entries, in the laws' word. -/
theorem rowsWithinC_iff (s : S) : rowsWithinC s = true ↔
    ∀ r ∈ s.rows, ∀ t ∈ r.masks, t.1.index < tableSize s.st t.1.oracle .mask := by
  unfold rowsWithinC
  simp only [List.all_eq_true, decide_eq_true_eq, tableSizeC_eq]

/-- **Where the chain does not stand at its end the item says nothing.** -/
theorem oneRowC_of_stand {s : S} (h : First.standOf s ≠ .mem) : oneRowC s = true := by
  unfold oneRowC
  split
  · rename_i a hh
    exact absurd (by simp [First.standOf, hh]) h
  · rfl

/-- At the chain's end the item says: one row, with a mask entry. -/
theorem oneRowC_at_end {s : S} {a : First.MemOwn} (hh : s.here = .mem a) {r : TensorRow}
    (hr : s.rows = [r]) (hne : r.masks ≠ []) : oneRowC s = true := by
  unfold oneRowC
  rw [hh]
  show (match s.rows with
    | [r] => !r.masks.isEmpty
    | _ => false) = true
  rw [hr]
  show (!r.masks.isEmpty) = true
  cases hm : r.masks with
  | nil => exact absurd hm hne
  | cons _ _ => rfl

section
variable {Pp W Cl : Type}

/-- **Kind K13's block earns it.** -/
theorem atM3_oneRow {P : Where} {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (h : (atM3 (Cl := Cl) P).decide s rs gs = .ok s') :
    oneRowC s' = true := by
  obtain ⟨r, hr, _, hne⟩ := rowMasks P s s' rs gs h
  obtain ⟨_, _, o, _, e⟩ := atM3_rec h
  exact oneRowC_at_end (a := o) (by rw [e]) hr hne

theorem rider3_oneRow {P : Where} {Mg : Meaning Pp W}
    (hM : ∀ x, Mg.pub oneRowItem x = oneRowC x.2) (hP : ∀ x, Mg.pubP oneRowItem x) :
    Rider3 Cl P Mg oneRowItem := fun x x' h => by
  obtain ⟨rs, gs, hd⟩ := h.2
  exact ⟨fun _ => by rw [hM]; exact atM3_oneRow hd, fun _ => hP x'⟩

theorem rider3_pileWithin {P : Where} {Mg : Meaning Pp W} (hO : OwedWithinM3)
    (hM : ∀ x, Mg.pub pileWithinItem x = pileWithinC x.2) (hP : ∀ x, Mg.pubP pileWithinItem x) :
    Rider3 Cl P Mg pileWithinItem := fun x x' h => by
  obtain ⟨rs, gs, hd⟩ := h.2
  exact ⟨fun h0 => by
    rw [hM] at h0 ⊢
    exact hO P x.2 x'.2 rs gs hd h0, fun _ => hP x'⟩

end

end VerifiableInference.Desc.K13.Law
