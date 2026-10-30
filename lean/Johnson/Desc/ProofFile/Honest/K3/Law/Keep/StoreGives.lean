-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Keep/StoreGives.lean: `StoreOk` (Honest/K3/StoreMake.lean)
gives the hypothesis of each sort of stage with a kept state, at every stage that stands in a
lookup's row. Theorems. Each of the first seven is conditional on `StoreOk`, and two of them on
bounds that the later ones show at the stages of the row.

Terms. Honest/K3/GLOSSARY.md. In this file a narrow hypothesis is one of `KeyOk`, `TabOk`, `TieOk`,
`SplitOk`, `Tie0Ok`, `LeavesOk`, `BitsOk`: where a store is passed on, just the fields that the
sort's job reads are those of `Fast.srcOf`.

What is shown.
  `storeOk_key`: `KeyOk R row a i k`, where part i is there and k is below its number of bits.
  `storeOk_tab`: `TabOk R row a l`, where l is below d.
  `storeOk_tie`, `storeOk_split`, `storeOk_tie0`, `storeOk_leaves`, `storeOk_bits`: no bound.
  `stages_key_range`, `stages_tab_range`, `stages_split_range`: a stage `key i k`, `tab l` or
    `split i` that stands in the row is in range. The last is asked by no narrow hypothesis: it
    is the bound of `splitKeep_faithful` (Honest/K3/JobsKeepTie.lean). (Honest/K3/Good/Gives.lean
    and Honest/K3/Law/Steps.lean have the like under other names; they are shown anew here, in
    their words, so that little is imported.)
  `storeOk_key_row`, `storeOk_tab_row`: so at a stage of the row no bound is left.

Hypotheses that remain.
  `hx : StoreOk R row a w h x`. It holds at no store, and at the store that `storeAt` makes of the
    same input and challenges (Honest/K3/Law/Keep/StoreLaw.lean: `storeOk_none`, `storeOk_at`); that
    it stays as more is heard is Honest/K3/Law/Keep/StoreStays.lean's, under that file's hypotheses.
  `hi`, `hk`: (in `storeOk_key`) part i is there; k is below its number of bits. `hl`: (in
    `storeOk_tab`) l is below d. `hs`: (in the last five theorems) the stage stands in the row.

Imported. Honest/K3/Law/Keep/StoreLaw.lean; the five files of the sorts: Honest/K3/JobsKeepKey.lean,
JobsKeepTab.lean, JobsKeepTie.lean, JobsKeepLeaves.lean, JobsKeepBits.lean, and through them
Honest/SumKeep.lean and Honest/SumKeepLaw.lean.

Users. Honest/K3/Law/Keep/SameRounds.lean imports this file. Meant for the row with a kept state
(Honest/K3/RowKeep.lean).

Limits. Out of range `KeyOk` and `TabOk` do not follow: there the store has `#[]` and `Fast.srcOf`
the leaves (Honest/K3/Law/Keep/StoreLaw.lean, § 3).

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Keep.StoreLaw
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepKey
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepTab
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepTie
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepLeaves
import Johnson.Desc.ProofFile.Honest.K3.JobsKeepBits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E)

section
variable {R : Reads} {row : E → Nat → E} {a : At} {w : Ask} {h : List Fmt.Drawn}
  {x : Option Store}

/-! ## 1 The narrow hypotheses -/

/-- **A key level.** Conditional on `StoreOk`; part i is there; k is below its number of bits. -/
theorem storeOk_key (hx : StoreOk R row a w h x) {i k : Nat} (hi : i < a.face.parts.length)
    (hk : k < a.face.parts.getD i 0) : KeyOk R row a i k w h x := fun st e => by
  have e2 := hx st e
  subst e2
  exact Fast.storeOf_key _ _ _ _ _ i (k + 1) hi hk

/-- **A level of the table side.** Conditional on `StoreOk`; l is below d. -/
theorem storeOk_tab (hx : StoreOk R row a w h x) {l : Nat} (hl : l < a.face.d) :
    TabOk R row a l w h x := fun st e => by
  have e2 := hx st e
  subst e2
  exact Fast.storeOf_tab _ _ _ _ _ (l + 1) hl

/-- **The tie's steps from 1 on.** Conditional on `StoreOk`. -/
theorem storeOk_tie (hx : StoreOk R row a w h x) : TieOk R row a w h x := fun st e => by
  have e2 := hx st e
  subst e2
  exact Fast.storeOf_tab _ _ _ _ _ 0 (Nat.zero_le _)

/-- **The parts' steps.** Conditional on `StoreOk`. -/
theorem storeOk_split (hx : StoreOk R row a w h x) : SplitOk R row a w h x := fun st e i hi => by
  have e2 := hx st e
  subst e2
  exact Fast.storeOf_key _ _ _ _ _ i 0 hi (Nat.zero_le _)

/-- **The tie's step 0.** Conditional on `StoreOk`. -/
theorem storeOk_tie0 (hx : StoreOk R row a w h x) : Tie0Ok R row a w h x :=
  ⟨storeOk_split hx, storeOk_tie hx⟩

/-- **The leaves.** Conditional on `StoreOk`. -/
theorem storeOk_leaves (hx : StoreOk R row a w h x) : LeavesOk R row a w h x := fun st e => by
  have e2 := hx st e
  subst e2
  exact ⟨rfl, rfl⟩

/-- **The bits.** Conditional on `StoreOk`. -/
theorem storeOk_bits (hx : StoreOk R row a w h x) : BitsOk R row a w h x := fun st e => by
  have e2 := hx st e
  subst e2
  rfl

end

/-! ## 2 The stages of the row are in range -/

/-- A key level that stands in the row: its part is there, and the level is below the part's number
of bits. -/
theorem stages_key_range {f : LFace} {i k : Nat} (hs : Stage.key i k ∈ stages f) :
    i < f.parts.length ∧ k < f.parts.getD i 0 := by
  have hh : ∃ y ∈ f.parts.zipIdx,
      Stage.key i k ∈ (List.range y.1).flatMap fun m => [Stage.key y.2 m, Stage.keyLine y.2 m] := by
    unfold stages at hs
    simp only [List.mem_append] at hs
    rcases hs with hs | h
    · rcases hs with hs | h
      · rcases hs with hs | h
        · exfalso
          by_cases hc : f.shifted = true <;> simp [hc] at hs
        · exact List.mem_flatMap.1 h
      · exfalso
        simp at h
    · exfalso
      simp at h
  obtain ⟨y, hy, h1⟩ := hh
  obtain ⟨m, hm, h2⟩ := List.mem_flatMap.1 h1
  simp only [List.mem_cons, Stage.key.injEq, reduceCtorEq, List.not_mem_nil, or_false] at h2
  obtain ⟨rfl, rfl⟩ := h2
  obtain ⟨hi, e⟩ := List.getElem?_eq_some_iff.1 (List.mem_zipIdx_iff_getElem?.1 hy)
  refine ⟨hi, ?_⟩
  rw [List.getD_eq_getElem _ _ hi, e]
  exact List.mem_range.1 hm

/-- A level of the table side that stands in the row is below d. -/
theorem stages_tab_range {f : LFace} {l : Nat} (hs : Stage.tab l ∈ stages f) : l < f.d := by
  unfold stages at hs
  by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs

/-- A parts' step that stands in the row: its part is there, and one more behind it. -/
theorem stages_split_range {f : LFace} {i : Nat} (hs : Stage.split i ∈ stages f) :
    i + 1 < f.parts.length := by
  have h : i < f.parts.length - 1 := by
    unfold stages at hs
    by_cases hc : f.shifted = true <;> simp [hc] at hs <;> exact hs
  omega

/-! ## 3 At the stages of the row -/

/-- **A key level of the row.** Conditional on `StoreOk`. -/
theorem storeOk_key_row {R : Reads} {row : E → Nat → E} {a : At} {w : Ask} {h : List Fmt.Drawn}
    {x : Option Store} (hx : StoreOk R row a w h x) {i k : Nat}
    (hs : Stage.key i k ∈ stages a.face) : KeyOk R row a i k w h x :=
  storeOk_key hx (stages_key_range hs).1 (stages_key_range hs).2

/-- **A level of the table side of the row.** Conditional on `StoreOk`. -/
theorem storeOk_tab_row {R : Reads} {row : E → Nat → E} {a : At} {w : Ask} {h : List Fmt.Drawn}
    {x : Option Store} (hx : StoreOk R row a w h x) {l : Nat}
    (hs : Stage.tab l ∈ stages a.face) : TabOk R row a l w h x :=
  storeOk_tab hx (stages_tab_range hs)

end ProofFile.Honest.K3

#print axioms ProofFile.Honest.K3.storeOk_key
#print axioms ProofFile.Honest.K3.storeOk_tab
#print axioms ProofFile.Honest.K3.storeOk_tie
#print axioms ProofFile.Honest.K3.storeOk_split
#print axioms ProofFile.Honest.K3.storeOk_tie0
#print axioms ProofFile.Honest.K3.storeOk_leaves
#print axioms ProofFile.Honest.K3.storeOk_bits
#print axioms ProofFile.Honest.K3.stages_key_range
#print axioms ProofFile.Honest.K3.stages_tab_range
#print axioms ProofFile.Honest.K3.stages_split_range
#print axioms ProofFile.Honest.K3.storeOk_key_row
#print axioms ProofFile.Honest.K3.storeOk_tab_row
