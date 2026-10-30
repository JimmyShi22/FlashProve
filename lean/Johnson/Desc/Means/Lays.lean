-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Lays.lean: a row carried to a group's tables means there what it means of the
words.

addToGroupRow adds x times a row to a group's row. This file shows the law LaysRight of it: at the
layout that the statement gives the group, for a row that has passed the tests of the adding, it
returns a group's row, and for all words the new group's row is short of its target, on the group's
tables as the words fill them, by what the old one was short of plus x times what the row is short
of on the words; and no coefficient is laid where the tables hold no word. So a row laid alone holds
of the tables just if it holds of the words (rowMeans).

The entry-by-entry laws of OnBytes/Iop/RowLaws.lean and MaskLaws.lean are used; their conditions on
the layout are met by Johnson/Desc/Means/Layout.lean.

Main theorems: placeOk_iff, RowIn.fits, RowIn.maskFits, addToGroupRow_total, coefficient_off,
main_part, mask_part, lays_eq, lays_clean, laysRight, rowMeans.

What is not claimed. Nothing on rows that have not passed the tests of RowIn: a sample row does not
go through the adding. Nothing on how words are tied to what a prover has sent, or on soundness.

-/
import Johnson.Desc.Means.Layout
import Johnson.Desc.Means.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S : Statement} {G : Group} {L : GroupLayout} {row : Row}

/-! ## What the tests give -/

/-- What the test of a place says. -/
theorem placeOk_iff (S : Statement) (G : Group) (o : Nat) (part : Part) (vars index : Nat) :
    Blk.placeOk S G o part vars index = true ↔
      o ∈ G.members.toList ∧ S.has o part = true ∧ vars = S.tableBits o part ∧
        index < 2 ^ S.tableBits o part := by
  unfold Blk.placeOk
  simp [and_assoc]

/-- A row that has passed the tests meets the condition of the laws on batching. -/
theorem RowIn.fits (h : RowIn S G row) : RowFits S row := by
  refine ⟨fun t ht => ?_, fun w hw => (h.runs w hw).2.1, fun f hf v hv => ?_⟩
  · rw [((placeOk_iff _ _ _ _ _ _).1 (h.terms t ht)).2.2.1]
    exact Nat.le_add_right _ _
  · have h1 := (h.forms f hf).2
    unfold Form.fits at h1
    simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h1
    rw [(h1.1 v hv).1]
    exact Nat.le_add_right _ _

/-- Its structured vectors on mask tables reach over all places of the group. -/
theorem RowIn.maskFits (F : LayFacts S G L) (h : RowIn S G row) : MaskFits S L row := by
  intro t ht hp
  obtain ⟨hm, hh, hv, _⟩ := (placeOk_iff _ _ _ _ _ _).1 (h.terms t ht)
  rw [hp] at hh hv
  rw [hv, ← F.mask_places _ hm hh]
  exact Nat.le_refl _

/-! ## A row is returned -/

/-- A fold that may fail does not fail if no step fails under a condition that the steps keep. -/
theorem foldlM_total {α β : Type} (P : β → Prop) (step : β → α → Option β) :
    ∀ (l : List α), (∀ a ∈ l, ∀ b, P b → ∃ b', step b a = some b' ∧ P b') →
    ∀ b, P b → ∃ b', l.foldlM step b = some b' ∧ P b'
  | [], _, b, hp => ⟨b, rfl, hp⟩
  | a :: l, hs, b, hp => by
    obtain ⟨b1, h1, p1⟩ := hs a List.mem_cons_self b hp
    obtain ⟨b2, h2, p2⟩ := foldlM_total P step l
      (fun a' ha' => hs a' (List.mem_cons_of_mem _ ha')) b1 p1
    refine ⟨b2, ?_, p2⟩
    rw [List.foldlM_cons, h1]
    exact h2

/-- A structured vector on a member's table is carried. -/
theorem addTermTo_total (F : LayFacts S G L) (x : E) (acc : GroupRow) (t : Term)
    (ht : Blk.placeOk S G t.oracle t.part t.v.vars 0 = true) :
    ∃ acc', addTermTo S L x acc t = some acc' := by
  obtain ⟨hm, hh, _, _⟩ := (placeOk_iff _ _ _ _ _ _).1 ht
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addTermTo
  cases hp : t.part with
  | main =>
    rw [hp] at hh
    by_cases hk : L.kept.getD i false = true
    · simp only [hf, hk, if_true]
      exact ⟨_, rfl⟩
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
      have hlt : ¬ L.k < S.rowBits t.oracle .main :=
        Nat.not_lt.2 (F.main_block _ i first hf hmf).2.2.le
      simp only [hf, hk', hmf, hlt, Bool.false_eq_true, if_false]
      exact ⟨_, rfl⟩
  | mask =>
    rw [hp] at hh
    obtain ⟨first, hmf⟩ := F.mask_block_of _ i hf hh
    have hlt : ¬ L.h < S.rowBits t.oracle .mask :=
      Nat.not_lt.2 (F.mask_block _ i first hf hmf).2.le
    simp only [hf, hmf, hlt, if_false]
    exact ⟨_, rfl⟩

/-- A coefficient on an entry of a member's table is carried. -/
theorem addEntryTo_total (F : LayFacts S G L) (x : E) (acc : GroupRow) (o : Nat) (part : Part)
    (index : Nat) (coeff : E) (hm : o ∈ G.members.toList) (hh : S.has o part = true)
    (hi : index < 2 ^ S.tableBits o part) (hs : acc.d.size = 2 ^ (L.h + L.logEllZk)) :
    ∃ acc', addEntryTo S L x acc o part index coeff = some acc' := by
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addEntryTo
  cases part with
  | main =>
    by_cases hk : L.kept.getD i false = true
    · simp only [hf, hk, if_true]
      exact ⟨_, rfl⟩
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
      simp only [hf, hk', hmf, Bool.false_eq_true, if_false]
      exact ⟨_, rfl⟩
  | mask =>
    obtain ⟨first, hmf⟩ := F.mask_block_of _ i hf hh
    have hlt : groupIndex index (S.rowBits o .mask) first L.h < acc.d.size := by
      rw [hs]
      apply groupIndex_lt _ _ _ _ _ (F.mask_block _ i first hf hmf).2
      rw [← F.mask_places _ hm hh]
      exact hi
    simp only [hf, hmf, hlt, if_true]
    exact ⟨_, rfl⟩

/-- A whole coefficient vector on a member's main table is carried. -/
theorem addFormTo_total (F : LayFacts S G L) (x : E) (acc : GroupRow) (f : MainForm)
    (hm : f.oracle ∈ G.members.toList) (hh : S.has f.oracle .main = true) :
    ∃ acc', addFormTo S L x acc f = some acc' := by
  obtain ⟨i, hf⟩ := F.find_of_mem _ hm
  unfold addFormTo
  by_cases hk : L.kept.getD i false = true
  · simp only [hf, hk, if_true]
    exact ⟨_, rfl⟩
  · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
    obtain ⟨first, hmf⟩ := F.main_block_of _ i hf hh hk'
    have hlt : ¬ L.k < S.rowBits f.oracle .main :=
      Nat.not_lt.2 (F.main_block _ i first hf hmf).2.2.le
    simp only [hf, hk', hmf, hlt, Bool.false_eq_true, if_false]
    exact ⟨_, rfl⟩

/-- The blocks of the mask rows, in the form of the laws on batching. -/
theorem LayFacts.maskOk (F : LayFacts S G L) : MaskBlocksOk S L :=
  fun o i first hf hm => (F.mask_block o i first hf hm).2

/-- The blocks of the main rows, in the form of the laws on batching. -/
theorem LayFacts.mainOk (F : LayFacts S G L) : MainBlocksOk S L :=
  fun o i first hf hm => (F.main_block o i first hf hm).2.2

include ρ in
/-- **A row that has passed the tests is carried.** (The reading serves the proof alone.) -/
theorem addToGroupRow_total (F : LayFacts S G L) (hr : RowIn S G row) (x : E) (acc : GroupRow)
    (hp : MaskReady L acc) : ∃ acc', addToGroupRow S L row x acc = some acc' := by
  have p0 := (GroupRow.ready_d ρ acc L hp 0).1
  have pos : 0 < 2 ^ (L.h + L.logEllZk) := Nat.two_pow_pos _
  obtain ⟨a1, h1, p1⟩ := foldlM_total (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (addTermTo S L x) row.terms.toList (fun t ht b hb => by
      obtain ⟨b', hb'⟩ := addTermTo_total F x b t (hr.terms t ht)
      exact ⟨b', hb', (addTermTo_mask ρ S L x b b' t (hr.fits.terms t ht) (hr.maskFits F t ht) hb'
        0 pos hb).1⟩) _ p0
  obtain ⟨a2, h2, p2⟩ := foldlM_total (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (fun acc (u : Single) => addEntryTo S L x acc u.oracle u.part u.index u.coeff)
    row.units.toList (fun u hu b hb => by
      obtain ⟨hm, hh, _, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 (hr.units u hu)
      obtain ⟨b', hb'⟩ := addEntryTo_total F x b u.oracle u.part u.index u.coeff hm hh hi hb
      exact ⟨b', hb', (addEntryTo_mask ρ S L F.maskOk x b b' _ _ _ _ hb' 0 pos hb).1⟩) _ p1
  obtain ⟨a3, h3, p3⟩ := foldlM_total (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (addRunTo S L x) row.runs.toList (fun w hw b hb => by
      obtain ⟨h0, h1, hpl⟩ := hr.runs w hw
      obtain ⟨hm, hh, _, hi⟩ := (placeOk_iff _ _ _ _ _ _).1 hpl
      obtain ⟨b', hb', _⟩ := foldlM_total
        (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
        (fun acc j => addEntryTo S L x acc w.oracle w.part (w.first + w.step * j) (w.coeffs.get j))
        (List.range w.coeffs.size) (fun j hj c hc => by
          have hj' : j ≤ w.coeffs.size - 1 := by
            have := List.mem_range.1 hj
            omega
          have hlt : w.first + w.step * j < 2 ^ S.tableBits w.oracle w.part :=
            Nat.lt_of_le_of_lt (Nat.add_le_add_left (Nat.mul_le_mul_left _ hj') _) hi
          obtain ⟨c', hc'⟩ := addEntryTo_total F x c w.oracle w.part (w.first + w.step * j)
            (w.coeffs.get j) hm hh hlt hc
          exact ⟨c', hc', (addEntryTo_mask ρ S L F.maskOk x c c' _ _ _ _ hc' 0 pos hc).1⟩) b hb
      exact ⟨b', hb', (addRunTo_mask ρ S L F.maskOk x b b' w h1 hb' 0 pos hb).1⟩) _ p2
  obtain ⟨a4, h4, _⟩ := foldlM_total (fun g : GroupRow => g.d.size = 2 ^ (L.h + L.logEllZk))
    (addFormTo S L x) row.forms.toList (fun f hf b hb => by
      obtain ⟨hm, hh, _, _⟩ := (placeOk_iff _ _ _ _ _ _).1 (hr.forms f hf).1
      obtain ⟨b', hb'⟩ := addFormTo_total F x b f hm hh
      have e : b'.d.size = 2 ^ (L.h + L.logEllZk) := by
        rw [addFormTo_mask S L x b b' f hb']
        exact hb
      exact ⟨b', hb', e⟩) _ p3
  unfold addToGroupRow
  simp only [← Array.foldlM_toList, h1, h2, h3, h4, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]
  exact ⟨_, rfl⟩

/-! ## Where a row has no coefficient -/

theorem sum_map_zero {α : Type} (l : List α) (f : α → K) (h : ∀ a ∈ l, f a = 0) :
    (l.map f).sum = 0 := by
  apply List.sum_eq_zero
  intro y hy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hy
  exact h a ha

/-- A row that has passed the tests has the coefficient 0 on what is no member. -/
theorem coefficient_off (hr : RowIn S G row) {o : Nat} (ho : o ∉ G.members.toList) (part : Part)
    (idx : Nat) : ρ.val (row.coefficient o part idx) = 0 := by
  rw [Row.coefficient_val]
  have add4 : ∀ a b c d : K, a = 0 → b = 0 → c = 0 → d = 0 → a + b + c + d = 0 := by
    intro a b c d ha hb hc hd
    rw [ha, hb, hc, hd]
    simp
  apply add4
  · apply sum_map_zero
    intro t ht
    have hne : t.oracle ≠ o := fun c => ho (c ▸ ((placeOk_iff _ _ _ _ _ _).1 (hr.terms t ht)).1)
    simp only [hne, false_and, if_false]
  · apply sum_map_zero
    intro u hu
    have hne : u.oracle ≠ o := fun c => ho (c ▸ ((placeOk_iff _ _ _ _ _ _).1 (hr.units u hu)).1)
    simp only [hne, false_and, if_false]
  · apply sum_map_zero
    intro w hw
    have hne : w.oracle ≠ o :=
      fun c => ho (c ▸ ((placeOk_iff _ _ _ _ _ _).1 (hr.runs w hw).2.2).1)
    simp only [hne, false_and, if_false]
  · apply sum_map_zero
    intro f hf
    have hne : f.oracle ≠ o :=
      fun c => ho (c ▸ ((placeOk_iff _ _ _ _ _ _).1 (hr.forms f hf).1).1)
    simp only [hne, false_and, if_false]

/-! ## The weights -/

theorem mainWeight_none {o : Nat} (h : L.find o = none) (J : Nat) :
    mainWeight (K := K) S L o J = 0 := by
  simp only [mainWeight, h]

theorem mainWeight_kept {o i : Nat} (hf : L.find o = some i) (hk : L.kept.getD i false = true)
    (J : Nat) : mainWeight (K := K) S L o J = 0 := by
  simp only [mainWeight, hf, hk, if_true]

theorem mainWeight_noBlock {o i : Nat} (hf : L.find o = some i)
    (hm : L.mainFirst.getD i none = none) (J : Nat) : mainWeight (K := K) S L o J = 0 := by
  simp only [mainWeight, hf, hm, ite_self]

theorem maskWeight_none {o : Nat} (h : L.find o = none) (J : Nat) :
    maskWeight (K := K) S L o J = 0 := by
  simp only [maskWeight, h]

theorem maskWeight_noBlock {o i : Nat} (hf : L.find o = some i)
    (hm : L.maskFirst.getD i none = none) (J : Nat) : maskWeight (K := K) S L o J = 0 := by
  simp only [maskWeight, hf, hm]

/-- At an index whose row is in a member's block every other oracle message has the weight 0. -/
theorem mainWeight_other (F : LayFacts S G L) {o o' i first J : Nat} (hne : o' ≠ o)
    (hf : L.find o = some i) (hm : L.mainFirst.getD i none = some first)
    (hJ : first ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < first + 2 ^ S.rowBits o .main) :
    mainWeight (K := K) S L o' J = 0 := by
  cases hf' : L.find o' with
  | none => exact mainWeight_none hf' J
  | some i' =>
    by_cases hk' : L.kept.getD i' false = true
    · exact mainWeight_kept hf' hk' J
    · cases hm' : L.mainFirst.getD i' none with
      | none => exact mainWeight_noBlock hf' hm' J
      | some first' =>
        rw [mainWeight_rows S L o' i' first' J hf' (Bool.eq_false_iff.2 hk') hm'
          (F.main_block o' i' first' hf' hm').2.2, if_neg]
        have := F.main_apart o' o i' i first' first hne hf' hf hm' hm
        omega

@[inherit_doc mainWeight_other]
theorem maskWeight_other (F : LayFacts S G L) {o o' i first J : Nat} (hne : o' ≠ o)
    (hf : L.find o = some i) (hm : L.maskFirst.getD i none = some first)
    (hJ : first ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < first + 2 ^ S.rowBits o .mask) :
    maskWeight (K := K) S L o' J = 0 := by
  cases hf' : L.find o' with
  | none => exact maskWeight_none hf' J
  | some i' =>
    cases hm' : L.maskFirst.getD i' none with
    | none => exact maskWeight_noBlock hf' hm' J
    | some first' =>
      rw [maskWeight_rows S L o' i' first' J hf' hm' (F.mask_block o' i' first' hf' hm').2, if_neg]
      have := F.mask_apart o' o i' i first' first hne hf' hf hm' hm
      omega

/-- At an index whose row is in no member's block every weight is 0. -/
theorem mainWeight_off (F : LayFacts S G L) {J : Nat} (h : OffMain S L J) (o : Nat) :
    mainWeight (K := K) S L o J = 0 := by
  cases hf : L.find o with
  | none => exact mainWeight_none hf J
  | some i =>
    by_cases hk : L.kept.getD i false = true
    · exact mainWeight_kept hf hk J
    · cases hm : L.mainFirst.getD i none with
      | none => exact mainWeight_noBlock hf hm J
      | some first =>
        have h' : ¬ (first ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < first + 2 ^ S.rowBits o .main) :=
          h o i first hf (Bool.eq_false_iff.2 hk) hm
        rw [mainWeight_rows S L o i first J hf (Bool.eq_false_iff.2 hk) hm
          (F.main_block o i first hf hm).2.2, if_neg h']

@[inherit_doc mainWeight_off]
theorem maskWeight_off (F : LayFacts S G L) {J : Nat} (h : OffMask S L J) (o : Nat) :
    maskWeight (K := K) S L o J = 0 := by
  cases hf : L.find o with
  | none => exact maskWeight_none hf J
  | some i =>
    cases hm : L.maskFirst.getD i none with
    | none => exact maskWeight_noBlock hf hm J
    | some first =>
      have h' : ¬ (first ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < first + 2 ^ S.rowBits o .mask) :=
        h o i first hf hm
      rw [maskWeight_rows S L o i first J hf hm (F.mask_block o i first hf hm).2, if_neg h']

/-- What is no kept member has the weight 0. -/
theorem keptWeight_off {o : Nat} (h : ¬ KeptAt L o) : keptWeight (K := K) L o = 0 := by
  cases hf : L.find o with
  | none => simp only [keptWeight, hf]
  | some i =>
    have hk : L.kept.getD i false = false := Bool.eq_false_iff.2 fun c => h ⟨i, hf, c⟩
    simp only [keptWeight, hf, hk, Bool.false_eq_true, if_false]

/-- A kept member has the weight 1. -/
theorem keptWeight_at {o : Nat} (h : KeptAt L o) : keptWeight (K := K) L o = 1 := by
  obtain ⟨i, hf, hk⟩ := h
  simp only [keptWeight, hf, hk, if_true]

/-! ## One oracle message at a time -/

/-- A member with a block in the main table: what the row adds there, on the member's entries, is x
times the row on the member's main table. -/
theorem main_block_sum (F : LayFacts S G L) (row : Row) (x : E) (m : Words K) {o i first : Nat}
    (hf : L.find o = some i) (hm : L.mainFirst.getD i none = some first) :
    (∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)), row.mainSum ρ S L x J *
      (mainWeight (K := K) S L o J * m o .main (mainBack S L o J))) =
      ρ.val x * onTable ρ S row m o .main := by
  obtain ⟨hh, hk, hb⟩ := F.main_block o i first hf hm
  have hsize : tableSize S o .main = 2 ^ (S.rowBits o .main + L.logEll) := by
    unfold tableSize Statement.tableBits
    rw [if_pos hh, F.main_places o (F.mem_of_find o i hf) hh]
  have e1 : ∀ J ∈ Finset.range (2 ^ (L.k + L.logEll)), row.mainSum ρ S L x J *
      (mainWeight (K := K) S L o J * m o .main (mainBack S L o J)) =
      (if first ≤ J % 2 ^ L.k ∧ J % 2 ^ L.k < first + 2 ^ S.rowBits o .main then (1 : K) else 0) *
        (row.mainSum ρ S L x J * m o .main (mainBack S L o J)) := by
    intro J _
    rw [mainWeight_rows S L o i first J hf hk hm hb]
    ring
  rw [Finset.sum_congr rfl e1, weight_sum _ _ _ _ hb
    (fun J => row.mainSum ρ S L x J * m o .main (mainBack S L o J))]
  unfold onTable
  rw [hsize, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro idx _
  have hback : mainBack S L o (groupIndex idx (S.rowBits o .main) first L.k) = idx :=
    unshift_groupIndex idx _ first L.k hb
  have hrow := groupIndex_row idx (S.rowBits o .main) first L.k hb
  have hlt := Nat.mod_lt idx (Nat.two_pow_pos (S.rowBits o .main))
  have hin : first ≤ groupIndex idx (S.rowBits o .main) first L.k % 2 ^ L.k ∧
      groupIndex idx (S.rowBits o .main) first L.k % 2 ^ L.k <
        first + 2 ^ S.rowBits o .main := by
    rw [hrow]
    omega
  have h1 : mainWeight (K := K) S L o (groupIndex idx (S.rowBits o .main) first L.k) = 1 := by
    rw [mainWeight_rows S L o i first _ hf hk hm hb, if_pos hin]
  rw [Row.mainSum_member ρ S L x row o _ h1 (fun o' hne => mainWeight_other F hne hf hm hin),
    hback]
  ring

/-- The like for the mask table. -/
theorem mask_block_sum (F : LayFacts S G L) (row : Row) (x : E) (m : Words K) {o i first : Nat}
    (hf : L.find o = some i) (hm : L.maskFirst.getD i none = some first) :
    (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)), row.maskSum ρ S L x J *
      (maskWeight (K := K) S L o J * m o .mask (maskBack S L o J))) =
      ρ.val x * onTable ρ S row m o .mask := by
  obtain ⟨hh, hb⟩ := F.mask_block o i first hf hm
  have hsize : tableSize S o .mask = 2 ^ (S.rowBits o .mask + L.logEllZk) := by
    unfold tableSize Statement.tableBits
    rw [if_pos hh, F.mask_places o (F.mem_of_find o i hf) hh]
  have e1 : ∀ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)), row.maskSum ρ S L x J *
      (maskWeight (K := K) S L o J * m o .mask (maskBack S L o J)) =
      (if first ≤ J % 2 ^ L.h ∧ J % 2 ^ L.h < first + 2 ^ S.rowBits o .mask then (1 : K) else 0) *
        (row.maskSum ρ S L x J * m o .mask (maskBack S L o J)) := by
    intro J _
    rw [maskWeight_rows S L o i first J hf hm hb]
    ring
  rw [Finset.sum_congr rfl e1, weight_sum _ _ _ _ hb
    (fun J => row.maskSum ρ S L x J * m o .mask (maskBack S L o J))]
  unfold onTable
  rw [hsize, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro idx _
  have hback : maskBack S L o (groupIndex idx (S.rowBits o .mask) first L.h) = idx :=
    unshift_groupIndex idx _ first L.h hb
  have hrow := groupIndex_row idx (S.rowBits o .mask) first L.h hb
  have hlt := Nat.mod_lt idx (Nat.two_pow_pos (S.rowBits o .mask))
  have hin : first ≤ groupIndex idx (S.rowBits o .mask) first L.h % 2 ^ L.h ∧
      groupIndex idx (S.rowBits o .mask) first L.h % 2 ^ L.h <
        first + 2 ^ S.rowBits o .mask := by
    rw [hrow]
    omega
  have h1 : maskWeight (K := K) S L o (groupIndex idx (S.rowBits o .mask) first L.h) = 1 := by
    rw [maskWeight_rows S L o i first _ hf hm hb, if_pos hin]
  rw [Row.maskSum_member ρ S L x row o _ h1 (fun o' hne => maskWeight_other F hne hf hm hin),
    hback]
  ring

/-- A table that is not there has no entry. -/
theorem tableSize_zero {o : Nat} {part : Part} (h : S.has o part = false) :
    tableSize S o part = 0 := by
  unfold tableSize
  rw [h]
  rfl

/-- Every oracle message: what the row adds on its entries in the group's main table, and on its own
main table if it is kept, is x times the row on its main table. -/
theorem main_part (F : LayFacts S G L) (hr : RowIn S G row) (x : E) (m : Words K) (o : Nat) :
    (∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)), row.mainSum ρ S L x J *
      (mainWeight (K := K) S L o J * m o .main (mainBack S L o J))) +
    (∑ i ∈ Finset.range (tableSize S o .main),
      keptWeight (K := K) L o * ρ.val (row.coefficient o .main i) * ρ.val x *
        (keptWeight (K := K) L o * m o .main i)) =
      ρ.val x * onTable ρ S row m o .main := by
  cases hf : L.find o with
  | none =>
    have hw : ∀ J, mainWeight (K := K) S L o J = 0 := mainWeight_none hf
    have hc : ∀ idx, ρ.val (row.coefficient o .main idx) = 0 :=
      coefficient_off ρ hr (fun hmem => by
        obtain ⟨i, hi⟩ := F.find_of_mem o hmem
        rw [hf] at hi
        cases hi) .main
    simp only [hw, hc, onTable, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
  | some i =>
    by_cases hk : L.kept.getD i false = true
    · have hw : ∀ J, mainWeight (K := K) S L o J = 0 := mainWeight_kept hf hk
      have hkw : keptWeight (K := K) L o = 1 := by simp only [keptWeight, hf, hk, if_true]
      simp only [hw, hkw, zero_mul, mul_zero, Finset.sum_const_zero, zero_add, one_mul]
      unfold onTable
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · have hk' : L.kept.getD i false = false := Bool.eq_false_iff.2 hk
      have hkw : keptWeight (K := K) L o = 0 := by
        simp only [keptWeight, hf, hk', Bool.false_eq_true, if_false]
      cases hm : L.mainFirst.getD i none with
      | some first =>
        rw [main_block_sum ρ F row x m hf hm]
        simp only [hkw, zero_mul, Finset.sum_const_zero, add_zero]
      | none =>
        have hh : S.has o .main = false := by
          apply Bool.eq_false_iff.2
          intro c
          obtain ⟨first, h⟩ := F.main_block_of o i hf c hk'
          rw [hm] at h
          cases h
        have hw : ∀ J, mainWeight (K := K) S L o J = 0 := mainWeight_noBlock hf hm
        simp only [hw, onTable, tableSize_zero hh, Finset.range_zero, Finset.sum_empty, zero_mul,
          mul_zero, Finset.sum_const_zero, add_zero]

/-- Every oracle message: what the row adds on its entries in the group's mask table is x times the
row on its mask table. -/
theorem mask_part (F : LayFacts S G L) (hr : RowIn S G row) (x : E) (m : Words K) (o : Nat) :
    (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)), row.maskSum ρ S L x J *
      (maskWeight (K := K) S L o J * m o .mask (maskBack S L o J))) =
      ρ.val x * onTable ρ S row m o .mask := by
  cases hf : L.find o with
  | none =>
    have hw : ∀ J, maskWeight (K := K) S L o J = 0 := maskWeight_none hf
    have hc : ∀ idx, ρ.val (row.coefficient o .mask idx) = 0 :=
      coefficient_off ρ hr (fun hmem => by
        obtain ⟨i, hi⟩ := F.find_of_mem o hmem
        rw [hf] at hi
        cases hi) .mask
    simp only [hw, hc, onTable, zero_mul, mul_zero, Finset.sum_const_zero]
  | some i =>
    cases hm : L.maskFirst.getD i none with
    | some first => exact mask_block_sum ρ F row x m hf hm
    | none =>
      have hh : S.has o .mask = false := by
        apply Bool.eq_false_iff.2
        intro c
        obtain ⟨first, h⟩ := F.mask_block_of o i hf c
        rw [hm] at h
        cases h
      have hw : ∀ J, maskWeight (K := K) S L o J = 0 := maskWeight_noBlock hf hm
      simp only [hw, onTable, tableSize_zero hh, Finset.range_zero, Finset.sum_empty, zero_mul,
        mul_zero, Finset.sum_const_zero]

/-! ## The law -/

/-- The equation of the law, at any layout that has the facts. -/
theorem lays_eq (F : LayFacts S G L) (hr : RowIn S G row) (x : E) (acc acc' : GroupRow)
    (hp : MaskReady L acc) (h : addToGroupRow S L row x acc = some acc') (m : Words K) :
    groupValue ρ S L acc' (tablesOf S L m) - ρ.val acc'.target =
      groupValue ρ S L acc (tablesOf S L m) - ρ.val acc.target +
        ρ.val x * (value ρ S row m - ρ.val row.target) := by
  have eT := addToGroupRow_target ρ S L row x acc acc' h
  have eA : (∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)),
        ρ.val (acc'.c.entry J) * (tablesOf S L m).main J) =
      (∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)),
        ρ.val (acc.c.entry J) * (tablesOf S L m).main J) +
      ∑ o ∈ Finset.range S.oracles.size, ∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)),
        row.mainSum ρ S L x J * (mainWeight (K := K) S L o J * m o .main (mainBack S L o J)) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J _
    rw [addToGroupRow_main ρ S L F.mainOk row hr.fits x acc acc' h J, add_mul, ← Finset.mul_sum]
    rfl
  have eB : (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
        ρ.val (acc'.d.getD J zeroE) * (tablesOf S L m).mask J) =
      (∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
        ρ.val (acc.d.getD J zeroE) * (tablesOf S L m).mask J) +
      ∑ o ∈ Finset.range S.oracles.size, ∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
        row.maskSum ρ S L x J * (maskWeight (K := K) S L o J * m o .mask (maskBack S L o J)) := by
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [(addToGroupRow_mask ρ S L F.maskOk row hr.fits (hr.maskFits F) x acc acc' hp h J
      (Finset.mem_range.1 hJ)).2, add_mul, ← Finset.mul_sum]
    rfl
  have eC : (∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
        keptSum ρ o i acc'.kept.toList * (tablesOf S L m).kept o i) =
      (∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
        keptSum ρ o i acc.kept.toList * (tablesOf S L m).kept o i) +
      ∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
        keptWeight (K := K) L o * ρ.val (row.coefficient o .main i) * ρ.val x *
          (keptWeight (K := K) L o * m o .main i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [addToGroupRow_kept ρ S L row hr.fits x acc acc' h o i, add_mul]
    rfl
  have eV : ρ.val x * value ρ S row m =
      (∑ o ∈ Finset.range S.oracles.size, ∑ J ∈ Finset.range (2 ^ (L.k + L.logEll)),
        row.mainSum ρ S L x J * (mainWeight (K := K) S L o J * m o .main (mainBack S L o J))) +
      (∑ o ∈ Finset.range S.oracles.size, ∑ i ∈ Finset.range (tableSize S o .main),
        keptWeight (K := K) L o * ρ.val (row.coefficient o .main i) * ρ.val x *
          (keptWeight (K := K) L o * m o .main i)) +
      ∑ o ∈ Finset.range S.oracles.size, ∑ J ∈ Finset.range (2 ^ (L.h + L.logEllZk)),
        row.maskSum ρ S L x J * (maskWeight (K := K) S L o J * m o .mask (maskBack S L o J)) := by
    unfold value
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro o _
    rw [mul_add, ← main_part ρ F hr x m o, ← mask_part ρ F hr x m o]
  unfold groupValue
  rw [eA, eB, eC, eT]
  linear_combination -eV

/-- No coefficient is laid where the tables hold no word. -/
theorem lays_clean (F : LayFacts S G L) (hr : RowIn S G row) (x : E) (acc acc' : GroupRow)
    (hp : MaskReady L acc) (h : addToGroupRow S L row x acc = some acc')
    (hc : Clean ρ S L acc) : Clean ρ S L acc' := by
  refine ⟨fun J hJ => ?_, fun J hlt hJ => ?_, fun o ho i => ?_⟩
  · rw [addToGroupRow_main ρ S L F.mainOk row hr.fits x acc acc' h J, hc.main J hJ,
      Row.mainSum_none ρ S L x row J (mainWeight_off F hJ), add_zero]
  · rw [(addToGroupRow_mask ρ S L F.maskOk row hr.fits (hr.maskFits F) x acc acc' hp h J hlt).2,
      hc.mask J hlt hJ, Row.maskSum_none ρ S L x row J (maskWeight_off F hJ), add_zero]
  · rw [addToGroupRow_kept ρ S L row hr.fits x acc acc' h o i, hc.kept o ho i, keptWeight_off ho]
    simp

/-- **The law of the laying holds of addToGroupRow.** -/
theorem laysRight : LaysRight ρ addToGroupRow := by
  intro S g G L row x acc hG hL hOk hr hp
  have F := layFacts hG hL hOk
  obtain ⟨acc', h⟩ := addToGroupRow_total ρ F hr x acc hp
  exact ⟨acc', h, (addToGroupRow_mask ρ S L F.maskOk row hr.fits (hr.maskFits F) x acc acc' hp h 0
    (Nat.two_pow_pos _)).1, lays_clean ρ F hr x acc acc' hp h, lays_eq ρ F hr x acc acc' hp h⟩

/-- A group's row without coefficients has none where the tables hold no word. -/
theorem clean_start (S : Statement) (L : GroupLayout) (g : Nat) : Clean ρ S L { group := g } :=
  ⟨fun J _ => Form.entry_empty ρ J, fun J _ _ => by simp [ρ.zero], fun o _ i => by simp [keptSum]⟩

/-- A group's row without coefficients has the value 0. -/
theorem groupValue_start (S : Statement) (L : GroupLayout) (g : Nat) (T : Tables K) :
    groupValue ρ S L { group := g } T = 0 := by
  simp [groupValue, Form.entry_empty, keptSum, ρ.zero]

/-- **A row laid on a group's tables holds of them just if it holds of the words.** -/
theorem rowMeans : RowMeans ρ addToGroupRow := by
  intro S g G L row hG hL hOk hr
  obtain ⟨R, h, _, c, e⟩ := laysRight ρ S g G L row oneE { group := g } hG hL hOk hr (Or.inl rfl)
  refine ⟨R, h, c (clean_start ρ S L g), fun m => ?_⟩
  have e1 := e m
  rw [groupValue_start, ρ.one] at e1
  have e2 : ρ.val ({ group := g } : GroupRow).target = 0 := ρ.zero
  rw [e2] at e1
  unfold GroupSays Says
  constructor
  · intro c
    linear_combination c - e1
  · intro c
    linear_combination c + e1

end OnBytes.Means
