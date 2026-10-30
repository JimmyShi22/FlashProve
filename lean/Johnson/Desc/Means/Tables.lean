-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Tables.lean: the group's tables as the words fill them are what the carrying of
indices says.

tablesOf is written with weights. Laid says the same with groupIndex, the function that the program
carries an index with: each entry of a member stands where groupIndex puts it, and an index whose
row is in no member's block holds 0. This file shows that tablesOf meets Laid, that tables which
meet Laid agree with it wherever a group's row reads them (tablesRight), and the law of the laying
for all tables that meet Laid (rowMeans_laid).

Main theorems: tablesOf_main_at, tablesOf_main_else, tablesOf_mask_at, tablesOf_mask_else,
tablesOf_kept_at, tablesOf_kept_else, tablesOf_laid, laid_main, laid_mask, laid_kept, tablesRight,
groupValue_laid, rowMeans_laid.

What is not claimed. Nothing on how the tables are tied to code words or to what a prover has sent.

-/
import Johnson.Desc.Means.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K]
variable {S : Statement} {G : Group} {L : GroupLayout}

/-- An oracle message that has a table is there. -/
theorem lt_of_has {o : Nat} {part : Part} (h : S.has o part = true) : o < S.oracles.size := by
  by_contra c
  unfold Statement.has at h
  rw [Array.getElem?_eq_none (Nat.le_of_not_lt c)] at h
  cases h

/-- Where an index goes, its row is in the block. -/
theorem groupIndex_in (idx a first k : Nat) (hb : BlockOk a first k) :
    first ≤ groupIndex idx a first k % 2 ^ k ∧
      groupIndex idx a first k % 2 ^ k < first + 2 ^ a := by
  rw [groupIndex_row idx a first k hb]
  have := Nat.mod_lt idx (Nat.two_pow_pos a)
  omega

/-- An index whose row is in the block is where its own index in the member's table goes. -/
theorem groupIndex_unshift (J a first k : Nat) (hb : BlockOk a first k)
    (hJ : first ≤ J % 2 ^ k ∧ J % 2 ^ k < first + 2 ^ a) :
    groupIndex (unshift a (k - a) J) a first k = J := by
  rw [groupIndex_eq_shiftIn _ _ _ _ hb]
  exact (shiftIn_eq_iff _ _ _ _ _).2 ⟨(inBlock_iff J a first k hb).2 hJ, rfl⟩

theorem LayFacts.mainSize (F : LayFacts S G L) {o i first : Nat} (hf : L.find o = some i)
    (hm : L.mainFirst.getD i none = some first) :
    tableSize S o .main = 2 ^ (S.rowBits o .main + L.logEll) := by
  have hh := (F.main_block o i first hf hm).1
  unfold tableSize Statement.tableBits
  rw [if_pos hh, F.main_places o (F.mem_of_find o i hf) hh]

theorem LayFacts.maskSize (F : LayFacts S G L) {o i first : Nat} (hf : L.find o = some i)
    (hm : L.maskFirst.getD i none = some first) :
    tableSize S o .mask = 2 ^ (S.rowBits o .mask + L.logEllZk) := by
  have hh := (F.mask_block o i first hf hm).1
  unfold tableSize Statement.tableBits
  rw [if_pos hh, F.mask_places o (F.mem_of_find o i hf) hh]

/-- In the main table each entry of a member stands where groupIndex puts it. -/
theorem tablesOf_main_at (F : LayFacts S G L) (m : Words K) {o i first : Nat}
    (hf : L.find o = some i) (hm : L.mainFirst.getD i none = some first) (idx : Nat) :
    (tablesOf S L m).main (groupIndex idx (S.rowBits o .main) first L.k) = m o .main idx := by
  obtain ⟨hh, hk, hb⟩ := F.main_block o i first hf hm
  have hin := groupIndex_in idx _ first L.k hb
  show (∑ o' ∈ Finset.range S.oracles.size,
    mainWeight (K := K) S L o' (groupIndex idx (S.rowBits o .main) first L.k) *
      m o' .main (mainBack S L o' (groupIndex idx (S.rowBits o .main) first L.k))) = _
  rw [Finset.sum_eq_single o]
  · rw [mainWeight_rows S L o i first _ hf hk hm hb, if_pos hin, one_mul]
    congr 1
    exact unshift_groupIndex idx _ first L.k hb
  · intro o' _ hne
    rw [mainWeight_other F hne hf hm hin, zero_mul]
  · intro hno
    exact absurd (Finset.mem_range.2 (lt_of_has hh)) hno

/-- In the mask table each entry of a member stands where groupIndex puts it. -/
theorem tablesOf_mask_at (F : LayFacts S G L) (m : Words K) {o i first : Nat}
    (hf : L.find o = some i) (hm : L.maskFirst.getD i none = some first) (idx : Nat) :
    (tablesOf S L m).mask (groupIndex idx (S.rowBits o .mask) first L.h) = m o .mask idx := by
  obtain ⟨hh, hb⟩ := F.mask_block o i first hf hm
  have hin := groupIndex_in idx _ first L.h hb
  show (∑ o' ∈ Finset.range S.oracles.size,
    maskWeight (K := K) S L o' (groupIndex idx (S.rowBits o .mask) first L.h) *
      m o' .mask (maskBack S L o' (groupIndex idx (S.rowBits o .mask) first L.h))) = _
  rw [Finset.sum_eq_single o]
  · rw [maskWeight_rows S L o i first _ hf hm hb, if_pos hin, one_mul]
    congr 1
    exact unshift_groupIndex idx _ first L.h hb
  · intro o' _ hne
    rw [maskWeight_other F hne hf hm hin, zero_mul]
  · intro hno
    exact absurd (Finset.mem_range.2 (lt_of_has hh)) hno

/-- An index of the main table whose row is in no member's block holds 0. -/
theorem tablesOf_main_else (F : LayFacts S G L) (m : Words K) (J : Nat) (h : OffMain S L J) :
    (tablesOf S L m).main J = 0 := by
  show (∑ o ∈ Finset.range S.oracles.size,
    mainWeight (K := K) S L o J * m o .main (mainBack S L o J)) = 0
  apply Finset.sum_eq_zero
  intro o _
  rw [mainWeight_off F h o, zero_mul]

/-- An index of the mask table whose row is in no member's block holds 0. -/
theorem tablesOf_mask_else (F : LayFacts S G L) (m : Words K) (J : Nat) (h : OffMask S L J) :
    (tablesOf S L m).mask J = 0 := by
  show (∑ o ∈ Finset.range S.oracles.size,
    maskWeight (K := K) S L o J * m o .mask (maskBack S L o J)) = 0
  apply Finset.sum_eq_zero
  intro o _
  rw [maskWeight_off F h o, zero_mul]

/-- The kept part has a kept member's main table. -/
theorem tablesOf_kept_at (m : Words K) {o : Nat} (h : KeptAt L o) (idx : Nat) :
    (tablesOf S L m).kept o idx = m o .main idx := by
  show keptWeight (K := K) L o * m o .main idx = _
  rw [keptWeight_at h, one_mul]

/-- The kept part is 0 at what is no kept member. -/
theorem tablesOf_kept_else (m : Words K) {o : Nat} (h : ¬ KeptAt L o) (idx : Nat) :
    (tablesOf S L m).kept o idx = 0 := by
  show keptWeight (K := K) L o * m o .main idx = _
  rw [keptWeight_off h, zero_mul]

/-- tablesOf holds the words as the layout lays them. -/
theorem tablesOf_laid (F : LayFacts S G L) (m : Words K) : Laid S L m (tablesOf S L m) :=
  ⟨fun _ _ _ hf _ hm idx _ => tablesOf_main_at F m hf hm idx,
    fun J _ h => tablesOf_main_else F m J h,
    fun _ _ _ hf hm idx _ => tablesOf_mask_at F m hf hm idx,
    fun J _ h => tablesOf_mask_else F m J h,
    fun _ i hf hk idx _ => tablesOf_kept_at m ⟨i, hf, hk⟩ idx,
    fun _ h idx => tablesOf_kept_else m h idx⟩

/-- Tables that hold the words as the layout lays them have tablesOf's main table. -/
theorem laid_main (F : LayFacts S G L) (m : Words K) (T : Tables K) (hT : Laid S L m T) (J : Nat)
    (hJ : J < 2 ^ (L.k + L.logEll)) : T.main J = (tablesOf S L m).main J := by
  by_cases hex : ∃ o i first, L.find o = some i ∧ L.kept.getD i false = false ∧
      L.mainFirst.getD i none = some first ∧ InBlock J (S.rowBits o .main) first L.k
  · obtain ⟨o, i, first, hf, hk, hm, hin⟩ := hex
    have hb := (F.main_block o i first hf hm).2.2
    have e := groupIndex_unshift J _ first L.k hb hin
    have hlt : unshift (S.rowBits o .main) (L.k - S.rowBits o .main) J < tableSize S o .main := by
      rw [F.mainSize hf hm]
      exact unshift_lt J _ first L.k L.logEll hb hJ
    rw [← e, hT.main_at o i first hf hk hm _ hlt, tablesOf_main_at F m hf hm]
  · have h : OffMain S L J := fun o i first hf hk hm hin => hex ⟨o, i, first, hf, hk, hm, hin⟩
    rw [hT.main_else J hJ h, tablesOf_main_else F m J h]

/-- Tables that hold the words as the layout lays them have tablesOf's mask table. -/
theorem laid_mask (F : LayFacts S G L) (m : Words K) (T : Tables K) (hT : Laid S L m T) (J : Nat)
    (hJ : J < 2 ^ (L.h + L.logEllZk)) : T.mask J = (tablesOf S L m).mask J := by
  by_cases hex : ∃ o i first, L.find o = some i ∧
      L.maskFirst.getD i none = some first ∧ InBlock J (S.rowBits o .mask) first L.h
  · obtain ⟨o, i, first, hf, hm, hin⟩ := hex
    have hb := (F.mask_block o i first hf hm).2
    have e := groupIndex_unshift J _ first L.h hb hin
    have hlt : unshift (S.rowBits o .mask) (L.h - S.rowBits o .mask) J < tableSize S o .mask := by
      rw [F.maskSize hf hm]
      exact unshift_lt J _ first L.h L.logEllZk hb hJ
    rw [← e, hT.mask_at o i first hf hm _ hlt, tablesOf_mask_at F m hf hm]
  · have h : OffMask S L J := fun o i first hf hm hin => hex ⟨o, i, first, hf, hm, hin⟩
    rw [hT.mask_else J hJ h, tablesOf_mask_else F m J h]

/-- Tables that hold the words as the layout lays them have tablesOf's kept part. -/
theorem laid_kept (m : Words K) (T : Tables K) (hT : Laid S L m T) (o i : Nat)
    (hi : i < tableSize S o .main) : T.kept o i = (tablesOf S L m).kept o i := by
  by_cases h : KeptAt L o
  · obtain ⟨j, hf, hk⟩ := h
    rw [hT.kept_at o j hf hk i hi, tablesOf_kept_at m ⟨j, hf, hk⟩]
  · rw [hT.kept_else o h, tablesOf_kept_else m h]

/-- **The tables are the laid words, and nothing else is.** -/
theorem tablesRight : TablesRight K := by
  intro S g G L m hG hL hOk
  have F := layFacts hG hL hOk
  exact ⟨tablesOf_laid F m,
    fun T hT => ⟨laid_main F m T hT, laid_mask F m T hT, laid_kept m T hT⟩⟩

variable (ρ : Reading K)

/-- A group's row has the same value on all tables that hold the words as the layout lays them. -/
theorem groupValue_laid (F : LayFacts S G L) (R : GroupRow) (m : Words K) (T : Tables K)
    (hT : Laid S L m T) : groupValue ρ S L R T = groupValue ρ S L R (tablesOf S L m) := by
  unfold groupValue
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intro J hJ
      rw [laid_main F m T hT J (Finset.mem_range.1 hJ)]
    · apply Finset.sum_congr rfl
      intro J hJ
      rw [laid_mask F m T hT J (Finset.mem_range.1 hJ)]
  · apply Finset.sum_congr rfl
    intro o _
    apply Finset.sum_congr rfl
    intro i hi
    rw [laid_kept m T hT o i (Finset.mem_range.1 hi)]

/-- **A row laid on a group's tables holds of them just if it holds of the words**, for all tables
that hold the words as the layout lays them. -/
theorem rowMeans_laid (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (row : Row)
    (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : RowIn S G row) :
    ∃ R, addToGroupRow S L row oneE { group := g } = some R ∧ Clean ρ S L R ∧
      ∀ (m : Words K) (T : Tables K), Laid S L m T → (GroupSays ρ S L R T ↔ Says ρ S row m) := by
  have F := layFacts hG hL hOk
  obtain ⟨R, h, c, e⟩ := rowMeans ρ S g G L row hG hL hOk hr
  refine ⟨R, h, c, fun m T hT => ?_⟩
  rw [← e m]
  unfold GroupSays
  rw [groupValue_laid ρ F R m T hT]

end OnBytes.Means
