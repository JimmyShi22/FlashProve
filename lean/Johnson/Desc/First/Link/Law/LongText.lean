-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/LongText.lean: WHAT THE TEXT LAYS AS THE CARRIED SINGLE ROWS' SYMBOLS AT
ONE POSITION (`rowsAt`, Johnson/Desc/Own/Symbols.lean), TAKEN APART AND READ IN THE FIELD. The
text's side of «the open word that the code switch reads is the fold of the members' words».
Theorems. No text already in the library turns.

  `layFrom_size`, `layRows_size`, `layMember_sizes`, `layMembers_sizes`: laying leaves the main and
    the mask table's sizes.
  `rowsAt_inv`: **a yes of rowsAt at two masks: there are the three tables t that the members'
    columns lay and the fresh mask's column, with: as many kept symbols as the rows count · the
    fresh mask's column has 2 ^ h symbols · what is laid is: the main table folded at gamma · the
    kept symbols · the mask table folded at gamma's first h · the fresh mask's column folded so.**
  `seg_main`, `seg_kept`, `seg_mask`, `seg_fresh`: its entries at 0 · 1 + j · maskRow 0 · maskRow 1.
  `main_field`, `mask_field`, `fresh_field`: **read in the field: entry 0 is ∑ b < 2 ^ k, eqW k
    (readL gamma) b * readV t.main b; the two masks' entries the like over 2 ^ h at gamma's first h
    coordinates** (by `readE_foldAll`, OnBytes/Slice/BlkCsSym.lean).
Limits. What stands IN the tables (which member's symbol at which row) is not said here. Nothing on
the typed fold. Nothing on soundness.
-/
import Johnson.Desc.Own.Symbols
import OnBytes.Slice.BlkCsSym

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Slice
open VerifiableInference.Desc.Own (Tables layFrom layRows layMember layMembers rowsAt)

/-! ## 1 Sizes -/

theorem layFrom_size : ∀ (es : List E) (table : Array E) (f : ℕ),
    (layFrom table f es).size = table.size
  | [], _, _ => rfl
  | e :: es, table, f => by
    show (layFrom (table.setIfInBounds f e) (f + 1) es).size = _
    rw [layFrom_size es, Array.size_setIfInBounds]

theorem layRows_size {table : Array E} {first : Option ℕ} {col t' : Array E}
    (h : layRows table first col = some t') : t'.size = table.size := by
  unfold layRows at h
  split at h
  · rw [← Option.some.inj h]
  · exact nomatch h
  · split at h
    · rw [← Option.some.inj h, layFrom_size]
    · exact nomatch h

theorem layMember_sizes {L : GroupLayout} {w : ℕ} {col : Column} {t t' : Tables}
    (h : layMember L w col t = some t') :
    t'.main.size = t.main.size ∧ t'.mask.size = t.mask.size := by
  unfold layMember at h
  obtain ⟨mask, hm, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · rw [← Option.some.inj h]
    exact ⟨rfl, layRows_size hm⟩
  · obtain ⟨main, hn, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨layRows_size hn, layRows_size hm⟩

theorem layMembers_sizes (L : GroupLayout) (opened : Array (Array Column)) (i : ℕ) :
    ∀ (ws : List ℕ) (t t' : Tables), layMembers L opened i ws t = some t' →
      t'.main.size = t.main.size ∧ t'.mask.size = t.mask.size
  | [], t, t', h => by
    rw [← Option.some.inj h]
    exact ⟨rfl, rfl⟩
  | w :: ws, t, t', h => by
    unfold layMembers at h
    obtain ⟨col, _, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨t₁, h1, h⟩ := Option.bind_eq_some_iff.1 h
    obtain ⟨a, b⟩ := layMembers_sizes L opened i ws t₁ t' h
    obtain ⟨c, d⟩ := layMember_sizes h1
    exact ⟨a.trans c, b.trans d⟩

/-! ## 2 The text taken apart -/

/-- The tables in front of the laying. -/
def blankTables (L : GroupLayout) : Tables :=
  ⟨Array.replicate (2 ^ L.k) zeroE, Array.replicate (2 ^ L.h) zeroE, #[]⟩

/-- **A YES OF rowsAt AT TWO MASKS.** -/
theorem rowsAt_inv {s : SingleRows} (hm : s.masks = 2) {opened : Array (Array Column)} {i : ℕ}
    {seg : Array E} (h : rowsAt s opened #[] i = some seg) :
    ∃ (t : Tables) (fresh : Column),
      layMembers s.layout opened i (List.range s.layout.members.size) (blankTables s.layout) =
        some t ∧
      t.main.size = 2 ^ s.layout.k ∧ t.mask.size = 2 ^ s.layout.h ∧ t.kept.size = s.keptRows ∧
      ((opened[s.layout.members.size]?).bind (·[i]?)) = some fresh ∧
      fresh.mask.size = 2 ^ s.layout.h ∧
      seg = (((#[] : Array E).push ((foldLow t.main s.gamma).getD 0 zeroE) ++ t.kept).push
        ((foldLow t.mask (s.gamma.take s.layout.h)).getD 0 zeroE)).push
          ((foldLow fresh.mask (s.gamma.take s.layout.h)).getD 0 zeroE) := by
  unfold rowsAt at h
  dsimp only at h
  obtain ⟨t, ht, h⟩ := Option.bind_eq_some_iff.1 h
  obtain ⟨z1, z2⟩ := layMembers_sizes _ _ _ _ _ _ ht
  by_cases hk : t.kept.size = s.keptRows
  · have hk' : (t.kept.size != s.keptRows) = false := by simp [hk]
    rw [hk', hm] at h
    simp only [Bool.false_eq_true, if_false, beq_self_eq_true, if_true,
      show (1 : ℕ) ≤ 2 from by omega] at h
    obtain ⟨fresh, hf, h⟩ := Option.bind_eq_some_iff.1 h
    by_cases hz : fresh.mask.size = 2 ^ s.layout.h
    · have hz' : (fresh.mask.size != 2 ^ s.layout.h) = false := by simp [hz]
      rw [hz'] at h
      simp only [Bool.false_eq_true, if_false] at h
      exact ⟨t, fresh, ht, by rw [z1, Array.size_replicate], by rw [z2, Array.size_replicate], hk,
        hf, hz, (Option.some.inj h).symm⟩
    · have hz' : (fresh.mask.size != 2 ^ s.layout.h) = true := by simp [hz]
      rw [hz'] at h
      exact nomatch h
  · have hk' : (t.kept.size != s.keptRows) = true := by simp [hk]
    rw [hk'] at h
    exact nomatch h

/-! ## 3 The entries -/

section
variable (m : E) (K : Array E) (z f : E)

theorem seg_main : ((((#[] : Array E).push m ++ K).push z).push f).getD 0 zeroE = m := by
  simp [Array.getD_eq_getD_getElem?]

theorem seg_kept {j : ℕ} (hj : j < K.size) :
    ((((#[] : Array E).push m ++ K).push z).push f).getD (1 + j) zeroE = K.getD j zeroE := by
  have e : ((((#[] : Array E).push m ++ K).push z).push f) =
      (m :: (K.toList ++ [z, f])).toArray := by
    apply Array.toList_inj.1
    simp
  rw [e, Array.getD_eq_getD_getElem?, List.getElem?_toArray, Nat.add_comm 1 j,
    List.getElem?_cons_succ, List.getElem?_append_left (by simpa using hj),
    Array.getD_eq_getD_getElem?, Array.getElem?_toList]

theorem seg_mask :
    ((((#[] : Array E).push m ++ K).push z).push f).getD (1 + K.size + 0) zeroE = z := by
  have e : ((((#[] : Array E).push m ++ K).push z).push f) =
      (m :: (K.toList ++ [z, f])).toArray := by
    apply Array.toList_inj.1
    simp
  rw [e, Array.getD_eq_getD_getElem?, List.getElem?_toArray, Nat.add_zero, Nat.add_comm 1 K.size,
    List.getElem?_cons_succ, List.getElem?_append_right (by simp)]
  simp

theorem seg_fresh :
    ((((#[] : Array E).push m ++ K).push z).push f).getD (1 + K.size + 1) zeroE = f := by
  have e : ((((#[] : Array E).push m ++ K).push z).push f) =
      (m :: (K.toList ++ [z, f])).toArray := by
    apply Array.toList_inj.1
    simp
  rw [e, Array.getD_eq_getD_getElem?, List.getElem?_toArray,
    show 1 + K.size + 1 = (K.size + 1) + 1 by omega, List.getElem?_cons_succ,
    List.getElem?_append_right (by simp)]
  simp

end

/-! ## 4 In the field -/

theorem main_field {T : Array E} {g : List E} {k : ℕ} (hg : g.length = k) (hT : T.size = 2 ^ k) :
    readE ((foldLow T g).getD 0 zeroE) =
      ∑ b ∈ Finset.range (2 ^ k), eqW k (readL g) b * readV T b := by
  subst hg
  exact readE_foldAll g T hT

theorem mask_field {T : Array E} {g : List E} {h : ℕ} (hg : h ≤ g.length) (hT : T.size = 2 ^ h) :
    readE ((foldLow T (g.take h)).getD 0 zeroE) =
      ∑ b ∈ Finset.range (2 ^ h), eqW h (readL (g.take h)) b * readV T b :=
  main_field (by rw [List.length_take]; omega) hT

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.layMembers_sizes
#print axioms VerifiableInference.Desc.LinkJoin.rowsAt_inv
#print axioms VerifiableInference.Desc.LinkJoin.seg_main
#print axioms VerifiableInference.Desc.LinkJoin.seg_kept
#print axioms VerifiableInference.Desc.LinkJoin.seg_mask
#print axioms VerifiableInference.Desc.LinkJoin.seg_fresh
#print axioms VerifiableInference.Desc.LinkJoin.main_field
#print axioms VerifiableInference.Desc.LinkJoin.mask_field
