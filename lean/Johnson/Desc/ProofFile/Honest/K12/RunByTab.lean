-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByTab.lean: helper lemmas for the proofs of the statements in
RunBySpec.lean. The main one is `Tab.reads`: if `Tab s last P p` holds and h ≤ k, the two tables
made of p's lists of words (`tabOf`, Fmt/M1Own.lean) decode to the message `μOf (sgOf s) P`.

The other lemmas: on words below the prime (`eq_ofE`, `okE_subE`), on indices (`sg_k`,
`tab_idx_lt`), on lists made by `List.range` (`wr_congr`, `getD_range`, `lst_range`), and on the
sizes and entries of `tabOf`, in general and under `Tab`.

By what. By unfolding `tabOf`, `wr` and `Tab`.

Limits. Helper lemmas only.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunBySpec
import Fmt.M1CsEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes.Slice (GE ofE toE toE_inj toE_ofE vec lst vecIn)
open Johnson.Prover.Link (PS wr μOf okE_ofE lst_wr length_wr)
open Fmt.M1 (Stage)
open Fmt.M1.Own (PSt tabOf)
open H2K.Pub (sgOf)

theorem eq_ofE {a : Fmt.M1.E} {x : GE} (h : Fmt.Fld.two.okE a = true) (e : toE a = x) :
    a = ofE x :=
  toE_inj _ _ h (okE_ofE x) (e.trans (toE_ofE x).symm)

theorem okE_subE (a b : Fmt.M1.E) : Fmt.Fld.two.okE (Fmt.Fld.two.subE a b) = true :=
  (Fmt.M1.CsEq.okE_iff .two _).2
    ⟨Fmt.Fld.ok_sub .two _ _, Fmt.Fld.ok_sub .two _ _, Fmt.Fld.ok_sub .two _ _⟩

theorem sg_k {s : Stage} (h : s.h ≤ s.k) : (sgOf s).h + (sgOf s).g = s.k := by
  show s.h + (s.k - s.h) = s.k
  omega

/-- Entry c of row b has index b + nr * c, which is below nr * m, the table's size. -/
theorem tab_idx_lt (nr m b c : ℕ) (hb : b < nr) (hc : c < m) : b + nr * c < nr * m :=
  calc b + nr * c < nr + nr * c := Nat.add_lt_add_right hb _
    _ = nr * (c + 1) := by ring
    _ ≤ nr * m := Nat.mul_le_mul_left _ hc

theorem wr_congr (n : ℕ) (f g : ℕ → GE) (h : ∀ j, j < n → f j = g j) : wr n f = wr n g := by
  unfold wr
  exact List.map_congr_left fun j hj => by rw [h j (List.mem_range.1 hj)]

theorem getD_range {α : Type} (n : ℕ) (f : ℕ → α) (d : α) (i : ℕ) (h : i < n) :
    ((List.range n).map f).getD i d = f i := by
  rw [List.getD_eq_getElem _ _ (by rw [List.length_map, List.length_range]; exact h),
    List.getElem_map, List.getElem_range]

theorem lst_range (n : ℕ) (f : ℕ → Fmt.M1.E) (i : ℕ) (h : i < n) :
    lst ((List.range n).map f) i = toE (f i) := by
  unfold lst
  rw [getD_range n f _ i h]

theorem size_tabOf (rows : List (List Fmt.M1.E)) (n : ℕ) :
    (tabOf rows n).size = rows.length * n := Array.size_ofFn

theorem vec_tabOf (rows : List (List Fmt.M1.E)) (n i : ℕ) (h : i < rows.length * n) :
    vec (tabOf rows n) i = lst (rows.getD (i % rows.length) []) (i / rows.length) := by
  unfold vec Fmt.M1.ent tabOf
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos h]
  rfl

/-- Entry j of row b is at index b + rows.length * j of the table. -/
theorem vec_tabOf_at (rows : List (List Fmt.M1.E)) (n b j : ℕ) (hb : b < rows.length)
    (hj : j < n) :
    vec (tabOf rows n) (b + rows.length * j) = lst (rows.getD b []) j := by
  have hlt : b + rows.length * j < rows.length * n := tab_idx_lt _ _ _ _ hb hj
  rw [vec_tabOf rows n _ hlt, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb,
    Nat.add_mul_div_left _ _ (Nat.lt_of_le_of_lt (Nat.zero_le b) hb), Nat.div_eq_of_lt hb,
    Nat.zero_add]

section
variable {s : Stage} {last : Bool} {P : PS} {p : PSt}

theorem Tab.len_main (T : Tab s last P p) : p.M.length = 2 ^ s.k := by
  rw [T.main, List.length_map, List.length_range]

theorem Tab.len_mask (T : Tab s last P p) : p.W.length = 2 ^ s.h := by
  rw [T.mask, List.length_map, List.length_range]

theorem Tab.size_main (T : Tab s last P p) : (tabOf p.M s.C.l).size = 2 ^ s.k * s.C.l := by
  rw [size_tabOf, T.len_main]

theorem Tab.size_mask (T : Tab s last P p) : (tabOf p.W s.Z.l).size = 2 ^ s.h * s.Z.l := by
  rw [size_tabOf, T.len_mask]

theorem Tab.vec_main (T : Tab s last P p) (b j : ℕ) (hb : b < 2 ^ s.k) (hj : j < s.C.l) :
    vec (tabOf p.M s.C.l) (b + 2 ^ s.k * j) = P.tabM (b + 2 ^ s.k * j) := by
  have e := vec_tabOf_at p.M s.C.l b j (by rw [T.len_main]; exact hb) hj
  rw [T.len_main] at e
  rw [e, T.main, getD_range _ _ _ b hb, lst_wr _ _ _ hj]

theorem Tab.vec_mask (T : Tab s last P p) (b j : ℕ) (hb : b < 2 ^ s.h) (hj : j < s.Z.l) :
    vec (tabOf p.W s.Z.l) (b + 2 ^ s.h * j) = P.tabZ (b + 2 ^ s.h * j) := by
  have e := vec_tabOf_at p.W s.Z.l b j (by rw [T.len_mask]; exact hb) hj
  rw [T.len_mask] at e
  rw [e, T.mask, getD_range _ _ _ b hb, lst_wr _ _ _ hj]

theorem Tab.reads (T : Tab s last P p) (h : s.h ≤ s.k) (t : Fmt.M1.E) :
    vecIn (sgOf s) ⟨tabOf p.M s.C.l, tabOf p.W s.Z.l, t⟩ = μOf (sgOf s) P := by
  funext x
  rcases x with ⟨β, j⟩ | ⟨β, j⟩
  · show vec (tabOf p.M s.C.l) (OnBytes.Slice.Sz.rowNo β + 2 ^ ((sgOf s).h + (sgOf s).g) * j.val) =
      P.tabM (OnBytes.Slice.Sz.rowNo β + 2 ^ ((sgOf s).h + (sgOf s).g) * j.val)
    have hb := OnBytes.Slice.rowNo_lt β
    have hj : j.val < s.C.l := j.isLt
    generalize OnBytes.Slice.Sz.rowNo β = b at hb ⊢
    generalize j.val = c at hj ⊢
    rw [sg_k h] at hb ⊢
    exact T.vec_main _ _ hb hj
  · show vec (tabOf p.W s.Z.l) (OnBytes.Slice.Sz.rowNo β + 2 ^ s.h * j.val) =
      P.tabZ (OnBytes.Slice.Sz.rowNo β + 2 ^ s.h * j.val)
    exact T.vec_mask _ _ (OnBytes.Slice.rowNo_lt β) j.isLt

end

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.eq_ofE
#print axioms ProofFile.Honest.K12.Light.okE_subE
#print axioms ProofFile.Honest.K12.Light.sg_k
#print axioms ProofFile.Honest.K12.Light.tab_idx_lt
#print axioms ProofFile.Honest.K12.Light.wr_congr
#print axioms ProofFile.Honest.K12.Light.getD_range
#print axioms ProofFile.Honest.K12.Light.lst_range
#print axioms ProofFile.Honest.K12.Light.size_tabOf
#print axioms ProofFile.Honest.K12.Light.vec_tabOf
#print axioms ProofFile.Honest.K12.Light.vec_tabOf_at
#print axioms ProofFile.Honest.K12.Light.Tab.len_main
#print axioms ProofFile.Honest.K12.Light.Tab.len_mask
#print axioms ProofFile.Honest.K12.Light.Tab.size_main
#print axioms ProofFile.Honest.K12.Light.Tab.size_mask
#print axioms ProofFile.Honest.K12.Light.Tab.vec_main
#print axioms ProofFile.Honest.K12.Light.Tab.vec_mask
#print axioms ProofFile.Honest.K12.Light.Tab.reads
