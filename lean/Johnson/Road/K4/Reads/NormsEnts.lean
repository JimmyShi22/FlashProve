-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Reads/NormsEnts.lean: the claims of the norms, of the norms' rows and of the
selectors name entries inside the families of tables alone. Statements and proofs.

MADE BY PROGRAM out of Johnson/Road/Rows/NormsRowsIn.lean (the same walk for the array
alone): `RowsIn` became `EntsIn`, the predicate «the array of reads» became `inTab v`
(Johnson/Road/K4/Reads/TermsEnts.lean). No proof is new.

Main names: `entsIn_normsL`, `entsIn_rowBatch`, `entsIn_ledgerL`, `entsIn_oneHotL`. Two of them take
as a premise that a sumcheck's own claim names such entries alone.
-/
import Johnson.Road.K4.Reads.TermsEnts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Reads

open OnBytes.Model
open OnBytes.Model.Layer (Env Heard Pub sumForms aff0)
open OnBytes.Road OnBytes.Road.Rows

variable {Q : ℕ → ℕ → ℕ → Prop}

/-! ### The row of a norm -/

theorem entsIn_c (k : E) : EntsIn Q (LedK.c k : Aff) := entsIn_ofConst k

theorem entsIn_kadd {a b : Aff} (ha : EntsIn Q a) (hb : EntsIn Q b) :
    EntsIn Q (LedK.add a b) := entsIn_add ha hb

theorem entsIn_ksub {a b : Aff} (ha : EntsIn Q a) (hb : EntsIn Q b) :
    EntsIn Q (LedK.sub a b) := entsIn_sub ha hb

theorem entsIn_kmul {a : Aff} (k : E) (ha : EntsIn Q a) : EntsIn Q (LedK.mul a k) :=
  entsIn_scale k ha

/-- A member of an array that is given by a function. -/
theorem entsIn_ofFn {n : ℕ} (f : Fin n → Aff) (hf : ∀ i, EntsIn Q (f i)) {d : Aff}
    (hd : EntsIn Q d) (j : ℕ) : EntsIn Q ((Array.ofFn f).getD j d) := by
  by_cases hj : j < n
  · have e : (Array.ofFn f).getD j d = f ⟨j, hj⟩ := by simp [Array.getD, hj]
    rw [e]
    exact hf _
  · have e : (Array.ofFn f).getD j d = d := by simp [Array.getD, hj]
    rw [e]
    exact hd

/-- A number in digits. -/
theorem entsIn_ledDig {Dg : Array Aff} (h : ∀ j, EntsIn Q (Dg.getD j (LedK.c zeroE)))
    (first n : ℕ) : EntsIn Q (ledDig Dg first n) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_kadd hf (entsIn_kmul _ (h _))) _ _ (entsIn_c _)

/-- All forms of a row that the claims read. -/
structure Row5In (Q : ℕ → ℕ → ℕ → Prop) (r : Row5 Aff) : Prop where
  Dg : ∀ j, EntsIn Q (r.Dg.getD j (LedK.c zeroE))
  c : ∀ j, EntsIn Q (r.c.getD j (LedK.c zeroE))
  Vlo : EntsIn Q r.Vlo
  Vhi : EntsIn Q r.Vhi
  a : EntsIn Q r.a
  b : EntsIn Q r.b
  sig : EntsIn Q r.sig
  s0 : EntsIn Q r.s0
  l1 : EntsIn Q r.l1
  h1 : EntsIn Q r.h1
  Blo : EntsIn Q r.Blo
  Bhi : EntsIn Q r.Bhi
  kap : EntsIn Q r.kap
  Rlo : EntsIn Q r.Rlo
  Rhi : EntsIn Q r.Rhi
  q1 : EntsIn Q r.q1
  rr : EntsIn Q r.rr
  rq : EntsIn Q r.rq

/-- The digits of the row that is made from cells. -/
theorem row5_dg {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) (j : ℕ) :
    EntsIn Q ((Array.ofFn (n := 99) fun j : Fin 99 =>
      (LedK.add (cell j.val) (LedK.c (ofNat 128)) : Aff)).getD j (LedK.c zeroE)) :=
  entsIn_ofFn _ (fun _ => entsIn_kadd (h _) (entsIn_c _)) (entsIn_c _) j

theorem row5_Dg {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) (j : ℕ) :
    EntsIn Q ((row5 cell).Dg.getD j (LedK.c zeroE)) := row5_dg h j

theorem row5_c {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) (j : ℕ) :
    EntsIn Q ((row5 cell).c.getD j (LedK.c zeroE)) :=
  entsIn_ofFn _ (fun s => by
    dsimp only
    split_ifs
    · exact entsIn_c _
    · exact row5_dg h 9
    · exact entsIn_ksub (entsIn_ledDig (row5_dg h) _ _) (entsIn_c _)) (entsIn_c _) j

theorem row5_Vlo {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).Vlo :=
  entsIn_ledDig (row5_dg h) 0 6

theorem row5_Vhi {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).Vhi :=
  entsIn_ledDig (row5_dg h) 6 4

theorem row5_a {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).a :=
  entsIn_kadd (entsIn_kadd (entsIn_kadd (entsIn_kmul _ (row5_dg h 58)) (row5_dg h 59))
    (entsIn_kmul _ (row5_dg h 60))) (entsIn_kmul _ (row5_dg h 61))

theorem row5_b {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).b :=
  entsIn_kadd (row5_dg h 62) (entsIn_kmul _ (row5_dg h 63))

theorem row5_sig {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).sig :=
  entsIn_kadd (row5_a h) (entsIn_kmul _ (row5_b h))

theorem row5_s0 {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).s0 := by
  unfold row5
  dsimp only
  exact row5_dg h 59

theorem row5_l1 {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).l1 :=
  entsIn_ledDig (row5_dg h) 64 5

theorem row5_h1 {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).h1 :=
  entsIn_ledDig (row5_dg h) 69 5

theorem row5_Blo {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).Blo :=
  entsIn_ledDig (row5_dg h) 74 3

theorem row5_Bhi {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).Bhi :=
  entsIn_ledDig (row5_dg h) 77 2

theorem row5_kap {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).kap :=
  entsIn_ksub (row5_dg h 79) (entsIn_c _)

theorem row5_Rlo {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).Rlo :=
  entsIn_ledDig (row5_dg h) 80 3

theorem row5_Rhi {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).Rhi :=
  entsIn_ledDig (row5_dg h) 83 3

theorem row5_q1 {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).q1 :=
  entsIn_ledDig (row5_dg h) 86 3

theorem row5_rr {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).rr :=
  entsIn_ledDig (row5_dg h) 89 5

theorem row5_rq {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : EntsIn Q (row5 cell).rq :=
  entsIn_ledDig (row5_dg h) 94 5

/-- The row that is made from cells. -/
theorem row5In_row5 {cell : ℕ → Aff} (h : ∀ j, EntsIn Q (cell j)) : Row5In Q (row5 cell) :=
  ⟨row5_Dg h, row5_c h, row5_Vlo h, row5_Vhi h, row5_a h, row5_b h, row5_sig h, row5_s0 h,
    row5_l1 h, row5_h1 h, row5_Blo h, row5_Bhi h, row5_kap h, row5_Rlo h, row5_Rhi h, row5_q1 h,
    row5_rr h, row5_rq h⟩

/-- The row that the verifier makes at a token point. -/
theorem row5In_row5At {v : Env} {P : String} {i : ℕ} {r : Row5 Aff} (h : v.row5At P i = some r) :
    Row5In (inTab v) r := by
  unfold Env.row5At at h
  obtain ⟨cells, hc, e⟩ := bind_some h
  obtain rfl : row5 (fun j => cells.getD j aff0) = r := Option.some.inj e
  exact row5In_row5 fun j => inTab_rowCells hc j

/-- A line of the carries. -/
theorem entsIn_ledCarry5 {r : Row5 Aff} (R : Row5In Q r) (s : ℕ) {w : Aff} (hw : EntsIn Q w) :
    EntsIn Q (ledCarry5 r s w) := by
  unfold ledCarry5
  dsimp only
  split_ifs
  · exact entsIn_c _
  · exact entsIn_ksub (entsIn_ksub (entsIn_kadd hw (R.c s)) (R.Dg s)) (entsIn_kmul _ (R.c (s + 1)))

/-- The eight lines. -/
theorem entsIn_ledLines5 {r : Row5 Aff} (R : Row5In Q r) {Pp : Array Aff}
    (hP : ∀ i, EntsIn Q (Pp.getD i (LedK.c zeroE))) (eps : E) {two : Aff} (h2 : EntsIn Q two) :
    ∀ a ∈ (ledLines5 r Pp eps two).toList, EntsIn Q a := by
  intro a ha
  unfold ledLines5 at ha
  dsimp only at ha
  split_ifs at ha
  · rw [Array.toList_replicate] at ha
    rw [(List.mem_replicate.mp ha).2]
    exact entsIn_c _
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact entsIn_ksub (entsIn_ksub (hP 1) R.Blo) (entsIn_kmul _ R.Bhi)
    · exact entsIn_kadd (entsIn_ksub (entsIn_ksub (entsIn_ksub (entsIn_kadd R.Vlo (entsIn_c _))
        (hP 0)) (entsIn_kmul _ R.Blo)) R.l1) (entsIn_kmul _ R.kap)
    · exact entsIn_ksub (entsIn_ksub (entsIn_ksub R.Vhi R.Bhi) (hP 2)) R.kap
    · exact entsIn_ksub (entsIn_kadd R.l1 R.h1) (entsIn_kmul _ R.sig)
    · exact entsIn_ksub (entsIn_kadd (hP 4) (hP 5)) R.q1
    · exact hP 6
    · exact entsIn_ksub (entsIn_ksub (entsIn_ksub (entsIn_ksub (entsIn_kadd h2 R.sig) R.s0)
        (entsIn_kmul _ (hP 3))) (entsIn_kmul _ R.q1)) (entsIn_kmul _ R.rr)
    · exact entsIn_kadd (entsIn_ksub (entsIn_kadd R.rr R.rq) R.sig) (entsIn_c _)

/-! ### The lists -/

/-- A member of lists laid end to end is a member of one of them. -/
theorem mem_flat_inv {α : Type} {l : α → Option (List Aff)} :
    ∀ {xs : List α} {L : List (List Aff)}, xs.mapM l = some L → ∀ {y : Aff}, y ∈ L.flatten →
      ∃ a ∈ xs, ∃ x, l a = some x ∧ y ∈ x
  | [], L, h, y, hy => by
    have e : L = [] := by simpa using h.symm
    rw [e] at hy
    cases hy
  | b :: xs, L, h, y, hy => by
    obtain ⟨z, zs, hz, hzs, e⟩ := mapM_cons_some h
    subst e
    rw [List.flatten_cons] at hy
    rcases List.mem_append.mp hy with hy | hy
    · exact ⟨b, List.mem_cons_self, z, hz, hy⟩
    · obtain ⟨a, ha, x, hx, hyx⟩ := mem_flat_inv hzs hy
      exact ⟨a, List.mem_cons_of_mem _ ha, x, hx, hyx⟩

/-- The three claims behind the sums of squares. -/
theorem entsIn_normsL {P : Pub} {v : Env} {H : Heard} {l : List Aff}
    (h : normsL P v H = some l) (hrow : InTab v H.wpl.row) :
    ∀ f ∈ l, InTab v f := by
  obtain ⟨x1, l2, e1, h2, rfl⟩ := appL_some h
  obtain ⟨x2, l3, e2, h3, rfl⟩ := appL_some h2
  cases e1
  cases e2
  obtain ⟨txs, -, h3⟩ := bind_some h3
  obtain ⟨tI, -, h3⟩ := bind_some h3
  obtain ⟨tA, -, h3⟩ := bind_some h3
  obtain ⟨e, -, h3⟩ := bind_some h3
  obtain ⟨sum, hsum, h3⟩ := bind_some h3
  cases h3
  have hs : InTab v sum := inTab_sumForms (fun x p hx => by
    obtain ⟨c, hc, e'⟩ := map_some hx
    subst e'
    split at hc
    · exact inTab_U3at hc
    · exact inTab_U3at hc) hsum
  intro f hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact hrow
  · exact entsIn_sub (entsIn_slot _) (entsIn_slot _)
  · exact entsIn_add (entsIn_slot _) hs

/-- The batch of the row products names no entry. -/
theorem entsIn_rowBatch (y : Model.Layer.Lay) (H : Heard) : EntsIn Q (rowBatchForm y H) :=
  entsIn_foldl _ (fun _ _ hf => entsIn_addMul _ hf (entsIn_slot _)) _ _ (entsIn_slot _)

/-- The norms' rows. -/
theorem entsIn_ledgerL {v : Env} {H : Heard} {sh : Array E} {l : List Aff}
    (h : ledgerL v H sh = some l)
    (hrow : InTab v (H.tV.p.rowForm (ledS0 v H sh) {})) :
    ∀ f ∈ l, InTab v f := by
  obtain ⟨lA, lC, lD, rP, hA, hrP, hC, hD, rfl⟩ := ledgerL_parts h
  have hR : ∀ x ∈ rP.toList.zipIdx, Row5In (inTab v) x.1 := by
    intro x hx
    have hx1 : x.1 ∈ rP.toList := List.fst_mem_of_mem_zipIdx hx
    have hrP' := hrP
    rw [Array.mapM_eq_mapM_toList] at hrP'
    obtain ⟨ys, hys, e⟩ := map_some hrP'
    subst e
    exact all_mapM (Pr := Row5In (inTab v))
      (fun _ _ hb => row5In_row5At hb) _ ys hys _ hx1
  intro f hf
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | hf | hf | hf
  · exact hrow
  · obtain ⟨L, hL, e⟩ := map_some hA
    subst e
    obtain ⟨i, -, x, hx, hfx⟩ := mem_flat_inv hL hf
    unfold shownL at hx
    obtain ⟨r, hr, hx⟩ := bind_some hx
    have R := row5In_row5At hr
    obtain ⟨L2, hL2, e⟩ := map_some hx
    subst e
    obtain ⟨q, hq, x2, hx2, hfx2⟩ := mem_flat_inv hL2 hfx
    cases hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfx2
    subst hfx2
    refine entsIn_sub (entsIn_slot _) ?_
    simp only [List.zipIdx_cons, List.zipIdx_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact R.a
    · exact R.b
    · exact R.Rlo
    · exact R.Rhi
  · obtain ⟨L, hL, e⟩ := map_some hC
    subst e
    obtain ⟨x, hxm, y, hy, hfy⟩ := mem_flat_inv hL hf
    unfold carryL at hy
    obtain ⟨L2, hL2, e⟩ := map_some hy
    subst e
    obtain ⟨s, -, x2, hx2, hfx2⟩ := mem_flat_inv hL2 hfy
    cases hx2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfx2
    subst hfx2
    exact entsIn_ledCarry5 (hR x hxm) s (entsIn_slot _)
  · obtain ⟨L, hL, e⟩ := map_some hD
    subst e
    obtain ⟨x, hxm, y, hy, hfy⟩ := mem_flat_inv hL hf
    unfold linesL at hy
    cases hy
    refine entsIn_ledLines5 (hR x hxm) (fun i => ?_) _ (entsIn_ofConst _) f hfy
    by_cases hi : i < 7
    · rw [range_map_getD' 7 _ _ hi]
      exact entsIn_slot _
    · have e : ((Array.range 7).map fun j => Aff.slot (H.sPv + 7 * x.2 + j)).getD i
          (LedK.c zeroE) = LedK.c zeroE := by simp [Array.getD, hi]
      rw [e]
      exact entsIn_c _

/-- The selectors' sums. -/
theorem entsIn_oneHotL {v : Env} {l : List Aff} (h : oneHotL v = some l) :
    ∀ f ∈ l, InTab v f := by
  unfold oneHotL at h
  split at h
  · obtain ⟨L, hL, e⟩ := map_some h
    subst e
    intro f hf
    obtain ⟨lm, -, x, hx, hfx⟩ := mem_flat_inv hL hf
    obtain ⟨s, hs, hx⟩ := bind_some hx
    cases hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfx
    subst hfx
    refine entsIn_add (entsIn_ofConst _) (inTab_sumForms (fun x p hx => ?_) hs)
    obtain ⟨c, hc, e'⟩ := map_some hx
    subst e'
    exact inTab_shA hc
  · cases h
    intro f hf
    cases hf

end OnBytes.Desc.First.K4.Reads
