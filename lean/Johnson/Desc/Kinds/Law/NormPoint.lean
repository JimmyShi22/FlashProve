-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormPoint.lean.
WHAT IT DOES NOT SHOW. That the hidden sums and products which a prover sends ARE these extensions:
that is the two sumchecks' and the two batching draws' matter, with chance in it: not here. That the
reads are true: the range check's law.
WHAT IT IS. THE ROW's 17 FORMS AT ANY POINT ON THE POSITIONS: with true reads, and with the nine
sums and the seven products laid as THE EXTENSIONS of the positions' true sums and products
(HeadNormLaw.lean: rowsAt c pV), each form's value is the sum over the positions of the equality
weight times the library's identity at that position's integers: of degree 1 in each coordinate of
pV, in values that the cells fix (rd_rowsAt): no chance in it. AND FROM A DRAWN POINT TO THE CORNERS
(rows_bridge): the cells first; then but for at most lt |K|^(lt - 1) points pV: if all 17 are 0 at
pV they are 0 at every position's corner: the clause rows of CellRelN.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormProof
import Johnson.Desc.Kinds.Law.Lemma2a
import Inst.Model.Common.LedgerForms

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits P6.rowProducts)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)

/-- The kind's equality weights, read, are the library's. -/
theorem wt_eq_eqN : ∀ (l : List K) (i : Nat), wt l i = Blocks.eqN l.length 0 (Blocks.ofList l) i
  | [], _ => by simp [wt, Blocks.eqN]
  | x :: xs, i => by
    unfold Blocks.eqN
    rw [List.length_cons, Finset.prod_range_succ', wt, wt_eq_eqN xs i, mul_comm]
    unfold Blocks.eqN
    congr 1
    refine Finset.prod_congr rfl fun t ht => ?_
    have h1 : xs.length + 1 - 1 - (t + 1) = xs.length - 1 - t := by omega
    rw [h1]
    simp [Blocks.ofList]

variable [Sizes] [Policy] [Request] [Token]

/-- A point's coordinates, read, as the library takes a point. -/
def ptK (z : Point) : Nat → K := Blocks.ofList (z.toList.map rd)

theorem sum_eq_ext (z : Point) (hz : z.size = lt) (v : Nat → K) :
    ((Finset.range T).sum fun t => rd (eq z t) * v t) = Blocks.ext lt v (ptK z) := by
  unfold Blocks.ext ptK
  refine Finset.sum_congr rfl fun t ht => ?_
  have h2 : t < 2 ^ z.size := by rw [hz]; exact Finset.mem_range.mp ht
  rw [rd_eq, if_pos h2, wt_eq_eqN, List.length_map, Array.length_toList, hz]

theorem rd_sum_point (z : Point) (hz : z.size = lt) (g : Nat → E) :
    rd (sumTo T fun t => eq z t * g t) = Blocks.ext lt (fun t => rd (g t)) (ptK z) := by
  rw [rd_sumTo, ← sum_eq_ext z hz]
  exact Finset.sum_congr rfl fun t _ => rd_mul _ _

section Filled
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads] {c : NCells}

/-- The 17 forms' values, as the library's identities with letters for the products. -/
theorem rowForms_values :
    Norm.rowForms.map cv = (List.range 17).map fun k =>
      Inst.Model.Ledger.idnP npOf
        (OnBytes.Desc.First.P6.dv Reading.gl W0 fun s => (Norm.W.getD (9 * 0 + s) {}).var)
        (OnBytes.Desc.First.P6.dv Reading.gl W0 (Norm.digit .rowsAtPV 0))
        (OnBytes.Desc.First.P6.dv Reading.gl W0 fun n => (Norm.P.getD (7 * 0 + n) {}).var) k := by
  rw [rowForms_eq, List.map_append]
  have h1 := OnBytes.Desc.First.P6.carries_value Reading.gl W0 (Norm.digit .rowsAtPV 0)
    (fun s => (Norm.W.getD (9 * 0 + s) {}).var) (fun n => (Norm.P.getD (7 * 0 + n) {}).var) npOf
  have h2 := OnBytes.Desc.First.P6.lines_value Reading.gl W0 (Norm.digit .rowsAtPV 0)
    (fun s => (Norm.W.getD (9 * 0 + s) {}).var) (fun n => (Norm.P.getD (7 * 0 + n) {}).var) npOf
    ((epsF : Nat) : E) ((2 ^ (MF + 1) : Nat) : Form)
    (by
      show rd ((epsF : Nat) : E) = _
      rw [rd_natCast]
      simp [npOf])
    (by
      show cv ((2 ^ (MF + 1) : Nat) : Form) = _
      rw [cv_natCast]
      simp [npOf])
  have e1 : (OnBytes.Desc.First.P6.carries (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
      (Norm.digit .rowsAtPV 0) fun s => (Norm.W.getD (9 * 0 + s) {}).var).map cv = _ := h1
  have e2 : (OnBytes.Desc.First.P6.lines (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
      (fun n => (Norm.P.getD (7 * 0 + n) {}).var) ((epsF : Nat) : E)
      ((2 ^ (MF + 1) : Nat) : Form)).map cv = _ := h2
  rw [e1, e2]
  have h17 : List.range 17 = List.range 9 ++ (List.range 8).map (9 + ·) := by decide
  rw [h17, List.map_append, List.map_map]
  rfl

/-- **At any point**: form number k, read, is the extension over the positions of the library's
identity number k at each position's integers. -/
theorem cv_rowForm_point (hF : FilledN c) (hz : (Norm.pV).size = lt) {k : Nat} (hk : k < 17) :
    (Norm.rowForms.map cv).getD k 0 =
      Blocks.ext lt (fun t => Inst.Model.Ledger.idn npOf (fun s => ((wsqZ c t s : Int) : K))
        (dK c t) k) (ptK Norm.pV) := by
  have hD : OnBytes.Desc.First.P6.dv Reading.gl W0 (Norm.digit .rowsAtPV 0) =
      fun m => Blocks.ext lt (fun t => dK c t m) (ptK Norm.pV) := by
    funext j
    show cv (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) (FinalNorm.entry .rowAtPV j) off1) = _
    rw [cv_addN, hF.hentry, cv_coe]
    show rd (sumTo T fun t' => eq Norm.pV t' * ofInt (c.cell .row j t')) + _ = _
    rw [rd_sum_point _ hz]
    have : (fun t => dK c t j) = fun t => rd (ofInt (c.cell .row j t)) + ((off1 : Nat) : K) := by
      funext t
      rw [rd_ofInt]
      unfold dK digZ off1
      push_cast
      ring
    rw [this, Blocks.ext_add, Blocks.ext_const]
  have hP : ∀ n, n < 7 → OnBytes.Desc.First.P6.dv Reading.gl W0
      (fun n => (Norm.P.getD (7 * 0 + n) {}).var) n =
      Blocks.ext lt (fun t => Inst.Model.Ledger.prods (dK c t) n) (ptK Norm.pV) := fun n hn => by
    show cv (Norm.P.getD (7 * 0 + n) {}).var = _
    rw [Nat.mul_zero, Nat.zero_add, hF.hP n hn, cv_coe, rd_sum_point _ hz]
    exact Blocks.ext_congr (fun t _ => rd_prodE c t hn) _
  have hW : ∀ s, s < 9 → OnBytes.Desc.First.P6.dv Reading.gl W0
      (fun s => (Norm.W.getD (9 * 0 + s) {}).var) s =
      Blocks.ext lt (fun t => ((wsqZ c t s : Int) : K)) (ptK Norm.pV) := fun s hs => by
    show cv (Norm.W.getD (9 * 0 + s) {}).var = _
    rw [Nat.mul_zero, Nat.zero_add, hF.hW s hs, cv_coe, rd_sum_point _ hz]
    exact Blocks.ext_congr (fun t _ => rd_ofInt _) _
  rw [rowForms_values, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by omega : k < 17)]
  simp only [Option.map_some, Option.getD_some]
  rw [Inst.Model.Ledger.ext_idn lt (fun m t => dK c t m) (ptK Norm.pV) npOf
    (fun s t => ((wsqZ c t s : Int) : K)) k, hD]
  -- the identities read the sums below 9 and the products below 7 alone
  unfold Inst.Model.Ledger.idnP
  by_cases h9 : k < 9
  · rw [if_pos h9, if_pos h9, hW k h9]
  · rw [if_neg h9, if_neg h9]
    have p0 := hP 0 (by omega)
    have p1 := hP 1 (by omega)
    have p2 := hP 2 (by omega)
    have p3 := hP 3 (by omega)
    have p4 := hP 4 (by omega)
    have p5 := hP 5 (by omega)
    have p6 := hP 6 (by omega)
    split <;> simp only [p0, p1, p2, p3, p4, p5, p6]

/-- Every one of the 17 forms has a constant that is written canonically. -/
theorem okE_rowForm (hF : FilledN c) {f : Form} (hf : f ∈ Norm.rowForms) :
    OnBytes.okE f.const = true := by
  rw [rowForms_eq, List.mem_append] at hf
  rcases hf with hf | hf
  · rw [OnBytes.Desc.First.P6.carries_eq] at hf
    obtain ⟨s, _, rfl⟩ := List.mem_map.mp hf
    exact okE_addMul _ _ _
  · rw [OnBytes.Desc.First.P6.lines, OnBytes.Desc.First.P6.root_eq,
      OnBytes.Desc.First.P6.reciprocal_eq] at hf
    simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact okE_addMul _ _ _
    · exact okE_addMul _ _ _
    · exact okE_addMul _ _ _
    · exact okE_addMul _ _ _
    · exact okE_addMul _ _ _
    · show OnBytes.okE (Norm.P.getD (7 * 0 + 6) {}).var.const = true
      rw [Nat.mul_zero, Nat.zero_add, hF.hP 6 (by omega)]
      exact okE_sumTo _ _
    · exact okE_addMul _ _ _
    · exact okE_addMul _ _ _

end Filled

/-! ## At the cells -/

/-- The library's identity number k at position t's integers, in K. -/
def vecK (c : NCells) (k t : Nat) : K :=
  Inst.Model.Ledger.idn npOf (fun s => ((wsqZ c t s : Int) : K)) (dK c t) k

variable {c : NCells}

theorem rowsAt_length (c : NCells) (pV : Point) : (rowsAt c pV).length = 17 := by
  letI := (cornerN 0 0).normIn; letI := normHeardAt c pV; letI := finalHeardAt c
  letI := normReadsAtCells c
  show (Norm.rowForms.map (·.const)).length = 17
  have h := congrArg List.length rowForms_values
  rw [List.length_map, List.length_map, List.length_range] at h
  rw [List.length_map, h]

/-- **LEMMA 2a-N, read in K.** -/
theorem rd_rowsAt (c : NCells) (pV : Point) (hz : pV.size = lt) {k : Nat} (hk : k < 17) :
    rd ((rowsAt c pV).getD k 0) = Blocks.ext lt (vecK c k) (ptK pV) := by
  letI := (cornerN 0 0).normIn; letI := normHeardAt c pV; letI := finalHeardAt c
  letI := normReadsAtCells c
  have h := cv_rowForm_point (filledN_at c (cornerN 0 0) pV) hz hk
  refine Eq.trans ?_ h
  show rd ((Norm.rowForms.map (·.const)).getD k 0) = _
  have e : Norm.rowForms.map cv = (Norm.rowForms.map (·.const)).map rd := by
    rw [List.map_map]
    exact List.map_congr_left fun f _ => cv_const f
  rw [e, ← rd_zero, List.getD_map]

theorem okE_rowsAt (c : NCells) (pV : Point) {v : E} (hv : v ∈ rowsAt c pV) :
    OnBytes.okE v = true := by
  letI := (cornerN 0 0).normIn; letI := normHeardAt c pV; letI := finalHeardAt c
  letI := normReadsAtCells c
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hv
  exact okE_rowForm (filledN_at c (cornerN 0 0) pV) hf

theorem ext_corner {t : Nat} (ht : t < T) (v : Nat → K) :
    Blocks.ext lt v (ptK (bits lt t)) = v t := by
  rw [← sum_eq_ext _ (size_bits lt t), Finset.sum_eq_single t]
  · rw [rd_eq_bits (n := lt) ht, if_pos rfl, one_mul]
  · intro b _ hb
    rw [rd_eq_bits (n := lt) ht, if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr ht) h

/-- The extension reads the point's first g coordinates alone. -/
theorem ext_congr_pt (g : Nat) (v : Nat → K) {a b : Nat → K} (h : ∀ t, t < g → a t = b t) :
    Blocks.ext g v a = Blocks.ext g v b := by
  unfold Blocks.ext Blocks.eqN
  refine Finset.sum_congr rfl fun X _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun t ht => ?_
  rw [Nat.zero_add, h t (Finset.mem_range.mp ht)]

/-- **FROM A DRAWN POINT TO THE CORNERS.** The cells come first. Then there is one set of at most
lt |K|^(lt - 1) points such that at every point pV outside it: if the 17 forms at pV (true reads;
the sums and the products laid as the extensions of the positions' own) are all 0, then they are 0
at every position's corner: the clause rows of CellRelN. -/
theorem rows_bridge (c : NCells) :
    ∃ Bad : Finset (Fin lt → K), Bad.card ≤ lt * Fintype.card K ^ (lt - 1) ∧
      ∀ pV : Point, pV.size = lt → (fun i : Fin lt => ptK pV i) ∉ Bad →
        (∀ v, v ∈ rowsAt c pV → v = 0) →
        ∀ t, t < T → ∀ v, v ∈ rowsAt c (bits lt t) → v = 0 := by
  classical
  by_cases hall : ∀ k, k < 17 → ∀ t, t < T → vecK c k t = 0
  · refine ⟨∅, by simp, fun _ _ _ _ t ht v hv => ?_⟩
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
    apply eq_of_rd (okE_rowsAt c _ hv) okE_zero
    have h := rd_rowsAt c (bits lt t) (size_bits lt t) hk'
    rw [List.getD_eq_getElem _ _ hk, ext_corner ht, hall k hk' t ht] at h
    rw [h, rd_zero]
  · obtain ⟨k, hk, t0, ht0, hne⟩ : ∃ k, k < 17 ∧ ∃ t, t < T ∧ vecK c k t ≠ 0 := by
      by_contra hcon
      exact hall fun k hk t ht => by
        by_contra hne
        exact hcon ⟨k, hk, t, ht, hne⟩
    refine ⟨Finset.univ.filter fun p : Fin lt → K => Blocks.ext lt (vecK c k) (Blocks.nat p) = 0,
      ?_, fun pV hz hout h0 => ?_⟩
    · have h := Blocks.cnt_ext_zero_le lt (vecK c k) ⟨t0, ht0, hne⟩
      unfold Prob.cnt at h
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h
      exact h
    · exfalso
      apply hout
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have hlen : k < (rowsAt c pV).length := by rw [rowsAt_length]; exact hk
      have h := rd_rowsAt c pV hz hk
      rw [List.getD_eq_getElem _ _ hlen, h0 _ (List.getElem_mem hlen), rd_zero] at h
      rw [h]
      refine ext_congr_pt lt _ fun t ht => ?_
      unfold Blocks.nat
      rw [dif_pos ht]

end VerifiableInference.Desc.Kinds.Head.Law
