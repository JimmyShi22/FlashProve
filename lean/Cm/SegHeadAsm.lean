-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegHeadAsm.lean: the head's identities read the valid names only, and two cases in which
`Spec.ReadsAt` holds.

Main names:
  `idn_same`: if `Same t t'`, the identities with i < `nT`, k < 17 agree (over any commutative
    ring).
  `readsAt_ofMat`, `readsAt_toMat`: `Spec.ReadsAt`, the hypothesis of `TS.Spec.head_holds_int`
    (Cm/TargetSegHead.lean), holds of the trace of matrices, and of the matrices of a trace.

Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadProofs
import Cm.SegLayoutProofs
import Cm.HeadNoWrap

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg
open Cb Code Inst.Model Inst.Model.Head Inst.Model.Layout Finset Cm.Seg.Ex

/-! ## 1. Identities read the valid names only -/

section Same
variable {K : Type} [CommRing K]

/-- two families of cells agree at the names that the plain head reads -/
structure Same (t t' : Head.Cells K) : Prop where
  hf : ∀ φ < Plain.nHf, ∀ i < nT, t.hf φ i = t'.hf φ i
  hd : ∀ φ < nFeat .hd, ∀ i < nT, t.hd φ i = t'.hd φ i
  hr : ∀ φ < Plain.nHr, ∀ i < nT, t.hr φ i = t'.hr φ i
  x : ∀ φ < nFeat .x, ∀ i < nT, t.x φ i = t'.x φ i

theorem rd_same {m : ℕ} {c c' : ℕ → K} (h : ∀ l < m, c l = c' l) : Head.rd m c = Head.rd m c' :=
  sum_congr rfl fun l hl => by rw [h l (mem_range.1 hl)]

variable {t t' : Head.Cells K} (h : Same t t')
include h

theorem bl_same {l j i : ℕ} (hl : l < 5) (hj : j < nD) (hi : i < nT) : bl t l j i = bl t' l j i :=
  h.x _ (by simp only [fX, nFeat, nD] at *; omega) i hi
theorem xv_same {j i : ℕ} (hj : j < nD) (hi : i < nT) : xv t j i = xv t' j i :=
  rd_same fun _ hl => bl_same h hl hj hi
theorem nw_same {j i : ℕ} (hj : j < nD) (hi : i < nT) : Head.nw t j i = Head.nw t' j i :=
  rd_same fun l hl => h.hf _ (by simp only [fNw, Plain.nHf, nD] at *; omega) i hi
theorem rn_same {j i : ℕ} (hj : j < nD) (hi : i < nT) : rn t j i = rn t' j i := by
  unfold rn
  rw [rd_same fun l hl => h.hf (fRn l j) (by simp only [fRn, Plain.nHf, nD] at *; omega) i hi]
theorem d1_same {v i : ℕ} (hv : v < nV) (hi : i < nT) : d1 t v i = d1 t' v i :=
  rd_same fun l hl => h.hf _ (by simp only [fD1, Plain.nHf, nV] at *; omega) i hi
theorem d2_same {v i : ℕ} (hv : v < nV) (hi : i < nT) : d2 t v i = d2 t' v i :=
  h.hf _ (by simp only [fD2, Plain.nHf, nV] at *; omega) i hi
theorem nrm_same {j i : ℕ} (hj : j < nD) (hi : i < nT) : Head.nrm t j i = Head.nrm t' j i :=
  rd_same fun l hl => h.hd _ (by simp only [fNrm, nFeat, nD] at *; omega) i hi
theorem Dv_same {n i : ℕ} (hn : n < 99) (hi : i < nT) : Dv t n i = Dv t' n i := by
  unfold Dv
  rw [h.hr n hn i hi]
theorem lg_same (H : ℕ → ℕ → K) {i : ℕ} (hi : i < nT) (v : ℕ) :
    Head.lg t H i v = Head.lg t' H i v :=
  sum_congr rfl fun j hj => by rw [nrm_same h (mem_range.1 hj) hi]

omit h in
theorem b256_same {D D' : ℕ → K} (hD : ∀ n < 99, D n = D' n) {a n : ℕ} (han : a + n ≤ 99) :
    Ledger.b256 D a n = Ledger.b256 D' a n :=
  sum_congr rfl fun l hl => by rw [hD (a + l) (by have := mem_range.1 hl; omega)]

omit h in
theorem R_same {D D' : ℕ → K} (hD : ∀ n < 99, D n = D' n) : Ledger.R D = Ledger.R D' := by
  unfold Ledger.R Ledger.Rlo Ledger.Rhi
  rw [b256_same hD (by norm_num), b256_same hD (by norm_num)]

omit h in
theorem cs_same {D D' : ℕ → K} (hD : ∀ n < 99, D n = D' n) {s : ℕ} (hs : s ≤ 9) :
    Ledger.cs D s = Ledger.cs D' s := by
  unfold Ledger.cs
  split_ifs
  · rfl
  · exact hD 9 (by norm_num)
  · rw [b256_same hD (by omega)]

omit h in
theorem ledger_same (np : NormPar) (Ws : ℕ → K) {D D' : ℕ → K}
    (hD : ∀ n < 99, D n = D' n) {k : ℕ} (hk : k < 17) :
    Ledger.idn np Ws D k = Ledger.idn np Ws D' k := by
  have e1 : Ledger.sa D = Ledger.sa D' := by unfold Ledger.sa; rw [hD 58 (by norm_num), hD 59 (by norm_num), hD 60 (by norm_num), hD 61 (by norm_num)]
  have e2 : Ledger.sb D = Ledger.sb D' := by
    unfold Ledger.sb; rw [hD 62 (by norm_num), hD 63 (by norm_num)]
  have e3 : Ledger.sig D = Ledger.sig D' := by unfold Ledger.sig; rw [e1, e2]
  have e4 : Ledger.s0 D = Ledger.s0 D' := hD 59 (by norm_num)
  have e5 : Ledger.kc D = Ledger.kc D' := by unfold Ledger.kc; rw [hD 79 (by norm_num)]
  have f1 : Ledger.Vlo D = Ledger.Vlo D' := b256_same hD (by norm_num)
  have f2 : Ledger.Vhi D = Ledger.Vhi D' := b256_same hD (by norm_num)
  have f3 : Ledger.l1 D = Ledger.l1 D' := b256_same hD (by norm_num)
  have f4 : Ledger.h1 D = Ledger.h1 D' := b256_same hD (by norm_num)
  have f5 : Ledger.Blo D = Ledger.Blo D' := b256_same hD (by norm_num)
  have f6 : Ledger.Bhi D = Ledger.Bhi D' := b256_same hD (by norm_num)
  have f7 : Ledger.Rlo D = Ledger.Rlo D' := b256_same hD (by norm_num)
  have f8 : Ledger.Rhi D = Ledger.Rhi D' := b256_same hD (by norm_num)
  have f9 : Ledger.q1 D = Ledger.q1 D' := b256_same hD (by norm_num)
  have g1 : Ledger.rr D = Ledger.rr D' := b256_same hD (by norm_num)
  have g2 : Ledger.rq D = Ledger.rq D' := b256_same hD (by norm_num)
  unfold Ledger.idn
  split_ifs with h9
  · rw [cs_same hD (by omega), cs_same hD (by omega), hD k (by omega)]
  · match k with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => exact absurd (by norm_num) h9
    | 9 => simp only [e1, e2, f5, f6]
    | 10 => simp only [e1, e5, f1, f5, f3]
    | 11 => simp only [e2, e5, f2, f6]
    | 12 => simp only [e3, f3, f4]
    | 13 => simp only [e1, e2, f7, f8, f9]
    | 14 => simp only [e2, f8]
    | 15 => simp only [e1, e3, e4, f7, f9, g1]
    | 16 => simp only [e3, g1, g2]
    | _ + 17 => rfl

theorem idn_same (np : NormPar) {i k : ℕ} (hi : i < nT) (hk : k < 17) :
    Plain.idn np t i k = Plain.idn np t' i k := by
  have eW : (Ledger.Wsum nD fun l j => bl t l j i) = Ledger.Wsum nD fun l j => bl t' l j i := by
    funext s
    unfold Ledger.Wsum
    refine sum_congr rfl fun j hj => sum_congr rfl fun l hl => sum_congr rfl fun l' hl' => ?_
    beta_reduce
    rw [bl_same h (mem_range.1 hl) (mem_range.1 hj) hi,
      bl_same h (mem_range.1 hl') (mem_range.1 hj) hi]
  unfold Plain.idn
  rw [ledger_same np _ (fun n hn => Dv_same h hn hi) hk, eW]

end Same

/-! ## 2. Places -/

/-- a place that the layout says the head reads -/
abbrev IsHd (q : Cb.Place) : Prop := q ∈ reads Hd.plain 24

/-! ## 3. Two lemmas on the families and their tables -/

theorem mem_allFam (f : Plain.Fam) : f ∈ allFam := by cases f <;> simp [allFam]

theorem rowsH_eq (f : Plain.Fam) : (Plain.tableOf f).rows = 2 ^ tabLog f := by cases f <;> rfl

/-! ## 4. Integer matrices -/

/-- `Spec.ReadsAt` holds in the two cases in which `TS.head_holds_int` is used: of the trace of
matrices (here), and of the matrices of a trace (`readsAt_toMat`). -/
theorem readsAt_ofMat (M : ℕ → ℕ → ℕ → ℤ) : Spec.ReadsAt (ofMat Hd.plain M).vHead M :=
  have h := lay_read_ofMat Hd.plain M
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem readsAt_toMat (T : All.Trace) : Spec.ReadsAt T.vHead (toMat Hd.plain T) :=
  have h := lay_read_toMat Hd.plain lay_figures.2.2.2.2.2 T
  ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end Cm.Seg
