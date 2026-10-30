-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/TargetSegHeadProofs.lean: the statements of Cm/TargetSegHead.lean on values, proved:
`head_key_live`, `head_key_dead`, `head_idn_val`. The head of Cm/TargetSegHead.lean tells them in
words.

The
fields are `Gl.F`, `Gl.E` (Cb/Gl/GlField.lean);
the format is `Cm.Seg.TS.fmtRef` (Cm/TargetSegAll.lean);
the head's keys and tables are those of the plain head with the scaled table
(Cm/TargetPHead.lean). The scaled table has the entry 0.





The limits of the statements: the head of Cm/TargetSegHead.lean.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegHeadProofs
import Cm.TargetSegAll
import Cm.TargetSegHead
import Cm.TargetSegIdxModel
import Cm.TargetSegIdxModelProofs


set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm.Seg.TS
open Cb Code Inst.Model Inst.Model.Head Inst.Model.Layout Finset Cm.Seg.Ex

/-! ## Forms -/

section Forms
variable (A : ℕ → ℕ → ℕ → Cb.Gl.E)

@[simp] theorem val_cHf (φ i : ℕ) : (cHf φ i).val A = (tH A).hf φ i := by simp [cHf, tH, atE]
@[simp] theorem val_cHd (φ i : ℕ) : (cHd φ i).val A = (tH A).hd φ i := by simp [cHd, tH, atE]
@[simp] theorem val_cHr (φ i : ℕ) : (cHr φ i).val A = (tH A).hr φ i := by simp [cHr, tH, atE]
@[simp] theorem val_cX (φ i : ℕ) : (cX φ i).val A = (tH A).x φ i := by simp [cX, tH, atE]
@[simp] theorem val_cRd (m : ℕ) (c : ℕ → CForm Cb.Gl.E) :
    (cRd m c).val A = Head.rd m fun l => (c l).val A := by
  simp [cRd, Head.rd]
@[simp] theorem val_cBl (l j i : ℕ) : (cBl l j i).val A = bl (tH A) l j i := by simp [cBl, bl]
@[simp] theorem val_cXv (j i : ℕ) : (cXv j i).val A = xv (tH A) j i := by simp [cXv, xv]
@[simp] theorem val_cNw (j i : ℕ) : (cNw j i).val A = nw (tH A) j i := by simp [cNw, Head.nw]
@[simp] theorem val_cRn (j i : ℕ) : (cRn j i).val A = rn (tH A) j i := by simp [cRn, rn]
@[simp] theorem val_cD1 (v i : ℕ) : (cD1 v i).val A = d1 (tH A) v i := by simp [cD1, d1]
@[simp] theorem val_cD2 (v i : ℕ) : (cD2 v i).val A = d2 (tH A) v i := by simp [cD2, d2]
@[simp] theorem val_cNrm (j i : ℕ) : (cNrm j i).val A = nrm (tH A) j i := by simp [cNrm, Head.nrm]
@[simp] theorem val_cDv (n i : ℕ) : (cDv n i).val A = Dv (tH A) n i := by simp [cDv, Dv]

end Forms

/-! ## The logits -/

section Logits
variable (x : XI) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E)

theorem HW_dead {j t : ℕ} (hj : 5120 ≤ j) : HW W j t = 0 := by
  unfold HW HF FFSeg.matR
  rw [if_neg (fun h => absurd h.1 (not_lt.2 hj)), map_zero]

/-- lg_i[v] -/
theorem val_lgV {a i : ℕ} (ha : a < 202048) (hi : i < 1024) :
    Ex1.val fmtRef x W A lgV 28 (vOf a i) = Head.lg (tH A) (HW W) i a := by
  unfold lgV Head.lg
  rw [val1_sumA]
  have key : ∀ j < 2 ^ 13,
      Ex0.val fmtRef x W A (aff0 (nrmIn 13) * idx0 (aH (Src.run 0 18) (Src.run 28 13)))
          (28 + 13) (vOf a i * 2 ^ 13 + j) =
        if j < 5120 then nrm (tH A) j i * HW W j a else 0 := by
    intro j hj
    have hj' : j < 8192 := by simpa using hj
    have e1 : (vOf a i * 2 ^ 13 + j) % 2 ^ 13 = j := by ar
    have e2 : (vOf a i * 2 ^ 13 + j) / 2 ^ 13 % 2 ^ 10 = i := by ar
    have n1 : Src.num (Src.run 0 18) (28 + 13) (vOf a i * 2 ^ 13 + j) = a := by
      rw [num_run 0 18 (by norm_num)]
      ar
    have n2 : Src.num (Src.run 28 13) (28 + 13) (vOf a i * 2 ^ 13 + j) = j := by
      rw [num_run 28 13 (by norm_num)]
      ar
    rw [val0_mul, val0_aff, val0_idx,
      h_vtx (28 + 13) _ _ (run_length 0 18) (by rw [run_length]; norm_num)
        W _ (by rw [n1]; exact ha),
      n1, n2]
    unfold nrmIn
    rw [e1, e2]
    split_ifs with h
    · rw [val_cNrm]
      rfl
    · rw [val_cK, zero_mul]
  rw [sum_congr rfl fun j hj => key j (mem_range.1 hj)]
  rw [sum_range_dead (d := 5120) (by norm_num) _ fun j h1 _ => if_neg (not_lt.2 h1)]
  exact sum_congr rfl fun j hj => if_pos (mem_range.1 hj)

/-- lg_i[w_i] -/
theorem val_lgW {a i : ℕ} (ha : a < 2 ^ 18) (hi : i < 1024) :
    Ex1.val fmtRef x W A lgW 28 (vOf a i) = Head.lg (tH A) (HW W) i (x.w i) := by
  unfold lgW Head.lg
  have hw : x.w i < 202048 := x.w_lt i
  rw [val1_sumA, show (2 : ℕ) ^ 31 = 2 ^ 18 * 2 ^ 13 by norm_num, sum_range_mul]
  have key : ∀ t < 2 ^ 18, ∀ j < 2 ^ 13,
      Ex0.val fmtRef x W A (Ex.sc isW (aff0 (nrmIn 31) * idx0 (aH (Src.run 28 18) (Src.run 46 13))))
          (28 + 31) (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) =
        if t = x.w i then (if j < 5120 then nrm (tH A) j i * HW W j (x.w i) else 0) else 0 := by
    intro t ht j hj
    have hj' : j < 8192 := by simpa using hj
    have ht' : t < 262144 := by simpa using ht
    have ha' : a < 262144 := by simpa using ha
    have e1 : (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) % 2 ^ 13 = j := by ar
    have e2 : (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) / 2 ^ 31 % 2 ^ 10 = i := by ar
    have e3 : (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) / 2 ^ 13 % 2 ^ 18 = t := by ar
    rw [val0_sc]
    unfold isW
    rw [e2, e3]
    split_ifs with h
    · have n1 : Src.num (Src.run 28 18) (28 + 31) (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) =
          t := by
        rw [num_run 28 18 (by norm_num)]
        ar
      have n2 : Src.num (Src.run 46 13) (28 + 31) (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) =
          j := by
        rw [num_run 46 13 (by norm_num)]
        ar
      rw [one_mul, val0_mul, val0_aff, val0_idx,
        h_vtx (28 + 31) _ _ (run_length 28 18) (by rw [run_length]; norm_num)
          W _ (by rw [n1, h]; exact hw),
        n1, n2]
      unfold nrmIn
      rw [e1, e2, h]
      rename_i h5
      rw [if_pos h5, val_cNrm]
      rfl
    · have n1 : Src.num (Src.run 28 18) (28 + 31) (vOf a i * (2 ^ 18 * 2 ^ 13) + (t * 2 ^ 13 + j)) =
          t := by
        rw [num_run 28 18 (by norm_num)]
        ar
      rw [one_mul, val0_mul, val0_aff]
      unfold nrmIn
      rw [e1]
      rename_i h5
      rw [if_neg h5, val_cK, zero_mul]
    · rw [zero_mul]
  rw [sum_congr rfl fun t ht => sum_congr rfl fun j hj => key t (mem_range.1 ht) j (mem_range.1 hj)]
  rw [sum_eq_single (x.w i) (fun t _ hne => by simp [hne])
      (fun h => absurd (mem_range.2 (lt_trans hw (by norm_num))) h)]
  simp only [if_true]
  rw [sum_range_dead (d := 5120) (by norm_num) _ fun j h1 _ => if_neg (not_lt.2 h1)]
  exact sum_congr rfl fun j hj => if_pos (mem_range.1 hj)

end Logits

/-! ## The keys at live vertices -/

section Live
variable (np : NormPar) (x : XI) (W : ℕ → ℕ → Cb.Gl.F) (A : ℕ → ℕ → ℕ → Cb.Gl.E)

theorem val_gd {vx len a i : ℕ} (f : ℕ → ℕ → CForm Cb.Gl.E) (h2 : a < 2 ^ vx)
    (ha : a < len) (hi : i < 2 ^ 10) :
    (gd vx len f (vOf a i)).val A = (f a i).val A := by
  unfold gd
  rw [va_vOf h2 hi, vi_vOf a hi, if_pos ha]

theorem rhoT_live {a i : ℕ} (ha : a < 202048) (hi : i < 2 ^ 10) :
    rhoT x (vOf a i) = (((reqOf x).rho i : ℤ) : Cb.Gl.E) := by
  unfold rhoT
  rw [va_vOf (lt_trans ha (by norm_num)) hi, vi_vOf a hi, if_pos ha]

theorem val_k1Ex {a i : ℕ} (ha : a < 202048) (hi : i < 2 ^ 10) :
    Ex1.val fmtRef x W A k1Ex 28 (vOf a i) = K1 (tH A) (reqOf x) a i := by
  unfold k1Ex K1
  rw [val1_add, val1_aff, val1_smul, val1_pub, val_gd A _ (lt_trans ha (by norm_num)) ha hi,
    rhoT_live x ha hi, val_cD1]

theorem val_k2Ex {a i : ℕ} (ha : a < 202048) (hi : i < 2 ^ 10) :
    Ex1.val fmtRef x W A k2Ex 28 (vOf a i) = K2 (tH A) (reqOf x) a i := by
  unfold k2Ex K2
  rw [val1_add, val1_aff, val1_smul, val1_pub, val_gd A _ (lt_trans ha (by norm_num)) ha hi,
    rhoT_live x ha hi, val_cD2]

theorem val_mgEx {a i : ℕ} (ha : a < 202048) (hi : i < 2 ^ 10) :
    Ex1.val fmtRef x W A mgEx 28 (vOf a i) = Plain.mg (tH A) (HW W) (reqOf x) a i := by
  unfold mgEx Plain.mg
  rw [val1_sc, val1_sub, val1_sub, val1_pub, val_lgW x W A (lt_trans ha (by norm_num)) hi,
    val_lgV x W A ha hi, rhoT_live x ha hi]
  unfold ltW
  rw [va_vOf (lt_trans ha (by norm_num)) hi, vi_vOf a hi]
  rfl

end Live

theorem head_key_live : Spec.head_key_live := by
  intro np f x W A a i ha hi
  have hi' : i < 2 ^ 10 := hi
  unfold keyFam
  rw [fam_val]
  cases f
  · replace ha : a < 5120 := ha
    have h2 : a < 2 ^ 13 := lt_trans ha (by norm_num)
    show Ex1.val fmtRef x W A
        (aff (gd 13 5120 cXv) * aff (fun b => lR fun n => cDv n (vi b)) +
          aff (gd 13 5120 fun j i =>
              cK (2 ^ (np.K - 1)) - ((2 : Cb.Gl.E) ^ np.K) • cNw j i -
                ((2 : Cb.Gl.E) ^ 16) • cRn j i))
        23 (vOf a i) =
      xv (tH A) a i * Ledger.R (fun n => Dv (tH A) n i) + 2 ^ (np.K - 1) -
        2 ^ np.K * Head.nw (tH A) a i - 2 ^ 16 * rn (tH A) a i
    rw [val1_add, val1_mul, val1_aff, val1_aff, val1_aff, val_gd A _ h2 ha hi',
      val_gd A _ h2 ha hi', vi_vOf a hi']
    simp
    ring
  · replace ha : a < 5120 := ha
    have h2 : a < 2 ^ 13 := lt_trans ha (by norm_num)
    show Ex1.val fmtRef x W A
        (aff (gd 13 5120 fun j i => (((2 ^ (32 - np.K) : ℕ) : Cb.Gl.E)) • cRn j i)) 23 (vOf a i) =
      ((2 ^ (32 - np.K) : ℕ) : Cb.Gl.E) * rn (tH A) a i
    rw [val1_aff, val_gd A _ h2 ha hi', val_smul, val_cRn]
  · replace ha : a < 202048 := ha
    show Ex1.val fmtRef x W A (mgEx - ((2 : Cb.Gl.E) ^ 8) • k1Ex - k2Ex) 28 (vOf a i) =
      Plain.mg (tH A) (HW W) (reqOf x) a i -
        2 ^ 8 * K1 (tH A) (reqOf x) a i - K2 (tH A) (reqOf x) a i
    rw [val1_sub, val1_sub, val1_smul, val_mgEx x W A ha hi',
      val_k1Ex x W A ha hi', val_k2Ex x W A ha hi']
  · exact val_k1Ex x W A ha hi'
  · replace ha : a < 99 := ha
    have h2 : a < 2 ^ 7 := lt_trans ha (by norm_num)
    show Ex1.val fmtRef x W A
        (aff (gd 7 99 fun n i => (((Ledger.mu n : ℤ) : Cb.Gl.E)) • cDv n i)) 17 (vOf a i) =
      ((Ledger.mu a : ℤ) : Cb.Gl.E) * Dv (tH A) a i
    rw [val1_aff, val_gd A _ h2 ha hi', val_smul, val_cDv]
  · exact val_k2Ex x W A ha hi'
  · replace ha : a < 5120 := ha
    have h2 : a < 2 ^ 13 := lt_trans ha (by norm_num)
    show Ex1.val fmtRef x W A
        (aff fun b =>
          if va 13 b < 5120 then
            (cNw (va 13 b) (vi b) + cK (2 ^ 15)) +
              ((2 : Cb.Gl.E) ^ 28) • (cNrm (va 13 b) (vi b) + cK (2 ^ 11))
          else cK (((FC.row 0 : ℤ) : Cb.Gl.E)))
        23 (vOf a i) =
      (Head.nw (tH A) a i + 2 ^ 15) + 2 ^ 28 * (Head.nrm (tH A) a i + 2 ^ 11)
    rw [val1_aff, va_vOf h2 hi', vi_vOf a hi', if_pos ha]
    simp

/-! ## The keys at dead vertices -/

theorem zero_mem_tab (f : Plain.Fam) (hf : f ≠ .CNF) :
    ∃ u ∈ (keyTab f).set, (0 : Cb.Gl.E) = algebraMap Cb.Gl.F Cb.Gl.E u := by
  refine ⟨0, ⟨0, by positivity, ?_⟩, (map_zero _).symm⟩
  cases f <;> first | exact absurd rfl hf | simp [keyTab, tabOf, Plain.TP.tableOf, Plain.TP.R23, R16, R8]

theorem val_gd_dead (A : ℕ → ℕ → ℕ → Cb.Gl.E) {vx len b : ℕ}
    (f : ℕ → ℕ → CForm Cb.Gl.E) (h : len ≤ va vx b) : (gd vx len f b).val A = 0 := by
  unfold gd
  rw [if_neg (not_lt.2 h), val_cK]

theorem rhoT_dead (x : XI) {b : ℕ} (h : 202048 ≤ va 18 b) : rhoT x b = 0 := if_neg (not_lt.2 h)

theorem head_key_dead : Spec.head_key_dead := by
  intro np f x W A b _ hd
  unfold keyFam
  rw [fam_val]
  cases f
  · replace hd : 5120 ≤ va 13 b := hd
    rw [show Ex1.val fmtRef x W A (keyEx np .NF) (vxH .NF + 10) b = 0 by
      unfold keyEx
      rw [val1_add, val1_mul, val1_aff, val1_aff, val1_aff, val_gd_dead A _ hd,
        val_gd_dead A _ hd, zero_mul, add_zero]]
    exact zero_mem_tab _ (by decide)
  · replace hd : 5120 ≤ va 13 b := hd
    rw [show Ex1.val fmtRef x W A (keyEx np .NFH) (vxH .NFH + 10) b = 0 by
      unfold keyEx
      rw [val1_aff, val_gd_dead A _ hd]]
    exact zero_mem_tab _ (by decide)
  · replace hd : 202048 ≤ va 18 b := hd
    rw [show Ex1.val fmtRef x W A (keyEx np .HD0) (vxH .HD0 + 10) b = 0 by
      unfold keyEx mgEx k1Ex k2Ex
      rw [val1_sub, val1_sub, val1_smul, val1_sc, val1_add, val1_add, val1_aff, val1_aff, val1_smul,
        val1_smul, val1_pub, rhoT_dead x hd, val_gd_dead A _ hd, val_gd_dead A _ hd]
      ring]
    exact zero_mem_tab _ (by decide)
  · replace hd : 202048 ≤ va 18 b := hd
    rw [show Ex1.val fmtRef x W A (keyEx np .HD1) (vxH .HD1 + 10) b = 0 by
      unfold keyEx k1Ex
      rw [val1_add, val1_aff, val1_smul, val1_pub, rhoT_dead x hd, val_gd_dead A _ hd]
      ring]
    exact zero_mem_tab _ (by decide)
  · replace hd : 99 ≤ va 7 b := hd
    rw [show Ex1.val fmtRef x W A (keyEx np .ROW) (vxH .ROW + 10) b = 0 by
      unfold keyEx
      rw [val1_aff, val_gd_dead A _ hd]]
    exact zero_mem_tab _ (by decide)
  · replace hd : 202048 ≤ va 18 b := hd
    rw [show Ex1.val fmtRef x W A (keyEx np .HD2) (vxH .HD2 + 10) b = 0 by
      unfold keyEx k2Ex
      rw [val1_add, val1_aff, val1_smul, val1_pub, rhoT_dead x hd, val_gd_dead A _ hd]
      ring]
    exact zero_mem_tab _ (by decide)
  · replace hd : 5120 ≤ va 13 b := hd
    refine ⟨((FC.row 0 : ℤ) : Cb.Gl.F), ⟨0, by positivity, rfl⟩, ?_⟩
    unfold keyEx
    rw [val1_aff, if_neg (not_lt.2 hd), val_cK, map_intCast]

/-! ## The identities -/

theorem head_idn_val : Spec.head_idn_val := by
  intro np k x W A i hi
  have hi' : i < 1024 := hi
  unfold idnFam idnEx Plain.idn
  rw [fam_val, val_ledEx]
  have e1 : vi i = i := Nat.mod_eq_of_lt hi
  have hB : ∀ l j,
      j < 2 ^ 13 → (blIn l (i * 2 ^ 13 + j)).val A = if j < 5120 then bl (tH A) l j i else 0 := by
    intro l j hj
    have a1 : (i * 2 ^ 13 + j) % 2 ^ 13 = j := by ar
    have a2 : (i * 2 ^ 13 + j) / 2 ^ 13 % 2 ^ 10 = i := by ar
    unfold blIn
    rw [a1, a2]
    split_ifs
    · exact val_cBl A l j i
    · exact val_cK A 0
  have eW : (fun s => Ex1.val fmtRef x W A (wsEx 10 13 blIn s) 10 i) =
      Ledger.Wsum nD fun l j => bl (tH A) l j i := by
    funext s
    rw [val_wsEx fmtRef x W A 10 13 blIn s i 5120 (by norm_num) fun l j h1 h2 => by
        rw [hB l j h2, if_neg (not_lt.2 h1)]]
    unfold Ledger.Wsum
    refine sum_congr rfl fun j hj => sum_congr rfl fun l _ => sum_congr rfl fun l' _ => ?_
    have hj5 : j < 5120 := mem_range.1 hj
    beta_reduce
    rw [hB l j (lt_trans hj5 (by norm_num)),
      hB l' j (lt_trans hj5 (by norm_num)), if_pos hj5, if_pos hj5]
  have eD : (fun n => (cDv n (vi i)).val A) = fun n => Dv (tH A) n i := by
    funext n
    rw [e1, val_cDv]
  rw [eW, eD]

end Cm.Seg.TS
