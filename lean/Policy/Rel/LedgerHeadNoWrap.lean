-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerHeadNoWrap.lean

Nothing wraps around in the head with the cost ledger, modulo every p with 2^61 - 1 ≤ p (the class
`Big p`, Inst/Model/Bound/Base.lean), under the conditions of `noWrap_pol`: what holds modulo p of
the cells' small integers holds over the integers.

`noWrap_pol`: for a valid final normalisation, an output matrix with entries at most 2^12 in
absolute value and a policy with `AcceptancePolicy.OK`, cells that meet the head's field relation modulo p
(`RFz p`, Policy/Rel/LedgerHeadInt.lean; its clause `small` asks that each cell be below 2^18 in
absolute value), at a request and that policy, hold a stream on which the final normalisation runs,
and the policy's three clauses hold of that stream's logits.

For the final normalisation the proof goes through the plain head (`base_plain` here; `noWrap`,
Cm/TargetPHeadNoWrap.lean). In `top_digit`, with the key of Policy/Rel/LedgerHead.lean, nothing is
inverted. What an implementation's inequalities are, by a reading that need not hold of the released
programs (lean/LIMITS.md, L1): the head of Inst/Model/Head/PolicyNoWrap.lean.

Limits: for p below 2^61 - 1 this file lifts no congruence to an equation. It is on the head alone:
the stream is whatever the cells hold, and nothing here ties it to the layers. The constants are
those of Inst/Model/Head/.
-/
import Inst.Model.Head.NoWrapPolicy
import Inst.Model.Head.NoWrapProgramN
import Inst.Model.ProgramRPol
import Inst.Model.Head.HonestN
import Cm.TargetPHeadNoWrap
import Cm.TargetPHeadHonest
import Policy.Rel.LedgerHeadInt

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerHead

open Inst.Model Inst.Model.Head Inst.Model.Head.Policy Finset
open Cm.TI (Big big_pow)
open Cm.Plain.TP (inLut_eq inR16 inR8)

/-- Under `Big p`: two integers that are congruent modulo p and differ by less than 2^61 - 1 in
absolute value are equal. -/
theorem lift {p : ℕ} [Big p] {a b : ℤ} (h : a ≡ b [ZMOD (p : ℤ)]) (hlt : |a - b| < 2 ^ 61 - 1) :
    a = b :=
  Ledger.lift_eq h (lt_of_lt_of_le hlt (big_pow p))

/-! ## 1. The final normalisation, by the plain head -/

/-- the cells, with hf set to 0 from feature 20,480 on (the cells of the margins' digits and of the
looked-up values) -/
def base (t : Cells ℤ) : Cells ℤ :=
  ⟨fun φ i => if φ < 20480 then t.hf φ i else 0, t.hd, t.hr, t.x⟩

section Base
variable (t : Cells ℤ) (y : Req)

theorem base_nw {j : ℕ} (hj : j < nD) (i : ℕ) : nw (base t) j i = nw t j i := by
  rw [N.nw_eq, N.nw_eq]
  show (if fNw 0 j < 20480 then t.hf (fNw 0 j) i else 0) +
      256 * (if fNw 1 j < 20480 then t.hf (fNw 1 j) i else 0) = _
  rw [if_pos (by simp only [fNw, nD] at *; omega), if_pos (by simp only [fNw, nD] at *; omega)]

theorem base_rn {j : ℕ} (hj : j < nD) (i : ℕ) : rn (base t) j i = rn t j i := by
  rw [N.rn_eq, N.rn_eq]
  show 32896 + ((if fRn 0 j < 20480 then t.hf (fRn 0 j) i else 0) +
      256 * (if fRn 1 j < 20480 then t.hf (fRn 1 j) i else 0)) = _
  rw [if_pos (by simp only [fRn, nD] at *; omega), if_pos (by simp only [fRn, nD] at *; omega)]

theorem rho_req0 (i : ℕ) : (N.req0 y).rho i = 0 := by
  unfold Req.rho N.req0
  rw [if_neg (by simp only; omega)]

theorem base_K1 (v i : ℕ) : K1 (base t) (N.req0 y) v i = 0 := by
  unfold K1
  rw [N.d1_eq, rho_req0]
  show (if fD1 0 v < 20480 then t.hf (fD1 0 v) i else 0) +
      256 * (if fD1 1 v < 20480 then t.hf (fD1 1 v) i else 0) + 32896 * ((0 : ℤ) : ℤ) = 0
  rw [if_neg (by unfold fD1; omega), if_neg (by unfold fD1; omega)]
  norm_num

theorem base_K2 (v i : ℕ) : K2 (base t) (N.req0 y) v i = 0 := by
  unfold K2 d2
  rw [rho_req0]
  show (if fD2 v < 20480 then t.hf (fD2 v) i else 0) + 128 * ((0 : ℤ) : ℤ) = 0
  rw [if_neg (by unfold fD2; omega)]
  norm_num

theorem base_mg (H : Mat) (v i : ℕ) : Cm.Plain.mg (base t) H (N.req0 y) v i = 0 := by
  unfold Cm.Plain.mg
  rw [rho_req0]
  simp

end Base

section Norm
variable {p : ℕ} {np : NormPar} {H : Mat} {y : Req} {t : Cells ℤ} (h : RFz p np H y t)
include h

/-- Under `RFz p`, for every number p: the cells `base t`, at the request without a covered
position, meet the plain head's relation (`Cm.Plain.TP.RFz p`). -/
theorem base_plain : Cm.Plain.TP.RFz p np H (N.req0 y) (base t) where
  small := fun i hi =>
    ⟨fun φ hφ => by
        show |if φ < 20480 then t.hf φ i else 0| < 2 ^ 18
        split_ifs
        · exact (h.small i hi).1 φ (lt_of_lt_of_le hφ (by decide))
        · norm_num,
      (h.small i hi).2.1,
      fun φ hφ => (h.small i hi).2.2.1 φ (lt_of_lt_of_le hφ (by decide)),
      (h.small i hi).2.2.2⟩
  keys := fun s x i hx hi => by
    cases s
    · -- NF
      have hj : x < nD := hx
      have e : Cm.Plain.TP.key np (base t) H (N.req0 y) .NF x i = key np t H y .NF x i := by
        simp only [Cm.Plain.TP.key, key]
        rw [base_nw t hj, base_rn t hj]
        rfl
      rw [e]
      exact h.keys .NF x i hx hi
    · -- NFH
      have hj : x < nD := hx
      have e : Cm.Plain.TP.key np (base t) H (N.req0 y) .NFH x i = key np t H y .NFH x i := by
        simp only [Cm.Plain.TP.key, key]
        rw [base_rn t hj]
      rw [e]
      exact h.keys .NFH x i hx hi
    · -- HD0
      show ∃ u < Cm.Plain.TP.R23.rows,
        Cm.Plain.mg (base t) H (N.req0 y) x i - 2 ^ 8 * K1 (base t) (N.req0 y) x i -
            K2 (base t) (N.req0 y) x i ≡
          Cm.Plain.TP.R23.row u [ZMOD (p : ℤ)]
      rw [base_mg, base_K1, base_K2]
      exact inLut_eq 0 (by show 0 < 2 ^ 16; norm_num)
        (by show (0 : ℤ) - 2 ^ 8 * 0 - 0 = 2 ^ 23 * ((0 : ℕ) : ℤ); norm_num)
    · -- HD1
      show ∃ u < R16.rows, K1 (base t) (N.req0 y) x i ≡ R16.row u [ZMOD (p : ℤ)]
      rw [base_K1]
      exact inR16 (by norm_num) (by norm_num)
    · -- ROW
      exact h.keys .ROW x i (lt_of_lt_of_le hx (by decide)) hi
    · -- HD2
      show ∃ u < R8.rows, K2 (base t) (N.req0 y) x i ≡ R8.row u [ZMOD (p : ℤ)]
      rw [base_K2]
      exact inR8 (by norm_num) (by norm_num)
    · -- CNF
      have hj : x < nD := hx
      have e : Cm.Plain.TP.key np (base t) H (N.req0 y) .CNF x i = key np t H y .CNF x i := by
        simp only [Cm.Plain.TP.key, key]
        rw [base_nw t hj]
        rfl
      rw [e]
      exact h.keys .CNF x i hx hi
  idns := fun i hi k hk => h.idns i hi k hk

variable [Big p]

/-- Under `RFz p`, `Big p`, `np.OK`, |H| ≤ 2^12, at every position: the final normalisation of the
stream that the cells hold runs, nrm is its output, and the stream is below 2^39 in absolute
value. -/
theorem norm_facts (hn : np.OK) (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {i : ℕ} (hi : i < nT) :
    NORM.OK np nD (xAt t i) ∧ (∀ j < nD, nrm t j i = NORM.out np nD (xAt t i) j) ∧
    ∀ j < nD, |xAt t i j| < 2 ^ 39 :=
  ⟨((Cm.Plain.TP.noWrap (base_plain h) hn hH).1 i hi).1,
    fun j hj => (((Cm.Plain.TP.noWrap (base_plain h) hn hH).1 i hi).2.1 j hj).2,
    ((Cm.Plain.TP.noWrap (base_plain h) hn hH).1 i hi).2.2⟩

/-- under `RFz p`, `Big p`, |H| ≤ 2^12, at a position below 1,024: |lg| ≤ 5,120 · 2,047 · 2^12 -/
theorem lg_abs (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {i : ℕ} (hi : i < nT) (v : ℕ) :
    |Head.lg t H i v| ≤ 42928701440 :=
  Cm.Plain.TP.step_H5 (base_plain h) hH hi v

end Norm

/-! ## 2. The policy's relations: from congruences modulo p to the integers -/

section
variable {P : Params} (p : ℕ) (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) (h : Hid)
  (K1 K2 ex : ℕ → ℕ → ℤ)

/-- The relations as congruences modulo p, with ranges for the cost ledger's six numbers (c, b, u,
k, z, zs) and the two lower digits, and a bound on ex. -/
structure HCong : Prop where
  rng : ∀ t ∈ x.cnt,
    (0 ≤ h.c t ∧ 0 ≤ h.b t ∧ 0 ≤ h.u t ∧ 0 ≤ h.k t ∧ 0 ≤ h.z t ∧ 0 ≤ h.zs t) ∧ h.Bytes t
  K1r : ∀ t, x.r ≤ t → t < x.e → ∀ v < P.V, 0 ≤ K1 v t ∧ K1 v t < 2 ^ 16
  K2r : ∀ t, x.r ≤ t → t < x.e → ∀ v < P.V, 0 ≤ K2 v t ∧ K2 v t < 2 ^ 8
  exb : ∀ t, x.r ≤ t → t < x.e → ∀ v < P.V, |ex v t| < 2 ^ 40
  HD0 : ∀ t, x.r ≤ t → t < x.e →
    ∀ v < P.V, ∃ u : ℕ,
      u < 2 ^ 16 ∧
      marg lg x h t v - 2 ^ 8 * K1 v t - K2 v t ≡ 2 ^ 23 * (u : ℤ) [ZMOD (p : ℤ)]
  HE : ∀ t, x.r ≤ t → t < x.e →
    ∀ v < P.V, ∃ u : ℕ, u < 2 ^ 16 ∧ K1 v t + 2 ^ 16 * ex v t ≡ FE.row u [ZMOD (p : ℤ)]
  Z : ∀ t ∈ x.cnt, h.zs t + ∑ v ∈ Finset.range P.V, ex v t ≡ 2 ^ 24 [ZMOD (p : ℤ)]
  B2 : ∑ t ∈ x.cnt, (h.c t + pol.C * h.b t + h.u t) ≡ pol.theta * x.NB [ZMOD (p : ℤ)]
  B3 : ∑ t ∈ x.cnt, (h.b t + h.z t) ≡ (if 0 < x.NB then (pol.cap : ℤ) else 0) [ZMOD (p : ℤ)]
  B4 : ∀ t ∈ x.cnt, h.c t + h.k t ≡ pol.C [ZMOD (p : ℤ)]

end

section
variable {P : Params} {p : ℕ} {lg : ℕ → ℕ → ℤ} {pol : AcceptancePolicy} {x : Instance P} {h : Hid}
  {K1 K2 ex : ℕ → ℕ → ℤ}

/-- under `HCong` and `Fit`, for t < T and v < V: −2^37 < margin < 2^46, before anything is known of
its digits -/
theorem marg_bounds (H : HCong p lg pol x h K1 K2 ex) (hf : Fit P lg pol) {t : ℕ} (ht : t < P.T)
    {v : ℕ} (hv : v < P.V) :
    -2 ^ 37 < marg lg x h t v ∧ marg lg x h t v < 2 ^ 46 := by
  have l1 := abs_le.1 (hf.lg t ht (x.w t) (x.w_lt t))
  have l2 := abs_le.1 (hf.lg t ht v hv)
  have hb : (if v < x.w t then (1 : ℤ) else 0) = 0 ∨ (if v < x.w t then (1 : ℤ) else 0) = 1 := by
    split_ifs <;> simp
  unfold marg rhoC
  by_cases hc : t ∈ x.cnt
  · obtain ⟨⟨c0, b0, -⟩, c1, b1, -⟩ := H.rng t hc
    rw [if_pos hc]
    rcases hb with hb | hb <;> rw [hb] <;> constructor <;> omega
  · rw [if_neg hc]
    rcases hb with hb | hb <;> rw [hb] <;> constructor <;> omega

variable [Big p]

/-- the key of the top digit, under `Big p`, `HCong p`, `Fit`, at a covered position, v < V: the
margin is K2 + 2^8 K1 + 2^23 K0 with K0 in [0, 2^16) -/
theorem top_digit (H : HCong p lg pol x h K1 K2 ex) (hf : Fit P lg pol) {t : ℕ} (hr : x.r ≤ t)
    (he : t < x.e) {v : ℕ} (hv : v < P.V) :
    marg lg x h t v = K2 v t + 2 ^ 8 * K1 v t + 2 ^ 23 * K0of lg x h K1 K2 v t ∧
    0 ≤ K0of lg x h K1 K2 v t ∧
    K0of lg x h K1 K2 v t < 2 ^ 16 := by
  obtain ⟨u, hu, hk⟩ := H.HD0 t hr he v hv
  have hu' : (u : ℤ) < 65536 := by exact_mod_cast hu
  have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
  have k1 := H.K1r t hr he v hv
  have k2 := H.K2r t hr he v hv
  have m := marg_bounds H hf (lt_of_lt_of_le he x.e_le) hv
  unfold K0of
  set A := marg lg x h t v - 2 ^ 8 * K1 v t - K2 v t with hA
  have e : A = 2 ^ 23 * (u : ℤ) := lift hk (by
    rw [abs_lt]; constructor <;> omega)
  have e2 : A / 2 ^ 23 = u := by rw [e]; exact Int.mul_ediv_cancel_left _ (by norm_num)
  rw [e2]
  refine ⟨by omega, hu0, by omega⟩

/-- the key of EX, under `Big p`, `HCong p`, at a covered position, v < V: the looked-up value is
the row of EX that the middle digit names -/
theorem he_of_cong (H : HCong p lg pol x h K1 K2 ex) {t : ℕ} (hr : x.r ≤ t) (he : t < x.e)
    {v : ℕ} (hv : v < P.V) : ex v t = EX (K1 v t).toNat := by
  obtain ⟨u, hu, hk⟩ := H.HE t hr he v hv
  have hu' : (u : ℤ) < 65536 := by exact_mod_cast hu
  have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
  have k1 := H.K1r t hr he v hv
  have b := abs_lt.1 (H.exb t hr he v hv)
  have t9 := TablesSanity.tab9.2 u
  have e : K1 v t + 2 ^ 16 * ex v t = FE.row u := lift hk (by
    show |K1 v t + 2 ^ 16 * ex v t - ((u : ℤ) + 2 ^ 16 * EX u)| < 2 ^ 61 - 1
    rw [abs_lt]; constructor <;> omega)
  exact (key_split k1.1 k1.2 hu e).2

theorem sum_ex_bounds (H : HCong p lg pol x h K1 K2 ex) (hV : 2 * P.V ≤ 2 ^ 24)
    {t : ℕ} (ht : t ∈ x.cnt) :
    0 ≤ ∑ v ∈ Finset.range P.V, ex v t ∧ ∑ v ∈ Finset.range P.V, ex v t ≤ 2 ^ 47 := by
  obtain ⟨hr, he⟩ := cnt_covered ht
  have hb : ∀ v ∈ Finset.range P.V, 1 ≤ ex v t ∧ ex v t ≤ 2 ^ 24 := fun v hv => by
    rw [he_of_cong H hr he (Finset.mem_range.1 hv)]; exact TablesSanity.tab9.2 _
  refine ⟨Finset.sum_nonneg fun v hv => by have := (hb v hv).1; omega, ?_⟩
  have h1 :=
    Finset.sum_le_card_nsmul (Finset.range P.V) (fun v => ex v t) (2 ^ 24) fun v hv => (hb v hv).2
  rw [Finset.card_range, nsmul_eq_mul] at h1
  have h2 : 2 * (P.V : ℤ) ≤ 2 ^ 24 := by exact_mod_cast hV
  have h3 : ∑ v ∈ Finset.range P.V, ex v t ≤ (P.V : ℤ) * 2 ^ 24 := h1
  omega

/-- No wrap-around: under `Big p`, `Fit`, T ≤ 2^10 the congruences `HCong p` give the relations over
ℤ. -/
theorem HRel_of_HCong (H : HCong p lg pol x h K1 K2 ex) (hf : Fit P lg pol) (hT : P.T ≤ 2 ^ 10) :
    HRel lg pol x h ⟨K0of lg x h K1 K2, K1, K2, ex⟩ where
  nonneg := fun t ht => (H.rng t ht).1
  B1 := fun t hr he v hv =>
    ⟨(top_digit H hf hr he hv).1, (top_digit H hf hr he hv).2,
      H.K1r t hr he v hv, H.K2r t hr he v hv⟩
  HE := fun t hr he v hv => he_of_cong H hr he hv
  Z := fun t ht => by
    obtain ⟨⟨-, -, -, -, -, s0⟩, -, -, -, -, -, s1⟩ := H.rng t ht
    have b := sum_ex_bounds H hf.V ht
    show h.zs t + ∑ v ∈ Finset.range P.V, ex v t = 2 ^ 24
    exact lift (H.Z t ht) (by rw [abs_lt]; constructor <;> omega)
  B2 := by
    have hC' : (pol.C : ℤ) < 2 ^ 40 := by exact_mod_cast hf.C
    have hθ' : (pol.theta : ℤ) < 2 ^ 40 := by exact_mod_cast hf.theta
    have b : 0 ≤ ∑ t ∈ x.cnt, (h.c t + pol.C * h.b t + h.u t) ∧
        ∑ t ∈ x.cnt, (h.c t + pol.C * h.b t + h.u t) ≤ 2 ^ 10 * 2 ^ 49 :=
        sum_cnt_bounds (x := x) hT (fun t => h.c t + pol.C * h.b t + h.u t) (B := 2 ^ 49)
            (by norm_num) fun t ht => by
      show 0 ≤ h.c t + pol.C * h.b t + h.u t ∧ h.c t + pol.C * h.b t + h.u t ≤ 2 ^ 49
      obtain ⟨⟨c0, b0, u0, -⟩, c1, b1, u1, -⟩ := H.rng t ht
      have m0 : 0 ≤ (pol.C : ℤ) * h.b t := mul_nonneg (Int.natCast_nonneg _) b0
      have m1 : (pol.C : ℤ) * h.b t ≤ 2 ^ 40 * 2 ^ 8 :=
        mul_le_mul (le_of_lt hC') (le_of_lt b1) b0 (by norm_num)
      constructor <;> omega
    have n0 : 0 ≤ (pol.theta : ℤ) * x.NB := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have n1 : (pol.theta : ℤ) * x.NB ≤ 2 ^ 40 * 2 ^ 10 :=
      mul_le_mul (le_of_lt hθ') (NB_le hT) (Int.natCast_nonneg _) (by norm_num)
    exact lift H.B2 (by rw [abs_lt]; constructor <;> omega)
  B3 := by
    have hc' : (pol.cap : ℤ) < 2 ^ 16 := by exact_mod_cast hf.cap
    have hc0 : (0 : ℤ) ≤ pol.cap := Int.natCast_nonneg _
    have b : 0 ≤ ∑ t ∈ x.cnt, (h.b t + h.z t) ∧ ∑ t ∈ x.cnt, (h.b t + h.z t) ≤ 2 ^ 10 * 2 ^ 17 :=
        sum_cnt_bounds (x := x) hT (fun t => h.b t + h.z t) (B := 2 ^ 17)
            (by norm_num) fun t ht => by
      show 0 ≤ h.b t + h.z t ∧ h.b t + h.z t ≤ 2 ^ 17
      obtain ⟨⟨-, b0, -, -, z0, -⟩, -, b1, -, -, z1, -⟩ := H.rng t ht
      constructor <;> omega
    exact lift H.B3 (by rw [abs_lt]; split <;> constructor <;> omega)
  B4 := fun t ht => by
    have hC' : (pol.C : ℤ) < 2 ^ 40 := by exact_mod_cast hf.C
    have hC0 : (0 : ℤ) ≤ pol.C := Int.natCast_nonneg _
    obtain ⟨⟨c0, -, -, k0, -⟩, c1, -, -, k1, -⟩ := H.rng t ht
    exact lift (H.B4 t ht) (by rw [abs_lt]; constructor <;> omega)

end

/-! ## 3. From the field relation to the policy -/

section Steps
variable {p : ℕ} [Big p] {np : NormPar} {H : Mat} {y : Req} {t : Cells ℤ} (h : RFz p np H y t)
include h

omit [Big p] in
theorem hf_lt {φ i : ℕ} (hφ : φ < nFeat .hf) (hi : i < nT) :
    -2 ^ 18 < t.hf φ i ∧ t.hf φ i < 2 ^ 18 :=
  abs_lt.1 ((h.small i hi).1 φ hφ)
omit [Big p] in
theorem hr_lt {φ i : ℕ} (hφ : φ < nFeat .hr) (hi : i < nT) :
    -2 ^ 18 < t.hr φ i ∧ t.hr φ i < 2 ^ 18 :=
  abs_lt.1 ((h.small i hi).2.2.1 φ hφ)

omit [Big p] in
theorem K1_abs {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    -67403904 < K1 t y v i ∧ K1 t y v i < 67403904 := by
  have a := hf_lt h (φ := fD1 0 v) (by simp only [fD1, nFeat, nV] at *; omega) hi
  have b := hf_lt h (φ := fD1 1 v) (by simp only [fD1, nFeat, nV] at *; omega) hi
  have r := y.rho_01 i
  simp only [K1, N.d1_eq, Int.cast_id]
  norm_num at a b
  rcases r with r | r <;> rw [r] <;> omega
omit [Big p] in
theorem K2_abs {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    -262272 < K2 t y v i ∧ K2 t y v i < 262272 := by
  have a := hf_lt h (φ := fD2 v) (by simp only [fD2, nFeat, nV] at *; omega) hi
  have r := y.rho_01 i
  simp only [K2, d2, Int.cast_id]
  norm_num at a
  rcases r with r | r <;> rw [r] <;> omega

/-- under `RFz p`, `Big p`, for v < V and i < 1,024: 0 ≤ K_1 < 2^16, and 0 ≤ K_2 < 2^8
(`K2_range`) -/
theorem K1_range {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    0 ≤ K1 t y v i ∧ K1 t y v i < 2 ^ 16 := by
  obtain ⟨u, hu, hk⟩ := h.keys .HD1 v i hv hi
  have a := K1_abs h hv hi
  have hu' : (u : ℤ) < 65536 := by exact_mod_cast hu
  have e : K1 t y v i = u := lift hk (by
    show |K1 t y v i - (u : ℤ)| < 2 ^ 61 - 1
    rw [abs_lt]; constructor <;> omega)
  omega
theorem K2_range {v i : ℕ} (hv : v < nV) (hi : i < nT) : 0 ≤ K2 t y v i ∧ K2 t y v i < 2 ^ 8 := by
  obtain ⟨u, hu, hk⟩ := h.keys .HD2 v i hv hi
  have a := K2_abs h hv hi
  have hu' : (u : ℤ) < 256 := by exact_mod_cast hu
  have e : K2 t y v i = u := lift hk (by
    show |K2 t y v i - (u : ℤ)| < 2 ^ 61 - 1
    rw [abs_lt]; constructor <;> omega)
  omega

/-- under `RFz p`, `Big p`: a ledger byte with multiplier 1 (99 ≤ n < 120) is a byte, at a position
below 1,024 -/
theorem byte_range {n i : ℕ} (h99 : 99 ≤ n) (hn : n < 120) (hi : i < nT) :
    0 ≤ Dv t n i ∧ Dv t n i < 256 := by
  obtain ⟨u, hu, hk⟩ := h.keys .ROW n i hn hi
  have hu' : (u : ℤ) < 256 := by exact_mod_cast hu
  have hu0 : (0 : ℤ) ≤ u := Int.natCast_nonneg u
  have a := hr_lt h (φ := n) hn hi
  have hmu : Ledger.mu n = 1 := by
    unfold Ledger.mu
    split_ifs <;> first | rfl | omega
  have hk' : ((Ledger.mu n : ℤ) : ℤ) * Dv t n i ≡ (u : ℤ) [ZMOD (p : ℤ)] := hk
  rw [hmu, one_mul] at hk'
  norm_num at a
  have e : Dv t n i = u := lift hk' (by
    rw [abs_lt]; unfold Dv; constructor <;> omega)
  omega

/-- under `RFz p`, `Big p`, at a position below 1,024: the cost ledger's six numbers (c, b, u, k, z,
zs), read from the cells, are not negative and within their bytes -/
theorem hid_full {i : ℕ} (hi : i < nT) :
    (0 ≤ (hidOf t).c i ∧ 0 ≤ (hidOf t).b i ∧ 0 ≤ (hidOf t).u i ∧ 0 ≤ (hidOf t).k i ∧
      0 ≤ (hidOf t).z i ∧ 0 ≤ (hidOf t).zs i) ∧
    (hidOf t).Bytes i := by
  have b : ∀ a n, 99 ≤ a → a + n ≤ 120 →
      0 ≤ Ledger.b256 (fun m => Dv t m i) a n ∧
      Ledger.b256 (fun m => Dv t m i) a n < 256 ^ n := fun a n ha han =>
    b256_range _ a n fun l hl => byte_range h (by omega) (by omega) hi
  have c := b 99 5 (by norm_num) (by norm_num)
  have bb := b 104 1 (by norm_num) (by norm_num)
  have u := b 105 5 (by norm_num) (by norm_num)
  have k := b 110 5 (by norm_num) (by norm_num)
  have z := b 115 2 (by norm_num) (by norm_num)
  have zs := b 117 3 (by norm_num) (by norm_num)
  exact ⟨⟨c.1, bb.1, u.1, k.1, z.1, zs.1⟩,
    by norm_num at c; exact c.2,
    by norm_num at bb; exact bb.2,
    by norm_num at u; exact u.2,
    by norm_num at k; exact k.2,
    by norm_num at z; exact z.2,
    by norm_num at zs; exact zs.2⟩

omit [Big p] in
/-- under `RFz p`, for v < V and i < 1,024: |ex| < 2^40, before anything else is known of the
looked-up value -/
theorem ex_abs {v i : ℕ} (hv : v < nV) (hi : i < nT) : |ex t v i| < 2 ^ 40 := by
  have a := hf_lt h (φ := fEx 0 v) (by simp only [fEx, nFeat, nV] at *; omega) hi
  have b := hf_lt h (φ := fEx 1 v) (by simp only [fEx, nFeat, nV] at *; omega) hi
  have c := hf_lt h (φ := fEx 2 v) (by simp only [fEx, nFeat, nV] at *; omega) hi
  rw [N.ex_eq, abs_lt]
  norm_num at a b c
  constructor <;> omega

omit [Big p] in
/-- under `RFz p`, for i < 1,024: K_1 + 2^16 ex is congruent modulo p to a row of FE, at every
token -/
theorem key_FE {v i : ℕ} (hv : v < nV) (hi : i < nT) :
    ∃ u : ℕ, u < 2 ^ 16 ∧ K1 t y v i + 2 ^ 16 * ex t v i ≡ FE.row u [ZMOD (p : ℤ)] := by
  by_cases hlt : v < 131072
  · obtain ⟨u, hu, hk⟩ := h.keys .HE0 v i hlt hi
    exact ⟨u, hu, hk⟩
  · obtain ⟨u, hu, hk⟩ :=
      h.keys .HE1 (v - 131072) i (by show v - 131072 < 70976; unfold nV at hv; omega) hi
    have e : 131072 + (v - 131072) = v := by omega
    have hk' : K1 t y (131072 + (v - 131072)) i + 2 ^ 16 * ex t (131072 + (v - 131072)) i ≡
        FE.row u [ZMOD (p : ℤ)] := hk
    rw [e] at hk'
    exact ⟨u, hu, hk'⟩

end Steps

section Pol
variable {p : ℕ} [Big p] {np : NormPar} {H : Mat} {pol : AcceptancePolicy} {x : Instance ppref} {t : Cells ℤ}
  (h : RFz p np H (Req.of pol x) t)
include h

/-- Under `Big p`: from the field relation (`RFz p` at `Req.of pol x`) to the relations as
congruences. -/
theorem hcong :
    HCong p (fun i v => Head.lg t H i v) pol x (hidOf t) (K1 t (Req.of pol x))
      (K2 t (Req.of pol x)) (ex t) where
  rng := fun i hi => hid_full h (lt_of_lt_of_le (cnt_covered hi).2 x.e_le)
  K1r := fun i _ he v hv => K1_range h hv (lt_of_lt_of_le he x.e_le)
  K2r := fun i _ he v hv => K2_range h hv (lt_of_lt_of_le he x.e_le)
  exb := fun i _ he v hv => ex_abs h hv (lt_of_lt_of_le he x.e_le)
  HD0 := fun i hr he v hv => by
    obtain ⟨u, hu, hk⟩ := h.keys .HD0 v i hv (lt_of_lt_of_le he x.e_le)
    refine ⟨u, hu, ?_⟩
    rw [← N.mg_marg (H := H) (pol := pol) hr he v]
    exact hk
  HE := fun i _ he v hv => key_FE h hv (lt_of_lt_of_le he x.e_le)
  Z := fun i hi => by
    have hz := (h.jc i (lt_of_lt_of_le (cnt_covered hi).2 x.e_le)).2
    unfold dZ at hz
    rw [Req.rhoC_of, if_pos hi] at hz
    have hz' : hidS t i + ∑ v ∈ range nV, ex t v i - 2 ^ 24 ≡ 0 [ZMOD (p : ℤ)] := by simpa using hz
    have := hz'.add_right (2 ^ 24)
    simpa [hidOf] using this
  B2 := by
    have hs := h.sums.1
    unfold sB2 at hs
    have e : ∑ i ∈ range nT,
          (((Req.of pol x).rhoC i : ℤ) : ℤ) * (hidC t i + ((pol.C : ℕ) : ℤ) * hidB t i + hidU t i) =
        ∑ i ∈ x.cnt, (hidC t i + (pol.C : ℤ) * hidB t i + hidU t i) :=
      Head.sum_rhoC pol x _
    have hs' : ∑ i ∈ x.cnt, (hidC t i + (pol.C : ℤ) * hidB t i + hidU t i) -
          (pol.theta : ℤ) * (x.NB : ℤ) ≡
        0 [ZMOD (p : ℤ)] := by
      rw [← e]
      exact hs
    have := hs'.add_right ((pol.theta : ℤ) * (x.NB : ℤ))
    simpa [hidOf] using this
  B3 := by
    have hs := h.sums.2
    unfold sB3 at hs
    have e : ∑ i ∈ range nT, (((Req.of pol x).rhoC i : ℤ) : ℤ) * (hidB t i + hidZ t i) =
        ∑ i ∈ x.cnt, (hidB t i + hidZ t i) :=
      Head.sum_rhoC pol x _
    have hs' : ∑ i ∈ x.cnt, (hidB t i + hidZ t i) - (if 0 < x.NB then (pol.cap : ℤ) else 0) ≡
        0 [ZMOD (p : ℤ)] := by
      rw [← e]
      exact hs
    have := hs'.add_right (if 0 < x.NB then (pol.cap : ℤ) else 0)
    simpa [hidOf] using this
  B4 := fun i hi => by
    have hz := (h.jc i (lt_of_lt_of_le (cnt_covered hi).2 x.e_le)).1
    unfold dB4 at hz
    rw [Req.rhoC_of, if_pos hi] at hz
    have hz' : hidC t i + hidK t i - (pol.C : ℤ) ≡ 0 [ZMOD (p : ℤ)] := by simpa using hz
    have := hz'.add_right (pol.C : ℤ)
    simpa [hidOf] using this

/-- under `RFz p` at `Req.of pol x`, `Big p`, |H| ≤ 2^12 and `pol.OK`: the logits of the cells and
the policy's numbers are within the bounds `Fit` -/
theorem fit (hH : ∀ j v, |H j v| ≤ 2 ^ 12) (hpol : pol.OK) :
    Fit ppref (fun i v => Head.lg t H i v) pol where
  lg := fun i hi v _ => le_trans (lg_abs h hH hi v) (by norm_num)
  C := hpol.C
  theta := hpol.theta
  cap := hpol.cap
  V := by decide

/-- From the field relation to the relations over ℤ, under `Big p`, if |H| ≤ 2^12 and `pol.OK`. -/
theorem hrel (hH : ∀ j v, |H j v| ≤ 2 ^ 12) (hpol : pol.OK) :
    HRel (fun i v => Head.lg t H i v) pol x (hidOf t)
      ⟨K0of (fun i v => Head.lg t H i v) x (hidOf t) (K1 t (Req.of pol x)) (K2 t (Req.of pol x)),
        K1 t (Req.of pol x), K2 t (Req.of pol x), ex t⟩ :=
  HRel_of_HCong (hcong h) (fit h hH hpol) (by decide)

/-- From the field relation to the policy (`PolOK`), for the logits of the cells, under `Big p`, if
|H| ≤ 2^12 and `pol.OK`. -/
theorem polOK (hH : ∀ j v, |H j v| ≤ 2 ^ 12) (hpol : pol.OK) :
    PolOK (fun i v => Head.lg t H i v) pol x :=
  polOK_of_HRel (hrel h hH hpol) (by decide)

/-! ## 4. In the integer program's words -/

/-- under `RFz p` at `Req.of pol x`, `Big p`, `np.OK`, |H| ≤ 2^12, if the borrowed cells hold X: the
logits of the cells are the integer program's, at positions below 1,024 -/
theorem lg_stream (hn : np.OK) (hH : ∀ j v, |H j v| ≤ 2 ^ 12) {X : ℕ → Vec}
    (hx : ∀ i < nT, ∀ j < nD, xv t j i = X i j) {i : ℕ} (hi : i < nT) (v : ℕ) :
    Head.lg t H i v = dot nD (NORM.out np nD (X i)) fun j => H j v := by
  unfold dot Head.lg
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < nD := mem_range.1 hj
  rw [(norm_facts h hn hH hi).2.1 j hj',
    NORM_out_congr np nD (x := X i) (x' := xAt t i) (fun j hj => (hx i hi j hj).symm) hj']

/-- Nothing wraps around. Under `Big p`, `np.OK`, |H| ≤ 2^12 and `pol.OK`: if cells t meet the
field relation of the head modulo p at `Req.of pol x`, the stream that they hold is below 2^39 in
absolute value; and for every stream X that they hold, the final normalisation of X runs at every
position, and the policy's clauses hold of the logits of X. The logits are written as
Inst/Model/Program.lean writes them, so that the statement unfolds to the last clause of `RunsK` and
to `lgK`. -/
theorem noWrap_pol (hn : np.OK) (hH : ∀ j v, |H j v| ≤ 2 ^ 12) (hpol : pol.OK) :
    (∀ i < nT, ∀ j < nD, |xAt t i j| < 2 ^ 39) ∧
    ∀ X : ℕ → Vec, (∀ i < nT, ∀ j < nD, xv t j i = X i j) →
      (∀ pos < nT, NORM.OK np nD (X pos)) ∧
      PolOK (fun i v => dot nD (NORM.out np nD (X i)) fun j => H j v) pol x :=
  ⟨fun i hi => (norm_facts h hn hH hi).2.2,
    fun _ hx =>
      ⟨fun pos hpos =>
          (NORM_OK_congr np nD fun j hj => (hx pos hpos j hj).symm).2 (norm_facts h hn hH hpos).1,
        (polOK h hH hpol).congr (by decide) fun i hi =>
          funext fun v => lg_stream h hn hH hx hi v⟩⟩

end Pol

end Policy.LedgerHead
