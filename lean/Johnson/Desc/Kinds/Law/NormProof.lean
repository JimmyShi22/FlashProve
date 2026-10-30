-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormProof.lean.
WHAT IT DOES NOT SHOW. No more than the statement says: of the normalization's 29 forms it speaks of
17, at corners; the step from a drawn point to the corners, which has chance in it, is not here;
that a read is the sum of its cells, that a key is a row of its table and that a cell is small are
taken.
WHAT IT IS. THE PROOF OF LEMMA 1-N (HeadNormLaw.lean): from the relation on the normalization's
cells to the final normalization in integers.
THE ROAD. (1) The row's 17 forms, read in the field K at a corner, are the library's 17 identities
of a normalization's ledger (P6/NormRowLaw.lean: row_says), at the images of the position's
integer digits and sums of limb products. (2) What is 0 in K is 0 modulo the field's prime. (3) The
library's Ledger.ledger_sound, at this kind's letters: root and reciprocal are the integer
program's. (4) The keys remLow and remHigh: Site.site_high: the rounding. (5) The key clamp.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Values
import Johnson.Desc.Kinds.HeadNormLaw
import OnBytes.Desc.First.P6.NormRowLaw
import Inst.Model.Common.LedgerSound
import Inst.Model.Common.Site
import Inst.Model.Sanity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Aff Reading World)
open OnBytes.Desc.First (P6.Row P6.Row.ofDigits P6.rowProducts)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
open Inst.Model (NormPar)

variable [Sizes] [Policy] [Request] [Token]

/-- The normalization's three numbers, as the library holds them. -/
def npOf : NormPar := ⟨MF, KF, (epsF : Int)⟩

/-- The field's prime. -/
abbrev pK : Int := (Code.pGold : Int)

theorem modEq_of_cast_eq {a b : Int} (h : (a : K) = (b : K)) : a ≡ b [ZMOD pK] :=
  (CharP.intCast_eq_intCast K Code.pGold).mp h

theorem modEq_zero_of_cast {a : Int} (h : (a : K) = 0) : a ≡ 0 [ZMOD pK] :=
  modEq_of_cast_eq (by rw [h]; simp)

theorem S2_posN : 0 < S2 := by unfold S2; positivity

theorem rd_eq_zl (x i : Nat) : rd (eq (bits ls (x % S2)) i) = if i = x % S2 then 1 else 0 :=
  rd_eq_bits (n := ls) (t := x % S2) (Nat.mod_lt _ S2_posN) i

/-- A sum under a corner's weights is one term. -/
theorem rd_sum_corner {t : Nat} (ht : t < T) (g : Nat → E) :
    rd (sumTo T fun t' => eq (bits lt t) t' * g t') = rd (g t) := by
  rw [rd_sumTo, Finset.sum_eq_single t]
  · rw [rd_mul, rd_eq_bits (n := lt) ht, if_pos rfl, one_mul]
  · intro b _ hb
    rw [rd_mul, rd_eq_bits (n := lt) ht, if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr ht) h

/-! ## The classes, filled -/

section Filled
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- What HeadNormLaw.lean's fillings say of the classes' fields. -/
structure FilledN (c : NCells) : Prop where
  hentry : ∀ r i, FinalNorm.entry r i = ((readAtN c r.of i : E) : Form)
  hwide : ∀ i, FinalNorm.wide i = ((sumTo S2 fun j => sumTo T fun t =>
    eq FinalNorm.zl j * eq FinalNorm.zt t * ofInt (c.cell .wide (S2 * i + j) t) : E) : Form)
  hW : ∀ s, s < 9 → (Norm.W.getD s {}).var =
    ((sumTo T fun t => eq Norm.pV t * ofInt (wsqZ c t s) : E) : Form)
  hP : ∀ n, n < 7 → (Norm.P.getD n {}).var =
    ((sumTo T fun t => eq Norm.pV t * prodE c t n : E) : Form)
  hclaimed : FinalNorm.normed.claimed.var = ((trueNormed c : E) : Form)
  hew : ∀ k x, FinalNorm.ew k x = FinalNorm.ewh k (x / S2) * eq FinalNorm.zl (x % S2)
  hwsum : ∀ k, FinalNorm.wsum k = sumTo (lenN k) fun x => FinalNorm.ew k x

variable {c : NCells} {t : Nat}

/-- The images of a position's digits. -/
def dK (c : NCells) (t : Nat) : Nat → K := fun n => ((digZ c t n : Int) : K)

/-- A digit of the row, read at pV, at the corner of t. -/
theorem cv_digit (hF : FilledN c) (hpV : Norm.pV = bits lt t) (ht : t < T) (j : Nat) :
    cv (Norm.digit .rowsAtPV 0 j) = dK c t j := by
  show cv (HAdd.hAdd (α := Form) (β := Nat) (γ := Form) (FinalNorm.entry .rowAtPV j) off1) = _
  rw [cv_addN, hF.hentry, cv_coe]
  show rd (sumTo T fun t' => eq Norm.pV t' * ofInt (c.cell .row j t')) + _ = _
  rw [hpV, rd_sum_corner ht, rd_ofInt]
  unfold dK digZ off1
  push_cast
  ring

/-- The same digits as constants: the row "in truth". -/
theorem dv_rowZ (c : NCells) (t : Nat) :
    OnBytes.Desc.First.P6.dv Reading.gl W0 (fun j => ((ofInt (digZ c t j) : E) : Form)) =
      dK c t := by
  funext n
  show cv ((ofInt (digZ c t n) : E) : Form) = _
  rw [cv_coe, rd_ofInt]
  rfl

theorem rd_fieldE (c : NCells) (t : Nat) :
    rd (fieldE c t 0) = Inst.Model.Ledger.sa (dK c t) ∧
    rd (fieldE c t 1) = Inst.Model.Ledger.sb (dK c t) ∧
    rd (fieldE c t 2) = Inst.Model.Ledger.Rlo (dK c t) ∧
    rd (fieldE c t 3) = Inst.Model.Ledger.Rhi (dK c t) := by
  have h := OnBytes.Desc.First.P6.fields_value Reading.gl W0
    (fun j => ((ofInt (digZ c t j) : E) : Form))
  rw [dv_rowZ] at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h.1]; exact (cv_const _).symm
  · rw [← h.2.1]; exact (cv_const _).symm
  · rw [← h.2.2.1]; exact (cv_const _).symm
  · rw [← h.2.2.2]; exact (cv_const _).symm

theorem rd_prodE (c : NCells) (t : Nat) {n : Nat} (hn : n < 7) :
    rd (prodE c t n) = Inst.Model.Ledger.prods (dK c t) n := by
  obtain ⟨ha, hb, hl, hh⟩ := rd_fieldE c t
  unfold prodE
  rw [rd_mul]
  interval_cases n <;>
    simp only [P6.rowProducts, List.getD_cons_zero, List.getD_cons_succ, ha, hb, hl, hh,
      Inst.Model.Ledger.prods, Inst.Model.Ledger.prodsOf] <;> ring

/-- The row's 17 forms, as the part's three lists. -/
theorem rowForms_eq :
    Norm.rowForms =
      OnBytes.Desc.First.P6.carries (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
        (Norm.digit .rowsAtPV 0) (fun s => (Norm.W.getD (9 * 0 + s) {}).var) ++
      OnBytes.Desc.First.P6.lines (P6.Row.ofDigits (Norm.digit .rowsAtPV 0))
        (fun n => (Norm.P.getD (7 * 0 + n) {}).var) ((epsF : Nat) : E)
        ((2 ^ (MF + 1) : Nat) : Form) := by
  simp [Norm.rowForms, Norm.rowAt, OnBytes.Desc.First.P6.lines, Norm.NI, Norm.epsF, Norm.MF,
    List.range_succ]

/-- **(1)** At the corner of t the 17 forms' being 0 is the library's 17 identities, in K. -/
theorem idn_K (hF : FilledN c) (hpV : Norm.pV = bits lt t) (ht : t < T)
    (h0 : ∀ f ∈ Norm.rowForms, cv f = 0) (k : Nat) :
    Inst.Model.Ledger.idn npOf (fun s => ((wsqZ c t s : Int) : K)) (dK c t) k = 0 := by
  have hD : OnBytes.Desc.First.P6.dv Reading.gl W0 (Norm.digit .rowsAtPV 0) = dK c t := by
    funext n
    exact cv_digit hF hpV ht n
  have key := OnBytes.Desc.First.P6.row_says Reading.gl W0 (Norm.digit .rowsAtPV 0)
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
    (fun f hf => h0 f (by rw [rowForms_eq]; exact List.mem_append_left _ hf))
    (fun f hf => h0 f (by rw [rowForms_eq]; exact List.mem_append_right _ hf))
    (fun j hj => by
      show cv (Norm.P.getD (7 * 0 + j) {}).var = _
      rw [hD, Nat.mul_zero, Nat.zero_add, hF.hP j hj, cv_coe, hpV, rd_sum_corner ht,
        rd_prodE c t hj])
    k
  rw [hD] at key
  by_cases hk : k < 9
  · rw [Inst.Model.Ledger.idn_j1 npOf _ _ hk] at key ⊢
    have hw : OnBytes.Desc.First.P6.dv Reading.gl W0
        (fun s => (Norm.W.getD (9 * 0 + s) {}).var) k = ((wsqZ c t k : Int) : K) := by
      show cv (Norm.W.getD (9 * 0 + k) {}).var = _
      rw [Nat.mul_zero, Nat.zero_add, hF.hW k hk, cv_coe, hpV, rd_sum_corner ht, rd_ofInt]
    rw [hw] at key
    exact key
  · have e : ∀ Ws Ws' : Nat → K, Inst.Model.Ledger.idn npOf Ws (dK c t) k =
        Inst.Model.Ledger.idn npOf Ws' (dK c t) k := by
      intro Ws Ws'
      unfold Inst.Model.Ledger.idn
      rw [if_neg hk, if_neg hk]
    rw [e _ _]
    exact key

/-! ## The keys at a corner -/

/-- The classes stand at the corner of entry x and position t. -/
structure AtCornerN (x t : Nat) : Prop where
  hzt : FinalNorm.zt = bits lt t
  hzl : FinalNorm.zl = bits ls (x % S2)
  hewh : ∀ k i, FinalNorm.ewh k i = if i == x / S2 then 1 else 0

variable {x : Nat}

theorem rd_ewN (hF : FilledN c) (hC : AtCornerN x t) (k : FinalNorm.Key) (x' : Nat) :
    rd (FinalNorm.ew k x') = if x' = x then 1 else 0 := by
  rw [hF.hew, rd_mul, hC.hewh, hC.hzl, rd_eq_zl]
  by_cases h : x' = x
  · subst h
    simp [rd_one]
  · rw [if_neg h]
    by_cases h1 : x' / S2 = x / S2
    · have h2 : ¬ x' % S2 = x % S2 := fun h2 => h (by
        rw [← Nat.div_add_mod x' S2, ← Nat.div_add_mod x S2, h1, h2])
      rw [if_neg h2, mul_zero]
    · have : (x' / S2 == x / S2) = false := by simpa using h1
      rw [this]
      simp [rd_zero]

theorem sum_ewN (hF : FilledN c) (hC : AtCornerN x t) (k : FinalNorm.Key) {n : Nat} (hx : x < n)
    (Z : Nat → K) : ((Finset.range n).sum fun x' => rd (FinalNorm.ew k x') * Z x') = Z x := by
  rw [Finset.sum_eq_single x]
  · rw [rd_ewN hF hC, if_pos rfl, one_mul]
  · intro b _ hb
    rw [rd_ewN hF hC, if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_range.mpr hx) h

theorem rd_wsumN (hF : FilledN c) (hC : AtCornerN x t) (k : FinalNorm.Key) (hx : x < lenN k) :
    rd (FinalNorm.wsum k) = 1 := by
  rw [hF.hwsum, rd_sumTo]
  have := sum_ewN hF hC k hx fun _ => (1 : K)
  simpa using this

/-- An entry of the head's wide read at the corner: one cell. -/
theorem cv_wideN (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (i : Nat) :
    cv (FinalNorm.wide i) = ((c.cell .wide (S2 * i + x % S2) t : Int) : K) := by
  rw [hF.hwide, cv_coe, rd_sumTo, Finset.sum_eq_single (x % S2)]
  · rw [rd_sumTo, Finset.sum_eq_single t]
    · rw [rd_mul, rd_mul, hC.hzl, hC.hzt, rd_eq_zl,
        rd_eq_bits (n := lt) ht, if_pos rfl, if_pos rfl, rd_ofInt]
      ring
    · intro b _ hb
      rw [rd_mul, rd_mul, hC.hzt, rd_eq_bits (n := lt) ht, if_neg hb]
      ring
    · intro h
      exact absurd (Finset.mem_range.mpr ht) h
  · intro b _ hb
    rw [rd_sumTo]
    refine Finset.sum_eq_zero fun t' _ => ?_
    rw [rd_mul, rd_mul, hC.hzl, rd_eq_zl, if_neg hb]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.mod_lt _ S2_posN)) h

/-- Two limbs of the wide matrix from feature f0 on, at the corner. -/
theorem cv_wideAtN (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (hd : S2 ∣ d) (hx : x < d)
    (k : FinalNorm.Key) (f0 : Nat) (hf : S2 ∣ f0) :
    cv (FinalNorm.wideAt k f0) =
      ((c.cell .wide (f0 + x) t + 256 * c.cell .wide (f0 + d + x) t : Int) : K) := by
  have hlt : x / S2 < d / S2 := Nat.div_lt_div_of_lt_of_dvd hd hx
  unfold FinalNorm.wideAt
  rw [cv_sumTo, Finset.sum_eq_single (x / S2)]
  · rw [cv_sumTo, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      cv_smulE, cv_smulE, rd_mul, rd_mul, rd_pow, rd_pow, rd_ofNat, hC.hewh, cv_wideN hF hC ht,
      cv_wideN hF hC ht]
    have e0 : S2 * ((f0 + 0 * d) / S2 + x / S2) + x % S2 = f0 + x := by
      rw [Nat.zero_mul, Nat.add_zero, Nat.mul_add, Nat.mul_div_cancel' hf, Nat.add_assoc,
        Nat.div_add_mod]
    have e1 : S2 * ((f0 + 1 * d) / S2 + x / S2) + x % S2 = f0 + d + x := by
      rw [Nat.one_mul, Nat.mul_add, Nat.mul_div_cancel' (Dvd.dvd.add hf hd), Nat.add_assoc,
        Nat.div_add_mod]
    rw [e0, e1]
    simp [rd_one]
  · intro b _ hb
    rw [cv_sumTo]
    refine Finset.sum_eq_zero fun l _ => ?_
    have : (b == x / S2) = false := by simpa using hb
    rw [cv_smulE, rd_mul, hC.hewh, this]
    simp [rd_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr hlt) h

/-- The rounded quotient, the remainder's high part, and the reciprocal, in integers. -/
def awZ (c : NCells) (t x : Nat) : Int := c.cell .wide x t + 256 * c.cell .wide (d + x) t
def remZ (c : NCells) (t x : Nat) : Int :=
  c.cell .wide (2 * d + x) t + 256 * c.cell .wide (2 * d + d + x) t + 32896
def recZ (c : NCells) (t : Nat) : Int := Inst.Model.Ledger.R (digZ c t)

theorem rd_R (c : NCells) (t : Nat) : rd (rowZ c t).R.const = ((recZ c t : Int) : K) := by
  rw [← cv_const]
  show Aff.value Reading.gl W0
    ((rowZ c t).Rlo + OnBytes.Desc.First.P6.sm (2 ^ 24) (rowZ c t).Rhi) = _
  rw [Aff.value_add, OnBytes.Desc.First.P6.sm_value]
  unfold rowZ
  rw [OnBytes.Desc.First.P6.Rlo_value, OnBytes.Desc.First.P6.Rhi_value, dv_rowZ]
  unfold recZ
  have := Inst.Model.Ledger.map_R (Int.castRingHom K) (digZ c t)
  simp only [eq_intCast] at this
  rw [this]
  unfold Inst.Model.Ledger.R dK
  push_cast
  ring

theorem rd_trueNormed (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (hx : x < d) :
    rd (trueNormed c) = ((str c t x * recZ c t : Int) : K) := by
  unfold trueNormed
  rw [hC.hzt, rd_sumTo, Finset.sum_eq_single t]
  · rw [rd_sumTo]
    have := sum_ewN hF hC .remLow hx fun x' => ((str c t x' * recZ c t : Int) : K)
    rw [← this]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [rd_mul, rd_mul, rd_mul, rd_eq_bits (n := lt) ht, if_pos rfl, rd_ofInt, rd_R]
    push_cast
    ring
  · intro b _ hb
    rw [rd_sumTo]
    refine Finset.sum_eq_zero fun x' _ => ?_
    rw [rd_mul, rd_mul, rd_eq_bits (n := lt) ht, if_neg hb]
    ring
  · intro h
    exact absurd (Finset.mem_range.mpr ht) h

theorem cv_remLow (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (hd : S2 ∣ d) (hx : x < d) :
    cv (FinalNorm.key 21 .remLow) =
      ((Inst.Model.Site.site (str c t x * recZ c t) (awZ c t x) (remZ c t x) KF : Int) : K) := by
  unfold FinalNorm.key
  rw [cv_sub, cv_sub, cv_addE, cv_smulN, cv_smulN, hF.hclaimed, cv_coe,
    rd_trueNormed hF hC ht hx, rd_mul, rd_wsumN hF hC .remLow hx, rd_sub, rd_natCast, rd_natCast,
    cv_wideAtN hF hC ht hd hx .remLow 0 (Nat.dvd_zero _),
    cv_wideAtN hF hC ht hd hx .remLow (2 * d) (Dvd.dvd.mul_left hd 2)]
  unfold Inst.Model.Site.site awZ remZ off2
  simp only [Nat.zero_add]
  push_cast
  ring

theorem cv_remHigh (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (hd : S2 ∣ d) (hx : x < d) :
    cv (FinalNorm.key 21 .remHigh) =
      ((Inst.Model.Site.high (remZ c t x) KF 32 : Int) : K) := by
  unfold FinalNorm.key
  rw [cv_smulN, cv_Eadd, rd_nmul, rd_wsumN hF hC .remHigh hx,
    cv_wideAtN hF hC ht hd hx .remHigh (2 * d) (Dvd.dvd.mul_left hd 2)]
  unfold Inst.Model.Site.high remZ off2
  push_cast
  ring

theorem cv_entry_short (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (r : FinalNorm.Read)
    (m : FinalNorm.Matrix) (hr : r.of = (m, .short (eq FinalNorm.zt))) (i : Nat) :
    cv (FinalNorm.entry r i) = ((c.of m i t : Int) : K) := by
  rw [hF.hentry, cv_coe, hr]
  show rd (sumTo T fun t' => eq FinalNorm.zt t' * ofInt (c.of m i t')) = _
  rw [hC.hzt, rd_sum_corner ht, rd_ofInt]

theorem cv_clamp (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (hd : S2 ∣ d) (hx : x < d) :
    cv (FinalNorm.key 21 .clamp) =
      (((awZ c t x + 2 ^ 15) + 2 ^ 28 * (act c.toCells t x + 2 ^ 11) : Int) : K) := by
  unfold FinalNorm.key
  rw [cv_addE, cv_add, cv_smulN, cv_sumTo, rd_muln, rd_wsumN hF hC .clamp hx,
    cv_wideAtN hF hC ht hd hx .clamp 0 (Nat.dvd_zero _)]
  have h1 : ((Finset.range d).sum fun k =>
      cv (FinalNorm.ew .clamp k • FinalNorm.actAt (FinalNorm.entry .actAtKeys) k)) =
      ((act c.toCells t x : Int) : K) := by
    rw [← sum_ewN hF hC .clamp hx fun k => ((act c.toCells t k : Int) : K)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cv_smulE]
    unfold FinalNorm.actAt
    rw [cv_add, cv_smulN, cv_entry_short hF hC ht .actAtKeys .act rfl,
      cv_entry_short hF hC ht .actAtKeys .act rfl]
    unfold act NCells.of
    push_cast
    ring
  rw [h1]
  unfold awZ
  simp only [Nat.zero_add]
  push_cast
  ring

theorem cv_digitsKey (hF : FilledN c) (hC : AtCornerN x t) (ht : t < T) (hx : x < NR + 21) :
    cv (FinalNorm.key 21 .digits) = (((mul x : Int) * digZ c t x : Int) : K) := by
  unfold FinalNorm.key
  rw [cv_sumTo, ← sum_ewN hF hC .digits hx fun j => (((mul j : Int) * digZ c t j : Int) : K)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cv_smulE, rd_mul, rd_natCast, cv_add, cv_natCast,
    cv_entry_short hF hC ht .rowAtKeys .row rfl]
  unfold digZ NCells.of off1
  push_cast
  ring

end Filled

/-! ## The classes at the cells and a point -/

theorem filledN_at (c : NCells) (p : NPt) (pV : Point) :
    letI := p.normIn; letI := normHeardAt c pV; letI := finalHeardAt c
    letI := normReadsAtCells c
    FilledN c :=
  letI := p.normIn; letI := normHeardAt c pV; letI := finalHeardAt c
  letI := normReadsAtCells c
  ⟨fun _ _ => rfl, fun _ => rfl,
    fun s hs => by interval_cases s <;> rfl, fun n hn => by interval_cases n <;> rfl,
    rfl, fun _ _ => rfl, fun _ => rfl⟩

theorem atCornerN_at (x t : Nat) : letI := (cornerN x t).normIn; AtCornerN x t :=
  letI := (cornerN x t).normIn
  ⟨rfl, rfl, fun _ _ => rfl⟩

section Wrap
variable {c : NCells} {x t : Nat}

theorem rd_keyN_remLow (ht : t < T) (hd : S2 ∣ d) (hx : x < d) :
    rd (keyNAt c (cornerN x t) .remLow) =
      ((Inst.Model.Site.site (str c t x * recZ c t) (awZ c t x) (remZ c t x) KF : Int) : K) := by
  letI := (cornerN x t).normIn; letI := normHeardAt c (cornerN x t).zt; letI := finalHeardAt c
  letI := normReadsAtCells c
  show rd (FinalNorm.key 21 .remLow).const = _
  rw [← cv_const, cv_remLow (filledN_at c (cornerN x t) _) (atCornerN_at x t) ht hd hx]

theorem rd_keyN_remHigh (ht : t < T) (hd : S2 ∣ d) (hx : x < d) :
    rd (keyNAt c (cornerN x t) .remHigh) =
      ((Inst.Model.Site.high (remZ c t x) KF 32 : Int) : K) := by
  letI := (cornerN x t).normIn; letI := normHeardAt c (cornerN x t).zt; letI := finalHeardAt c
  letI := normReadsAtCells c
  show rd (FinalNorm.key 21 .remHigh).const = _
  rw [← cv_const, cv_remHigh (filledN_at c (cornerN x t) _) (atCornerN_at x t) ht hd hx]

theorem rd_keyN_clamp (ht : t < T) (hd : S2 ∣ d) (hx : x < d) :
    rd (keyNAt c (cornerN x t) .clamp) =
      (((awZ c t x + 2 ^ 15) + 2 ^ 28 * (act c.toCells t x + 2 ^ 11) : Int) : K) := by
  letI := (cornerN x t).normIn; letI := normHeardAt c (cornerN x t).zt; letI := finalHeardAt c
  letI := normReadsAtCells c
  show rd (FinalNorm.key 21 .clamp).const = _
  rw [← cv_const, cv_clamp (filledN_at c (cornerN x t) _) (atCornerN_at x t) ht hd hx]

theorem rd_keyN_digits (ht : t < T) (hx : x < NR + 21) :
    rd (keyNAt c (cornerN x t) .digits) = (((mul x : Int) * digZ c t x : Int) : K) := by
  letI := (cornerN x t).normIn; letI := normHeardAt c (cornerN x t).zt; letI := finalHeardAt c
  letI := normReadsAtCells c
  show rd (FinalNorm.key 21 .digits).const = _
  rw [← cv_const, cv_digitsKey (filledN_at c (cornerN x t) _) (atCornerN_at x t) ht hx]

/-- **(1), (2)** The 17 identities, modulo the field's prime, in integers. -/
theorem idn_modEq (ht : t < T) (h0 : ∀ v, v ∈ rowsAt c (bits lt t) → v = 0) (k : Nat) :
    Inst.Model.Ledger.idn npOf (Inst.Model.Ledger.Wsum d (limbZ c t)) (digZ c t) k
      ≡ 0 [ZMOD pK] := by
  letI := (cornerN 0 0).normIn; letI := normHeardAt c (bits lt t); letI := finalHeardAt c
  letI := normReadsAtCells c
  have hK := idn_K (filledN_at c (cornerN 0 0) (bits lt t)) rfl ht
    (fun f hf => by
      rw [cv_const, h0 f.const (List.mem_map.mpr ⟨f, hf, rfl⟩), rd_zero]) k
  apply modEq_zero_of_cast
  have hm := Inst.Model.Ledger.map_idn (Int.castRingHom K) (digZ c t) npOf
    (Inst.Model.Ledger.Wsum d (limbZ c t)) k
  simp only [eq_intCast] at hm
  rw [hm]
  have hw : (fun s => ((Inst.Model.Ledger.Wsum d (limbZ c t) s : Int) : K)) =
      fun s => ((wsqZ c t s : Int) : K) := by
    funext s
    congr 1
    unfold Inst.Model.Ledger.Wsum wsqZ
    rw [sumZ_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sumZ_eq]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sumZ_eq]
  rw [hw]
  exact hK

end Wrap

/-! ## What the tests on the plan say of the normalization -/

structure PlanN : Prop where
  hM24 : 24 ≤ MF
  hM47 : MF ≤ 47
  hMK : MF ≤ KF + 14
  hK17 : 17 ≤ KF
  hK32 : KF ≤ 32
  he1 : 1 ≤ epsF
  he48 : epsF < 2 ^ 48
  hdS : d % S2 = 0
  hled : 5 * d * (2 ^ 18) ^ 2 < 2 ^ 53

theorem planN {sT : Nat} (h : planOk sT = true) : PlanN := by
  unfold planOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨_, hr⟩, hn⟩ := h
  unfold Sizes.ranges at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, _⟩, h7⟩, h8⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩,
    hd⟩, _⟩, _⟩ := hr
  unfold noOverflow at hn
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hled, _⟩ := hn
  have hled' := of_decide_eq_true hled
  unfold Ty at hled'
  exact ⟨by simpa using h1, by simpa using h2, by simpa using h3, by simpa using h4,
    by simpa using h5, by simpa using h7, by simpa using h8, by simpa using hd, hled'⟩

theorem pK_eq : pK = 18446744069414584321 := by
  unfold pK
  rw [Code.pGold_eq]
  norm_num

theorem admN (P : PlanN) : Inst.Model.Ledger.Adm pK npOf d (2 ^ 18) := by
  have h1 := P.he1
  have h2 := P.he48
  have h3 := P.hled
  refine ⟨?_, ?_, P.hM47, by norm_num, ?_, ?_, ?_⟩
  · show (1 : Int) ≤ (epsF : Int)
    exact_mod_cast h1
  · show (epsF : Int) < 2 ^ 48
    exact_mod_cast h2
  · rw [pK_eq]; norm_num
  · rw [pK_eq]
    have : (5 * (d : Int) * (2 ^ 18) ^ 2) < 2 ^ 53 := by exact_mod_cast h3
    nlinarith
  · rw [pK_eq]; norm_num

/-! ## The lemma -/

theorem mul_eq_mu (n : Nat) : ((mul n : Nat) : Int) = Inst.Model.Ledger.mu n := by
  unfold mul Inst.Model.Ledger.mu
  by_cases h9 : n = 9
  · subst h9; rfl
  by_cases h58 : n = 58
  · subst h58; rfl
  by_cases h59 : n = 59
  · subst h59; rfl
  by_cases h63 : n = 63
  · subst h63; rfl
  by_cases h76 : n = 76
  · subst h76; rfl
  by_cases h79 : n = 79
  · subst h79; rfl
  simp [h9, h58, h59, h63, h76, h79]

theorem inBits_modEq {w : Nat} {v : E} {z : Int} (h : InBits w v) (hv : rd v = (z : K)) :
    ∃ u : Int, 0 ≤ u ∧ u < 2 ^ w ∧ z ≡ u [ZMOD pK] := by
  obtain ⟨n, hn, rfl⟩ := h
  refine ⟨(n : Int), Int.natCast_nonneg n, by exact_mod_cast hn, modEq_of_cast_eq ?_⟩
  rw [← hv, rd_natCast, Int.cast_natCast]

theorem abs_lt_of_natAbs {z : Int} {B : Nat} (h : z.natAbs < B) : |z| < (B : Int) := by
  rw [Int.abs_eq_natAbs]
  exact_mod_cast h

theorem lemma1N : Lemma1NStatement := by
  intro _ _ _ _ sT c hplan h t ht
  have P := planN hplan
  have hdS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hp := pK_eq
  have cellB : ∀ m f, |c.cell m f t| < 2 ^ 18 := fun m f => by
    have := abs_lt_of_natAbs (h.small m f t)
    exact_mod_cast this
  have hb : ∀ l < 5, ∀ j < d, |limbZ c t l j| ≤ 2 ^ 18 := fun l _ j _ => by
    have := abs_lt_of_natAbs (h.smallS (l * d + j) t)
    exact le_of_lt (by exact_mod_cast this)
  have hD : ∀ n < 99, |digZ c t n - 128| ≤ 2 ^ 18 := fun n _ => by
    unfold digZ
    rw [add_sub_cancel_right]
    exact le_of_lt (cellB .row n)
  have hk : ∀ n < 99, ∃ u : Int, 0 ≤ u ∧ u < 256 ∧
      Inst.Model.Ledger.mu n * digZ c t n ≡ u [ZMOD pK] := fun n hn => by
    obtain ⟨u, h0, h1, h2⟩ := inBits_modEq (h.digits t ht n (by unfold NR; omega))
      (rd_keyN_digits (c := c) ht (by unfold NR; omega))
    rw [mul_eq_mu] at h2
    exact ⟨u, h0, by norm_num at h1; exact h1, h2⟩
  obtain ⟨-, hV, hsig, hR, hV78, hs1, hs39, hx, hxR⟩ :=
    Inst.Model.Ledger.ledger_sound (admN P) hb hD hk fun k _ => idn_modEq ht (h.rows t ht) k
  have hstr : ∀ j, Inst.Model.Ledger.xOf (limbZ c t) j = str c t j := fun j => by
    unfold Inst.Model.Ledger.xOf str
    rw [sumZ_eq]
  have hvsq : Inst.Model.NORM.V d (Inst.Model.Ledger.xOf (limbZ c t)) = vsq c t := by
    unfold Inst.Model.NORM.V vsq
    rw [sumZ_eq]
    exact Finset.sum_congr rfl fun j _ => by rw [hstr, sq]
  have hv0 : 0 ≤ vsq c t + (epsF : Int) := by
    have h1 : 0 ≤ vsq c t := by
      rw [← hvsq]
      unfold Inst.Model.NORM.V
      exact Finset.sum_nonneg fun j _ => sq_nonneg _
    positivity
  have hroot := Inst.Model.isqrt_spec hv0
  have hsig' : Inst.Model.Ledger.sig (digZ c t) = Inst.Model.isqrt (vsq c t + (epsF : Int)) := by
    rw [hsig]
    unfold Inst.Model.NORM.sig
    rw [hvsq]
    rfl
  refine ⟨Inst.Model.Ledger.sig (digZ c t), hs1, ?_, ?_, ?_, fun k hk' => ⟨awZ c t k, ?_⟩⟩
  · rw [hsig', ← sq]; exact hroot.2.1
  · rw [hsig', ← sq]; exact hroot.2.2
  · rw [← hvsq]; exact hV78
  · -- the clamp first: the quotient fits 16 bits
    obtain ⟨u, hu, hkey⟩ := h.clamp t ht k hk'
    have a1 := abs_lt.mp (cellB .wide k)
    have a2 := abs_lt.mp (cellB .wide (d + k))
    have a3 := abs_lt.mp (cellB .act k)
    have a4 := abs_lt.mp (cellB .act (d + k))
    have a5 := abs_lt.mp (cellB .wide (2 * d + k))
    have a6 := abs_lt.mp (cellB .wide (2 * d + d + k))
    have hu' : (u : Int) < 65536 := by exact_mod_cast hu
    have hu0 : (0 : Int) ≤ u := Int.natCast_nonneg u
    have hc : -2047 ≤ clampZ ((u : Int) - 2 ^ 15) ∧ clampZ ((u : Int) - 2 ^ 15) ≤ 2047 := by
      unfold clampZ
      omega
    have hcong : (awZ c t k + 2 ^ 15) + 2 ^ 28 * (act c.toCells t k + 2 ^ 11) ≡
        (u : Int) + 2 ^ 28 * (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11) [ZMOD pK] := by
      apply modEq_of_cast_eq
      obtain ⟨m, hm⟩ : ∃ m : Nat, (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11).toNat = m := ⟨_, rfl⟩
      have hm' : clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11 = (m : Int) := by
        rw [← hm]
        exact (Int.toNat_of_nonneg (by omega)).symm
      rw [← rd_keyN_clamp ht hdS hk', hkey, hm, rd_natCast, hm']
      push_cast
      ring
    have e : (awZ c t k + 2 ^ 15) + 2 ^ 28 * (act c.toCells t k + 2 ^ 11) =
        (u : Int) + 2 ^ 28 * (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11) :=
      Inst.Model.Ledger.lift_eq hcong (by
        rw [abs_lt, hp]
        unfold awZ act
        constructor <;> omega)
    have e1 : awZ c t k + 2 ^ 15 = u := by
      unfold awZ act at e
      unfold awZ
      omega
    have e2 : act c.toCells t k = clampZ ((u : Int) - 2 ^ 15) := by
      unfold awZ act at e
      unfold awZ at e1
      unfold act
      omega
    have hfit : |awZ c t k| ≤ 2 ^ 15 := by
      rw [abs_le]
      constructor <;> omega
    -- the rounding
    have p1 : (2 : Int) ^ MF ≤ 2 ^ 47 := pow_le_pow_right₀ (by norm_num) P.hM47
    have p2 : (2 : Int) ^ (32 - KF) ≤ 2 ^ 15 :=
      pow_le_pow_right₀ (by norm_num) (by have := P.hK17; omega)
    have p3 : (2 : Int) ^ (KF - 1) ≤ 2 ^ 31 :=
      pow_le_pow_right₀ (by norm_num) (by have := P.hK32; omega)
    have p4 : (2 : Int) ^ KF ≤ 2 ^ 32 := pow_le_pow_right₀ (by norm_num) P.hK32
    have hrem : |remZ c t k| ≤ 67403904 := by
      rw [abs_le]
      unfold remZ
      constructor <;> omega
    have hA : |str c t k * recZ c t| ≤ 2 ^ 47 + 2 ^ 38 := by
      have := hxR k hk'
      rw [hstr] at this
      have h2 : (2 : Int) ^ npOf.M = 2 ^ MF := rfl
      rw [h2] at this
      exact le_of_lt (lt_of_lt_of_le this (by linarith))
    have hpH : (2 : Int) ^ (32 - KF) * 67403904 + 2 ^ 16 ≤ pK := by
      have h1 := mul_le_mul_of_nonneg_right p2 (show (0 : Int) ≤ 67403904 by norm_num)
      rw [hp]
      norm_num at h1 ⊢
      linarith
    have hpL : (2 : Int) ^ 47 + 2 ^ 38 + 2 ^ (KF - 1) + 2 ^ KF * 2 ^ 15 + 2 ^ 16 * 67403904 + 2 ^ 16
        ≤ pK := by
      have h1 := mul_le_mul_of_nonneg_right p4 (show (0 : Int) ≤ 2 ^ 15 by norm_num)
      rw [hp]
      norm_num at h1 p3 ⊢
      linarith
    have hq := Inst.Model.Site.site_high (p := pK) (k := KF) (top := 32) (w := 16) rfl
      (by have := P.hK17; omega) P.hK32 hA hfit hrem hpH hpL
      (inBits_modEq (h.remHigh t ht k hk') (rd_keyN_remHigh ht hdS hk'))
      (inBits_modEq (h.remLow t ht k hk') (rd_keyN_remLow ht hdS hk'))
    have hrec : recZ c t =
        (2 ^ MF + Inst.Model.Ledger.sig (digZ c t) / 2) / Inst.Model.Ledger.sig (digZ c t) := by
      unfold recZ
      rw [hR]
      unfold Inst.Model.NORM.R
      rw [← hsig]
      rfl
    refine ⟨?_, by omega, by omega, ?_⟩
    · rw [← hrec, hq.1]
      rfl
    · rw [e2, ← e1]
      congr 1
      ring

/-- **The same in the words of the library's integer program**: at every position NORM goes on, and
act is its output on the stream that the cells hold. -/
theorem lemma1N_program [Sizes] [Policy] [Request] [Token] (sT : Nat) (c : NCells)
    (hplan : planOk sT = true) (h : CellRelN c) {t : Nat} (ht : t < T) :
    Inst.Model.NORM.OK npOf d (str c t) ∧
      ∀ k, k < d → act c.toCells t k = Inst.Model.NORM.out npOf d (str c t) k := by
  obtain ⟨sig, hs1, hlo, hhi, h78, hk⟩ := lemma1N sT c hplan h t ht
  have hV : Inst.Model.NORM.V d (str c t) = vsq c t := by
    unfold Inst.Model.NORM.V vsq
    rw [sumZ_eq]
    exact Finset.sum_congr rfl fun j _ => sq _
  have hsig : Inst.Model.NORM.sig npOf d (str c t) = sig := by
    unfold Inst.Model.NORM.sig
    rw [hV]
    exact Inst.Model.Ledger.isqrt_eq (by omega) hlo hhi
  have hyw : ∀ k, Inst.Model.NORM.yw npOf d (str c t) k =
      (str c t k * ((2 ^ MF + sig / 2) / sig) + 2 ^ (KF - 1)) / 2 ^ KF := fun k => by
    unfold Inst.Model.NORM.yw Inst.Model.NORM.R Inst.Model.rhu
    rw [hsig]
    rfl
  refine ⟨⟨by rw [hV]; exact h78, fun k hk' => ?_⟩, fun k hk' => ?_⟩
  · obtain ⟨aw, e, h1, h2, _⟩ := hk k hk'
    rw [hyw, ← e]
    exact ⟨h1, h2⟩
  · obtain ⟨aw, e, _, _, h3⟩ := hk k hk'
    unfold Inst.Model.NORM.out
    rw [hyw, ← e, h3]
    rfl

/-- What Lemma 1 (HeadLaw.lean) takes of the activations, at the positions and features that there
are. -/
theorem act_le [Sizes] [Policy] [Request] [Token] (sT : Nat) (c : NCells)
    (hplan : planOk sT = true) (h : CellRelN c) {t k : Nat} (ht : t < T) (hk : k < d) :
    (act c.toCells t k).natAbs ≤ 2047 := by
  obtain ⟨_, _, _, _, _, hk'⟩ := lemma1N sT c hplan h t ht
  obtain ⟨aw, _, _, _, h3⟩ := hk' k hk
  rw [h3]
  unfold clampZ
  omega

/-- The head's 21 digits are bytes: the key digits at its entries from NR on. -/
theorem bytes_of_digits [Sizes] [Policy] [Request] [Token] {c : NCells} (h : CellRelN c) {t : Nat}
    (ht : t < T) {j : Nat} (hj : j < 21) :
    0 ≤ c.cell .row (NR + j) t + 128 ∧ c.cell .row (NR + j) t + 128 < 256 := by
  obtain ⟨u, h0, h1, h2⟩ := inBits_modEq (h.digits t ht (NR + j) (by omega))
    (rd_keyN_digits (c := c) ht (by omega))
  have hm : ((mul (NR + j) : Nat) : Int) = 1 := by
    unfold mul NR
    have : ∀ a : Nat, a < 99 → (99 + j == a) = false := fun a ha => by simp; omega
    simp [this]
  rw [hm, one_mul] at h2
  have hb := abs_lt.mp (abs_lt_of_natAbs (h.small .row (NR + j) t))
  have e : digZ c t (NR + j) = u := Inst.Model.Ledger.lift_eq h2 (by
    rw [abs_lt, pK_eq]
    unfold digZ
    push_cast at hb
    constructor <;> omega)
  unfold digZ at e
  norm_num at h1
  omega

/-- THE TIE OF THE TWO TEXTS: HeadLaw.lean's relation is its two clauses small and bytes with
CellRelH: should either structure turn, this stops compiling. -/
theorem cellRel_iff [Sizes] [Policy] [Request] [Token] (c : Cells) (tab : Nat → Nat) :
    CellRel c tab ↔
      (∀ m f t, (c.cell m f t).natAbs < 2 ^ 18) ∧
      (∀ t, t < T → ∀ j, j < 21 →
        0 ≤ c.cell .row (NR + j) t + 128 ∧ c.cell .row (NR + j) t + 128 < 256) ∧
      CellRelH c tab :=
  ⟨fun h => ⟨h.small, h.bytes, ⟨h.top, h.mid, h.low, h.rowA, h.rowB, h.lines, h.sums⟩⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.top, h.2.2.mid, h.2.2.low, h.2.2.rowA, h.2.2.rowB, h.2.2.lines,
      h.2.2.sums⟩⟩

/-- **LEMMA 1, WHOLE.** -/
theorem lemma1_whole : Lemma1WholeStatement := by
  intro _ _ _ _ sT tab c hplan hreq hy htab hW h hN
  have hC : CellRel c.toCells tab :=
    (cellRel_iff _ _).mpr ⟨hN.small, fun _ ht _ hj => bytes_of_digits hN ht hj, h⟩
  exact ⟨lemma1_strong hplan hreq hy htab hW (fun _ ht _ hk => act_le sT c hplan hN ht hk) hC,
    lemma1N sT c hplan hN⟩

end VerifiableInference.Desc.Kinds.Head.Law
