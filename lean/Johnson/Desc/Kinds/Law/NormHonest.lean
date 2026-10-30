-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormHonest.lean.
WHAT IT DOES NOT SHOW. THAT CellRelN AND THE HEAD's OWN RELATION (CellRelH) CAN BE MET TOGETHER,
with the other premises of Lemma 1, whole: the head's 21 digits and its part of the wide matrix are
laid here as they come (bytes; zeros). Nothing on a prover's program or a proof file.
WHAT IT SHOWS: THE RELATION CellRelN (HeadNormLaw.lean) CAN BE MET: Lemma 1-N is not empty. Proved.
(1) cellRelN_of_int: the way back from the integers: cells whose integers meet the library's 17
identities at every position, and whose four keys lie in their ranges IN THE INTEGERS, meet
CellRelN. (2) honest_meets: for EVERY stream in five limbs on which the library's integer program
NORM goes on (HonHyp at every position; every rounded product fits 16 bits) the honest cells (the
row by the library's own honest ledger, hon; quotient, remainder and activation by the program's
formulas, cut into limbs) meet CellRelN. (3) cellRelN_met: under the tests on the plan there are
such cells: the stream of zeros.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.NormPoint
import Inst.Model.Common.LedgerHonest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E okE)
open OnBytes.Model (Aff Reading World)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)
open Inst.Model (NormPar)

/-! ## Canonical writings -/

theorem okE_natE (n : Nat) : okE (natE n) = true := by
  rw [OnBytes.okE_triple]
  show Fmt.Fld.two.okE (Fmt.Fld.ofF (Fmt.Fld.two.red n)) = true
  unfold Fmt.Fld.okE Fmt.Fld.ofF
  have h0 : Fmt.Fld.two.ok 0 = true := by decide
  simp [Fmt.Fld.ok_red, h0]

theorem okE_sumToForm (n : Nat) (hn : 0 < n) (f : Nat → Form) :
    okE (sumTo n f).const = true := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  unfold sumTo
  rw [List.range_succ, List.foldl_append]
  exact okE_addMul _ _ _

variable [Sizes] [Policy] [Request] [Token]

theorem okE_keyNAt (c : NCells) (p : NPt) (k : FinalNorm.Key) : okE (keyNAt c p k) = true := by
  cases k
  · exact okE_addMul _ _ _
  · exact okE_addMul _ _ _
  · exact okE_addMul _ _ _
  · letI := p.normIn; letI := normHeardAt c p.zt; letI := finalHeardAt c
    letI := normReadsAtCells c
    show okE (FinalNorm.key 21 .digits).const = true
    unfold FinalNorm.key
    exact okE_sumToForm _ (by unfold NR; omega) _

/-- An element that is read as a small natural number is that number's image. -/
theorem inBits_of_rd {w : Nat} {v : E} {z : Int} (hv : okE v = true) (hr : rd v = (z : K))
    (h0 : 0 ≤ z) (h1 : z < 2 ^ w) : InBits w v := by
  refine ⟨z.toNat, by zify; rw [Int.toNat_of_nonneg h0]; exact h1, eq_of_rd hv (okE_natE _) ?_⟩
  rw [hr]
  show _ = rd ((z.toNat : Nat) : E)
  rw [rd_natCast, ← Int.cast_natCast, Int.toNat_of_nonneg h0]

/-! ## (1) From the integers back -/

theorem vecK_eq_cast (c : NCells) (k t : Nat) :
    vecK c k t = ((Inst.Model.Ledger.idn npOf (Inst.Model.Ledger.Wsum d (limbZ c t)) (digZ c t) k :
      Int) : K) := by
  have hm := Inst.Model.Ledger.map_idn (Int.castRingHom K) (digZ c t) npOf
    (Inst.Model.Ledger.Wsum d (limbZ c t)) k
  simp only [eq_intCast] at hm
  rw [hm]
  unfold vecK
  congr 1
  funext s
  congr 1
  unfold Inst.Model.Ledger.Wsum wsqZ
  rw [sumZ_eq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sumZ_eq]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sumZ_eq]

/-- The relation, in the integers. -/
structure IntRelN (c : NCells) : Prop where
  small : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18
  smallS : ∀ f t, (c.stream f t).natAbs < 2 ^ 18
  idn : ∀ t, t < T → ∀ k, k < 17 →
    Inst.Model.Ledger.idn npOf (Inst.Model.Ledger.Wsum d (limbZ c t)) (digZ c t) k = 0
  remLow : ∀ t, t < T → ∀ x, x < d →
    0 ≤ Inst.Model.Site.site (str c t x * recZ c t) (awZ c t x) (remZ c t x) KF ∧
      Inst.Model.Site.site (str c t x * recZ c t) (awZ c t x) (remZ c t x) KF < 2 ^ 16
  remHigh : ∀ t, t < T → ∀ x, x < d →
    0 ≤ Inst.Model.Site.high (remZ c t x) KF 32 ∧ Inst.Model.Site.high (remZ c t x) KF 32 < 2 ^ 16
  clamp : ∀ t, t < T → ∀ x, x < d →
    0 ≤ awZ c t x + 2 ^ 15 ∧ awZ c t x + 2 ^ 15 < 2 ^ 16 ∧
      act c.toCells t x = clampZ (awZ c t x)
  digits : ∀ t, t < T → ∀ j, j < NR + 21 →
    0 ≤ (mul j : Int) * digZ c t j ∧ (mul j : Int) * digZ c t j < 2 ^ 8

theorem cellRelN_of_int {c : NCells} (hd : S2 ∣ d) (h : IntRelN c) : CellRelN c where
  small := h.small
  smallS := h.smallS
  rows := fun t ht v hv => by
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hv
    have hk' : k < 17 := by rw [rowsAt_length] at hk; exact hk
    apply eq_of_rd (okE_rowsAt c _ hv) okE_zero
    have e := rd_rowsAt c (bits lt t) (size_bits lt t) hk'
    rw [List.getD_eq_getElem _ _ hk, ext_corner ht, vecK_eq_cast, h.idn t ht k hk'] at e
    rw [e, rd_zero, Int.cast_zero]
  remLow := fun t ht x hx =>
    inBits_of_rd (okE_keyNAt _ _ _) (rd_keyN_remLow ht hd hx) (h.remLow t ht x hx).1
      (h.remLow t ht x hx).2
  remHigh := fun t ht x hx =>
    inBits_of_rd (okE_keyNAt _ _ _) (rd_keyN_remHigh ht hd hx) (h.remHigh t ht x hx).1
      (h.remHigh t ht x hx).2
  clamp := fun t ht x hx => by
    obtain ⟨h0, h1, h2⟩ := h.clamp t ht x hx
    obtain ⟨u, hu⟩ : ∃ u : Nat, awZ c t x + 2 ^ 15 = (u : Int) :=
      ⟨(awZ c t x + 2 ^ 15).toNat, (Int.toNat_of_nonneg h0).symm⟩
    have hc : -2047 ≤ clampZ ((u : Int) - 2 ^ 15) := by
      unfold clampZ
      omega
    obtain ⟨m, hm⟩ : ∃ m : Nat, (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11).toNat = m := ⟨_, rfl⟩
    have hm' : clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11 = (m : Int) := by
      rw [← hm]
      exact (Int.toNat_of_nonneg (by omega)).symm
    refine ⟨u, by zify; rw [← hu]; exact h1, eq_of_rd (okE_keyNAt _ _ _) (okE_natE _) ?_⟩
    rw [rd_keyN_clamp ht hd hx, hm]
    show _ = rd ((u + 2 ^ 28 * m : Nat) : E)
    have ha : awZ c t x = (u : Int) - 2 ^ 15 := by omega
    rw [rd_natCast, h2, ha]
    have : ((u : Int) - 2 ^ 15 + 2 ^ 15 + 2 ^ 28 * (clampZ ((u : Int) - 2 ^ 15) + 2 ^ 11)) =
        ((u + 2 ^ 28 * m : Nat) : Int) := by
      rw [hm']
      push_cast
      ring
    rw [this, Int.cast_natCast]
  digits := fun t ht j hj =>
    inBits_of_rd (okE_keyNAt _ _ _) (rd_keyN_digits ht hj) (h.digits t ht j hj).1
      (h.digits t ht j hj).2

/-! ## (2) The honest cells -/

/-- A number in two limbs: the low one a signed byte. -/
def loZ (z : Int) : Int := (z + 128) % 256 - 128
def hiZ (z : Int) : Int := (z - loZ z) / 256

theorem lo_hi (z : Int) : loZ z + 256 * hiZ z = z := by
  unfold hiZ loZ
  omega

theorem lo_bd (z : Int) : -128 ≤ loZ z ∧ loZ z ≤ 127 := by
  unfold loZ
  omega

theorem hi_bd {z : Int} (h0 : -2 ^ 16 ≤ z) (h1 : z < 2 ^ 16) : -257 ≤ hiZ z ∧ hiZ z ≤ 256 := by
  unfold hiZ loZ
  omega

section Honest
variable (b : Nat → Nat → Nat → Int)

/-- The stream's value, the rounded product, the remainder's part above 16 bits, the activation: by
the library's integer program. -/
def xH (t : Nat) : Nat → Int := Inst.Model.Ledger.xOf (b t)
def awH (t k : Nat) : Int := Inst.Model.NORM.yw npOf d (xH b t) k
def rhH (t k : Nat) : Int :=
  (xH b t k * Inst.Model.NORM.R npOf d (xH b t) + 2 ^ (KF - 1) - 2 ^ KF * awH b t k) / 2 ^ 16
def actH (t k : Nat) : Int := Inst.Model.NORM.out npOf d (xH b t) k

/-- THE HONEST CELLS of the stream whose limb l of feature k at position t is b t l k. Beyond the
positions and the features that there are: zeros. -/
def honestN : NCells where
  Wh := fun _ _ => 0
  stream := fun f t => if t < T ∧ f < 5 * d then b t (f / d) (f % d) else 0
  cell := fun m f t =>
    if t < T then
      match m with
      | .row => Inst.Model.Ledger.hon npOf d (b t) f - 128
      | .act => if f < d then loZ (actH b t f) else if f < 2 * d then hiZ (actH b t (f - d)) else 0
      | .wide =>
        if f < d then loZ (awH b t f) else if f < 2 * d then hiZ (awH b t (f - d))
        else if f < 3 * d then loZ (rhH b t (f - 2 * d) - 32896)
        else if f < 4 * d then hiZ (rhH b t (f - 3 * d) - 32896) else 0
    else 0

/-- What is asked of the stream: the library's conditions for its honest ledger, and that the
integer program goes on. -/
structure RunsN : Prop where
  hon : ∀ t, t < T → Inst.Model.Ledger.HonHyp npOf d (b t)
  fits : ∀ t, t < T → ∀ k, k < d → Inst.Model.Fits16 (awH b t k)

variable {b}

theorem limb_honest {t l k : Nat} (ht : t < T) (hl : l < 5) (hk : k < d) :
    limbZ (honestN b) t l k = b t l k := by
  show (if t < T ∧ l * d + k < 5 * d then b t ((l * d + k) / d) ((l * d + k) % d) else 0) = _
  have h1 : l * d + k < 5 * d := by nlinarith
  have hd0 : 0 < d := by omega
  rw [if_pos ⟨ht, h1⟩, Nat.mul_comm l d, Nat.mul_add_div hd0, Nat.div_eq_of_lt hk, Nat.add_zero,
    Nat.mul_add_mod, Nat.mod_eq_of_lt hk]

theorem wsum_honest {t : Nat} (ht : t < T) :
    Inst.Model.Ledger.Wsum d (limbZ (honestN b) t) = Inst.Model.Ledger.Wsum d (b t) := by
  funext s
  unfold Inst.Model.Ledger.Wsum
  refine Finset.sum_congr rfl fun j hj => ?_
  refine Finset.sum_congr rfl fun l hl => ?_
  refine Finset.sum_congr rfl fun l' hl' => ?_
  rw [limb_honest ht (Finset.mem_range.mp hl) (Finset.mem_range.mp hj),
    limb_honest ht (Finset.mem_range.mp hl') (Finset.mem_range.mp hj)]

theorem str_honest {t k : Nat} (ht : t < T) (hk : k < d) : str (honestN b) t k = xH b t k := by
  unfold str xH Inst.Model.Ledger.xOf
  rw [sumZ_eq]
  exact Finset.sum_congr rfl fun l hl => by rw [limb_honest ht (Finset.mem_range.mp hl) hk]

theorem dig_honest {t : Nat} (ht : t < T) :
    digZ (honestN b) t = Inst.Model.Ledger.hon npOf d (b t) := by
  funext j
  show (if t < T then Inst.Model.Ledger.hon npOf d (b t) j - 128 else 0) + 128 = _
  rw [if_pos ht]
  ring

theorem aw_honest {t k : Nat} (ht : t < T) (hk : k < d) : awZ (honestN b) t k = awH b t k := by
  show (if t < T then (if k < d then loZ (awH b t k) else _) else 0) +
    256 * (if t < T then (if d + k < d then _ else if d + k < 2 * d then
      hiZ (awH b t (d + k - d)) else _) else 0) = _
  rw [if_pos ht, if_pos ht, if_pos hk, if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]
  exact lo_hi _

theorem rem_honest {t k : Nat} (ht : t < T) (hk : k < d) : remZ (honestN b) t k = rhH b t k := by
  show (if t < T then (if 2 * d + k < d then _ else if 2 * d + k < 2 * d then _
      else if 2 * d + k < 3 * d then loZ (rhH b t (2 * d + k - 2 * d) - 32896) else _) else 0) +
    256 * (if t < T then (if 2 * d + d + k < d then _ else if 2 * d + d + k < 2 * d then _
      else if 2 * d + d + k < 3 * d then _ else if 2 * d + d + k < 4 * d then
        hiZ (rhH b t (2 * d + d + k - 3 * d) - 32896) else _) else 0) + 32896 = _
  rw [if_pos ht, if_pos ht, if_neg (by omega), if_neg (by omega), if_pos (by omega),
    if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left, show 2 * d + d + k - 3 * d = k by omega, lo_hi]
  ring

theorem act_honest {t k : Nat} (ht : t < T) (hk : k < d) :
    act (honestN b).toCells t k = actH b t k := by
  show (if t < T then (if k < d then loZ (actH b t k) else _) else 0) +
    256 * (if t < T then (if d + k < d then _ else if d + k < 2 * d then
      hiZ (actH b t (d + k - d)) else _) else 0) = _
  rw [if_pos ht, if_pos ht, if_pos hk, if_neg (by omega), if_pos (by omega),
    Nat.add_sub_cancel_left]
  exact lo_hi _

/-- Every digit of the honest ledger is a byte, also beyond the 99. -/
theorem hon_byte_all {t : Nat} (H : Inst.Model.Ledger.HonHyp npOf d (b t)) (n : Nat) :
    0 ≤ Inst.Model.Ledger.hon npOf d (b t) n ∧ Inst.Model.Ledger.hon npOf d (b t) n ≤ 255 := by
  by_cases hn : n < 99
  · exact Inst.Model.Ledger.hon_byte H hn
  · obtain ⟨j, rfl⟩ : ∃ j, n = 94 + j := ⟨n - 94, by omega⟩
    unfold Inst.Model.Ledger.hon
    rw [Inst.Model.Ledger.rd_rq]
    exact Inst.Model.Ledger.byteAt_bounds _ _

/-- The remainder of the rounding. -/
theorem rem_facts (P : PlanN) (t k : Nat) :
    0 ≤ rhH b t k ∧ rhH b t k < 2 ^ (KF - 16) ∧
      0 ≤ Inst.Model.Site.site (xH b t k * Inst.Model.NORM.R npOf d (xH b t)) (awH b t k)
        (rhH b t k) KF ∧
      Inst.Model.Site.site (xH b t k * Inst.Model.NORM.R npOf d (xH b t)) (awH b t k)
        (rhH b t k) KF < 2 ^ 16 := by
  have hK := P.hK17
  set A := xH b t k * Inst.Model.NORM.R npOf d (xH b t) with hA
  have hs := Inst.Model.rhu_spec A KF
  have hq : awH b t k = Inst.Model.rhu A KF := rfl
  set r0 := A + 2 ^ (KF - 1) - 2 ^ KF * awH b t k with hr0
  have h0 : 0 ≤ r0 := by rw [hr0, hq]; linarith [hs.1]
  have h1 : r0 < 2 ^ KF := by rw [hr0, hq]; linarith [hs.2]
  have hrh : rhH b t k = r0 / 2 ^ 16 := rfl
  have hpow : (2 : Int) ^ KF = 2 ^ 16 * 2 ^ (KF - 16) := by
    rw [← pow_add]
    congr 1
    omega
  have hsite : Inst.Model.Site.site A (awH b t k) (rhH b t k) KF = r0 % 2 ^ 16 := by
    unfold Inst.Model.Site.site
    rw [hrh, Int.emod_def]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hrh]; exact Int.ediv_nonneg h0 (by norm_num)
  · rw [hrh]; exact Int.ediv_lt_of_lt_mul (by norm_num) (by rw [mul_comm, ← hpow]; exact h1)
  · rw [hsite]; exact Int.emod_nonneg _ (by norm_num)
  · rw [hsite]; exact Int.emod_lt_of_pos _ (by norm_num)

/-- **(2) THE HONEST CELLS MEET THE RELATION.** -/
theorem honest_meets (P : PlanN) (R : RunsN b) : CellRelN (honestN b) := by
  have hdS : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have pK16 : (2 : Int) ^ (KF - 16) ≤ 2 ^ 16 :=
    pow_le_pow_right₀ (by norm_num) (by have := P.hK32; omega)
  have outB : ∀ t k, -2047 ≤ actH b t k ∧ actH b t k ≤ 2047 := fun t k => by
    unfold actH Inst.Model.NORM.out Inst.Model.clamp
    omega
  refine cellRelN_of_int hdS ⟨fun m f t => ?_, fun f t => ?_, fun t ht k hk => ?_,
    fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht x hx => ?_, fun t ht j hj => ?_⟩
  · -- small
    show (if t < T then _ else (0 : Int)).natAbs < 2 ^ 18
    by_cases ht : t < T
    · rw [if_pos ht]
      cases m with
      | row =>
        have := hon_byte_all (R.hon t ht) f
        show (Inst.Model.Ledger.hon npOf d (b t) f - 128).natAbs < 2 ^ 18
        omega
      | act =>
        show (if f < d then loZ (actH b t f) else if f < 2 * d then hiZ (actH b t (f - d))
          else 0).natAbs < 2 ^ 18
        split
        · have := lo_bd (actH b t f); omega
        · split
          · have := outB t (f - d)
            have := hi_bd (z := actH b t (f - d)) (by omega) (by omega)
            omega
          · norm_num
      | wide =>
        show (if f < d then loZ (awH b t f) else if f < 2 * d then hiZ (awH b t (f - d))
          else if f < 3 * d then loZ (rhH b t (f - 2 * d) - 32896)
          else if f < 4 * d then hiZ (rhH b t (f - 3 * d) - 32896) else 0).natAbs < 2 ^ 18
        split
        · have := lo_bd (awH b t f); omega
        · split
          · have h := R.fits t ht (f - d) (by omega)
            unfold Inst.Model.Fits16 at h
            have := hi_bd (z := awH b t (f - d)) (by omega) (by omega)
            omega
          · split
            · have := lo_bd (rhH b t (f - 2 * d) - 32896); omega
            · split
              · have h := rem_facts (b := b) P t (f - 3 * d)
                have := hi_bd (z := rhH b t (f - 3 * d) - 32896) (by omega) (by omega)
                omega
              · norm_num
    · rw [if_neg ht]
      norm_num
  · -- smallS
    show (if t < T ∧ f < 5 * d then b t (f / d) (f % d) else 0).natAbs < 2 ^ 18
    by_cases h : t < T ∧ f < 5 * d
    · rw [if_pos h]
      have hd0 : 0 < d := by omega
      have := (R.hon t h.1).cell (f / d) (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h.2))
        (f % d) (Nat.mod_lt _ hd0)
      rw [abs_le] at this
      omega
    · rw [if_neg h]
      norm_num
  · rw [wsum_honest ht, dig_honest ht]
    exact Inst.Model.Ledger.hon_idn (R.hon t ht) k hk
  · have hr : recZ (honestN b) t = Inst.Model.NORM.R npOf d (xH b t) := by
      unfold recZ
      rw [dig_honest ht]
      exact Inst.Model.Ledger.hon_R (R.hon t ht)
    rw [str_honest ht hx, hr, aw_honest ht hx, rem_honest ht hx]
    exact ⟨(rem_facts P t x).2.2.1, (rem_facts P t x).2.2.2⟩
  · rw [rem_honest ht hx]
    obtain ⟨h0, h1, _, _⟩ := rem_facts (b := b) P t x
    unfold Inst.Model.Site.high
    have hp : (0 : Int) < 2 ^ (32 - KF) := by positivity
    refine ⟨mul_nonneg hp.le h0, ?_⟩
    have e : (2 : Int) ^ (32 - KF) * 2 ^ (KF - 16) = 2 ^ 16 := by
      rw [← pow_add]
      congr 1
      have := P.hK17
      have := P.hK32
      omega
    rw [← e]
    exact mul_lt_mul_of_pos_left h1 hp
  · rw [aw_honest ht hx, act_honest ht hx]
    have h := R.fits t ht x hx
    unfold Inst.Model.Fits16 at h
    exact ⟨by omega, by omega, rfl⟩
  · rw [dig_honest ht]
    by_cases h99 : j < 99
    · have := Inst.Model.Ledger.hon_typed (R.hon t ht) j h99
      rw [mul_eq_mu]
      exact ⟨this.1, by norm_num; omega⟩
    · have hm : ((mul j : Nat) : Int) = 1 := by
        unfold mul
        have : ∀ a : Nat, a < 99 → (j == a) = false := fun a ha => by simp; omega
        simp [this]
      have := hon_byte_all (R.hon t ht) j
      rw [hm, one_mul]
      exact ⟨this.1, by norm_num; omega⟩

end Honest

/-- **(3) UNDER THE TESTS ON THE PLAN THE RELATION IS MET**: by the honest cells of the stream of
zeros. -/
theorem cellRelN_met {sT : Nat} (hplan : planOk sT = true) : ∃ c : NCells, CellRelN c := by
  have P := planN hplan
  refine ⟨honestN fun _ _ _ => 0, honest_meets P ⟨fun t _ => ?_, fun t _ k _ => ?_⟩⟩
  · have h1 := P.he1
    have h2 := P.he48
    have h3 := P.hled
    have hx : ∀ j, Inst.Model.Ledger.xOf (fun _ _ => (0 : Int)) j = 0 := fun j => by
      simp [Inst.Model.Ledger.xOf]
    refine ⟨?_, ?_, P.hM47, by omega, fun _ _ _ _ => by simp, ?_⟩
    · show (1 : Int) ≤ (epsF : Int)
      exact_mod_cast h1
    · show (epsF : Int) < 2 ^ 48
      exact_mod_cast h2
    · have hV : Inst.Model.NORM.V d (Inst.Model.Ledger.xOf fun _ _ => (0 : Int)) = 0 := by
        unfold Inst.Model.NORM.V
        exact Finset.sum_eq_zero fun j _ => by rw [hx]; ring
      rw [hV]
      show (0 : Int) + (epsF : Int) < 2 ^ 78
      have : (epsF : Int) < 2 ^ 48 := by exact_mod_cast h2
      linarith [show (2 : Int) ^ 48 < 2 ^ 78 by norm_num]
  · have hx : xH (fun _ _ _ => (0 : Int)) t k = 0 := by
      simp [xH, Inst.Model.Ledger.xOf]
    unfold awH Inst.Model.NORM.yw
    rw [hx, zero_mul, Inst.Model.rhu_zero (by show 1 ≤ KF; have := P.hK17; omega)]
    unfold Inst.Model.Fits16
    norm_num

end VerifiableInference.Desc.Kinds.Head.Law
