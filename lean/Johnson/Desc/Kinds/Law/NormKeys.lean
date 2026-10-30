-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NormKeys.lean: THE FINAL NORMALIZATION's FOUR KEYS IN ANY WORLD: each key's value,
in a world in which three reads and the one claimed sum have their true values and the letters that
come in are the weights that they are taken for, is spread over its entries and the positions:
  val W (FinalNorm.key 21 k) = the sum over x < lenN k, t < T of ew k x * eq zt t * GN c k x t,
AND GN DOES NOT DEPEND ON THE POINT: it is the key's value at the corner of x and t
(rd_keyNAt_corner). What Lemma 2a and Law/General.lean say of the head's five keys, said of the
normalization's four. No chance in it.
IMPORTED, NOT THIS FILE's: HeadNormLaw.lean and Law/NormProof.lean (NCells, keyNAt, cornerN, trueNormed;
awZ, remZ, recZ, rd_R; the four corner values rd_keyN_*); Law/Base.lean, Law/Corner.lean.
WHAT IT DOES NOT SAY. That the reads and the claimed sum are true in a world: the range check's law and
a law of the sumcheck "normed", which is stated nowhere yet. Nothing on a verifier's yes.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.Val
import Johnson.Desc.Kinds.Law.NormProof

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open OnBytes.Model (Aff Reading World)
open Norm (lt ls d lPd T S2)
open FinalNorm (MF KF epsF)

variable [Sizes] [Policy] [Request] [Token]

/-- A key of the normalization at entry x and position t: its corner value, read in the field. -/
def GN (c : NCells) : FinalNorm.Key → Nat → Nat → K
  | .remLow, x, t =>
    ((Inst.Model.Site.site (str c t x * recZ c t) (awZ c t x) (remZ c t x) KF : Int) : K)
  | .remHigh, x, t => ((Inst.Model.Site.high (remZ c t x) KF 32 : Int) : K)
  | .clamp, x, t => (((awZ c t x + 2 ^ 15) + 2 ^ 28 * (act c.toCells t x + 2 ^ 11) : Int) : K)
  | .digits, x, t => (((mul x : Int) * digZ c t x : Int) : K)

/-- **GN is the key at the corner.** -/
theorem rd_keyNAt_corner (c : NCells) (hd : S2 ∣ d) (k : FinalNorm.Key) {x t : Nat}
    (hx : x < lenN k) (ht : t < T) : rd (keyNAt c (cornerN x t) k) = GN c k x t := by
  cases k
  · exact rd_keyN_remLow ht hd hx
  · exact rd_keyN_remHigh ht hd hx
  · exact rd_keyN_clamp ht hd hx
  · exact rd_keyN_digits ht hx

section Filled
variable [FinalNorm.In] [Norm.Heard] [FinalNorm.Heard] [FinalNorm.Reads]

/-- In the world W: the reads of act and of the row at the lookup's point, the head's read of its wide
matrix there, and the claimed sum of "normed" have their true values; the letters are the weights that
they are taken for. EACH READ IS ASKED BELOW THE LENGTH THAT THE FOUR KEYS SPEND, and no further: beyond a
read's length an entry of the real array is another read's (fam2's find on its own TrueReads). -/
structure FilledNW (W : World K) (c : NCells) : Prop where
  hact : ∀ i, i < 2 * d → val W (FinalNorm.entry .actAtKeys i)
    = rd (readAtN c (.act, .short (eq FinalNorm.zt)) i)
  hrow : ∀ i, i < NR + 21 → val W (FinalNorm.entry .rowAtKeys i)
    = rd (readAtN c (.row, .short (eq FinalNorm.zt)) i)
  hwide : ∀ i, i < 4 * d / S2 → val W (FinalNorm.wide i)
    = rd (readAt c.toCells (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)) i)
  hclaimed : val W FinalNorm.normed.claimed.var = rd (trueNormed c)
  hblock : ∀ k, k ≠ FinalNorm.Key.digits → ∀ x, x < d →
    FinalNorm.ew k x = FinalNorm.ewh k (x / S2) * eq FinalNorm.zl (x % S2)
  hwsum : ∀ k, FinalNorm.wsum k = sumTo (lenN k) fun x => FinalNorm.ew k x
  hzt : (FinalNorm.zt).size = lt

variable {W : World K} {c : NCells}

/-- The weight of entry x of key k; of position t. -/
def UN (k : FinalNorm.Key) (x : Nat) : K := rd (FinalNorm.ew k x)
@[inherit_doc UN] def WN (t : Nat) : K := rd (eq FinalNorm.zt t)

theorem sum_WN (hF : FilledNW W c) : (Finset.range T).sum WN = 1 := by
  have h := sum_rd_eq FinalNorm.zt
  rw [hF.hzt] at h
  exact h

theorem val_short (m : FinalNorm.Matrix) (i : Nat) :
    rd (readAtN c (m, .short (eq FinalNorm.zt)) i)
      = (Finset.range T).sum fun t => WN t * ((c.of m i t : Int) : K) := by
  show rd (sumTo T fun t => eq FinalNorm.zt t * ofInt (c.of m i t)) = _
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun t _ => by rw [rd_mul, rd_ofInt]; rfl

theorem val_long (i : Nat) :
    rd (readAt c.toCells (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)) i)
      = (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
          rd (eq FinalNorm.zl j) * WN t * ((c.cell .wide (S2 * i + j) t : Int) : K) := by
  show rd (sumTo S2 fun j => sumTo T fun t =>
    eq FinalNorm.zl j * eq FinalNorm.zt t * ofInt (c.cell .wide (S2 * i + j) t)) = _
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun t _ => by rw [rd_mul, rd_mul, rd_ofInt]; rfl

/-- Two limbs of the wide matrix from feature f0 on, under a key's weights. -/
theorem val_wideAt (hF : FilledNW W c) (hd : S2 ∣ d) (k : FinalNorm.Key)
    (hk : k ≠ FinalNorm.Key.digits) (f0 : Nat) (hf : S2 ∣ f0) (hf4 : f0 + 2 * d ≤ 4 * d) :
    val W (FinalNorm.wideAt k f0) = spr d T (UN k) WN fun x t =>
      ((c.cell .wide (f0 + x) t + 256 * c.cell .wide (f0 + d + x) t : Int) : K) := by
  have hS : 0 < S2 := S2_posN
  have hdd : d / S2 * S2 = d := Nat.div_mul_cancel hd
  have hb := sum_blocks S2 (fun x => (Finset.range T).sum fun t => UN k x * WN t *
    ((c.cell .wide (f0 + x) t + 256 * c.cell .wide (f0 + d + x) t : Int) : K)) (d / S2)
  rw [hdd] at hb
  unfold spr
  rw [← hb]
  unfold FinalNorm.wideAt
  rw [val_sumTo]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  have hin : ∀ l, l < 2 → (f0 + l * d) / S2 + i < 4 * d / S2 := by
    intro l hl
    obtain ⟨a, ha⟩ : S2 ∣ f0 + l * d := Dvd.dvd.add hf (Dvd.dvd.mul_left hd l)
    have h1 : (i + 1) * S2 ≤ d / S2 * S2 := Nat.mul_le_mul_right _ hi'
    rw [hdd] at h1
    have h2 : l * d ≤ 1 * d := Nat.mul_le_mul_right d (by omega)
    rw [ha, Nat.mul_div_cancel_left _ hS]
    apply (Nat.le_div_iff_mul_le hS).2
    have h3 : (a + i + 1) * S2 = S2 * a + (i + 1) * S2 := by ring
    rw [h3, ← ha]
    omega
  rw [val_sumTo, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    val_smulE, val_smulE, rd_mul, rd_mul, rd_pow, rd_pow, rd_ofNat,
    hF.hwide _ (hin 0 (by omega)), hF.hwide _ (hin 1 (by omega)), val_long,
    val_long, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e0 : S2 * ((f0 + 0 * d) / S2 + i) + j = f0 + (S2 * i + j) := by
    rw [Nat.zero_mul, Nat.add_zero, Nat.mul_add, Nat.mul_div_cancel' hf, Nat.add_assoc]
  have e1 : S2 * ((f0 + 1 * d) / S2 + i) + j = f0 + d + (S2 * i + j) := by
    rw [Nat.one_mul, Nat.mul_add, Nat.mul_div_cancel' (Dvd.dvd.add hf hd), Nat.add_assoc]
  have hlt : S2 * i + j < d := by
    have h1 : (i + 1) * S2 ≤ d / S2 * S2 := Nat.mul_le_mul_right _ hi'
    rw [hdd, Nat.add_mul, Nat.one_mul, Nat.mul_comm] at h1
    omega
  have h1 : (S2 * i + j) / S2 = i := by
    rw [Nat.mul_add_div hS, Nat.div_eq_of_lt hj', Nat.add_zero]
  have h2 : (S2 * i + j) % S2 = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj']
  have hU : UN k (S2 * i + j) = rd (FinalNorm.ewh k i) * rd (eq FinalNorm.zl j) := by
    unfold UN
    rw [hF.hblock k hk _ hlt, rd_mul, h1, h2]
  rw [e0, e1, hU]
  push_cast
  ring

theorem rd_wsumN' (hF : FilledNW W c) (k : FinalNorm.Key) (a : K) :
    rd (FinalNorm.wsum k) * a = spr (lenN k) T (UN k) WN fun _ _ => a := by
  rw [hF.hwsum, rd_sumTo, Finset.sum_mul]
  exact spr_entries (sum_WN hF) fun _ => a

theorem rd_wsum_d (hF : FilledNW W c) (k : FinalNorm.Key) (hk : k ≠ FinalNorm.Key.digits) (a : K) :
    rd (FinalNorm.wsum k) * a = spr d T (UN k) WN fun _ _ => a := by
  cases k
  · exact rd_wsumN' hF _ a
  · exact rd_wsumN' hF _ a
  · exact rd_wsumN' hF _ a
  · exact absurd rfl hk

theorem rd_trueNormed' :
    rd (trueNormed c) = spr d T (UN .remLow) WN fun x t => ((str c t x * recZ c t : Int) : K) := by
  have h : ∀ t, rd (sumTo d fun x => eq FinalNorm.zt t * FinalNorm.ew .remLow x *
      (ofInt (str c t x) * (rowZ c t).R.const))
      = (Finset.range d).sum fun x => UN .remLow x * WN t * ((str c t x * recZ c t : Int) : K) := by
    intro t
    rw [rd_sumTo]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [rd_mul, rd_mul, rd_mul, rd_ofInt, rd_R]
    unfold UN WN
    push_cast
    ring
  unfold trueNormed
  rw [rd_sumTo]
  simp only [h]
  unfold spr
  exact Finset.sum_comm

/-- **Each of the four keys, in any such world.** -/
theorem val_keyN (hF : FilledNW W c) (hd : S2 ∣ d) (k : FinalNorm.Key) :
    val W (FinalNorm.key 21 k) = spr (lenN k) T (UN k) WN (GN c k) := by
  cases k
  · show _ = spr d T (UN .remLow) WN (GN c .remLow)
    unfold FinalNorm.key
    rw [val_sub, val_sub, val_addE, val_smulN, val_smulN, hF.hclaimed, rd_trueNormed', rd_mul,
      rd_sub, rd_natCast, rd_natCast, rd_wsum_d hF .remLow (fun h => FinalNorm.Key.noConfusion h),
      val_wideAt hF hd .remLow (fun h => FinalNorm.Key.noConfusion h) 0 (Nat.dvd_zero _) (by omega),
      val_wideAt hF hd .remLow (fun h => FinalNorm.Key.noConfusion h) (2 * d)
        (Dvd.dvd.mul_left hd 2) (by omega),
      spr_mul, spr_mul, spr_add, spr_sub, spr_sub]
    apply spr_congr
    intro x _ t _
    simp only [GN]
    unfold Inst.Model.Site.site awZ remZ off2
    simp only [Nat.zero_add]
    push_cast
    ring
  · show _ = spr d T (UN .remHigh) WN (GN c .remHigh)
    unfold FinalNorm.key
    rw [val_smulN, val_Eadd, rd_nmul, mul_comm ((off2 : Nat) : K) (rd (FinalNorm.wsum .remHigh)),
      rd_wsum_d hF .remHigh (fun h => FinalNorm.Key.noConfusion h),
      val_wideAt hF hd .remHigh (fun h => FinalNorm.Key.noConfusion h) (2 * d)
        (Dvd.dvd.mul_left hd 2) (by omega), spr_add, spr_mul]
    apply spr_congr
    intro x _ t _
    simp only [GN]
    unfold Inst.Model.Site.high remZ off2
    push_cast
    ring
  · show _ = spr d T (UN .clamp) WN (GN c .clamp)
    have h1 : ((Finset.range d).sum fun k =>
        val W (FinalNorm.ew .clamp k • FinalNorm.actAt (FinalNorm.entry .actAtKeys) k))
        = spr d T (UN .clamp) WN fun x t => ((act c.toCells t x : Int) : K) := by
      unfold spr
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.1 hk
      rw [val_smulE]
      unfold FinalNorm.actAt
      rw [val_add, val_smulN, hF.hact _ (by omega), hF.hact _ (by omega), val_short, val_short,
        Finset.mul_sum,
        ← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      unfold UN act NCells.of
      push_cast
      ring
    unfold FinalNorm.key
    rw [val_addE, val_add, val_smulN, val_sumTo, h1, rd_muln, rd_wsum_d hF .clamp (fun h => FinalNorm.Key.noConfusion h),
      val_wideAt hF hd .clamp (fun h => FinalNorm.Key.noConfusion h) 0 (Nat.dvd_zero _) (by omega),
      spr_mul, spr_add, spr_add]
    apply spr_congr
    intro x _ t _
    simp only [GN]
    unfold awZ
    simp only [Nat.zero_add]
    push_cast
    ring
  · show _ = spr (NR + 21) T (UN .digits) WN (GN c .digits)
    have h128 : ((off1 : Nat) : K) = (Finset.range T).sum fun t => WN t * ((off1 : Nat) : K) := by
      rw [← Finset.sum_mul, sum_WN hF, one_mul]
    unfold FinalNorm.key spr
    rw [val_sumTo]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [val_smulE, rd_mul, rd_natCast, val_add, val_natCast, hF.hrow _ (Finset.mem_range.1 hj),
      val_short]
    conv_lhs => rw [h128]
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [GN]
    unfold UN digZ NCells.of off1
    push_cast
    ring

end Filled

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.val_keyN
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rd_keyNAt_corner
