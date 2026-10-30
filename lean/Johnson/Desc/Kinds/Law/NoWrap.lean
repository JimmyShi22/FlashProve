-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/NoWrap.lean: LEMMA 1, FROM THE FIELD TO THE INTEGERS (L4 of the road).
`CastRel`: the relation on cells as equalities, in the field, of casts of the integers of Ints.lean.
`intRel_of_castRel`: under the tests on the plan and the lemma's bounds these equalities hold in the
integers: no side can wrap around the prime.
-/
import Mathlib
import OnBytes.Slice.ProgField
import Johnson.Desc.Kinds.Law.Ints

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Norm (lt ls d lPd T S2)

/-- The field in which the program's elements are read. -/
abbrev K : Type := Cb.Gl.E

instance : CharP K Code.pGold :=
  charP_of_injective_algebraMap (algebraMap Cb.Gl.F Cb.Gl.E).injective Code.pGold

/-- Two integers with one image in the field, less than the prime apart, are equal. -/
theorem int_eq_of_cast_eq {a b : Int} (h : (a : K) = (b : K)) (hb : |a - b| < 2 ^ 63) : a = b := by
  have h0 : ((a - b : Int) : K) = 0 := by push_cast; rw [h]; ring
  have hd := (CharP.intCast_eq_zero_iff K Code.pGold (a - b)).mp h0
  have hp : (2 : Int) ^ 63 < (Code.pGold : Int) := by rw [Code.pGold_eq]; norm_num
  have := Int.eq_zero_of_abs_lt_dvd hd (lt_trans hb hp)
  omega

/-! ## The digits of a number -/

theorem digits_lt (m : Nat) (a : Nat → Int) (h : ∀ l, l < m → 0 ≤ a l ∧ a l < 256) :
    (Finset.range m).sum (fun l => 256 ^ l * a l) < 256 ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have h1 := ih fun l hl => h l (Nat.lt_succ_of_lt hl)
    have h2 := (h m (Nat.lt_succ_self m)).2
    have hp : (0 : Int) < 256 ^ m := by positivity
    nlinarith

variable [Sizes] [Policy] [Request] [Token]

/-! ## What the tests on the plan say -/

structure PlanFacts : Prop where
  hF : F = 24
  hsh : sh = 7 ∨ sh = 8
  hV2 : 2 ≤ V
  hdS : d % S2 = 0
  hJVa : JVa % S2 = 0
  hW : (2 * d * 2 ^ 11 * 2 ^ 12 + 1) + 2 ^ 40 + 2 ^ 8 * 2 ^ 37 + 2 ^ sh * (257 * 2 ^ 18 + 32896)
        + 2 ^ 18 + 128 < 2 ^ 60
  hZ : JV * 2 ^ F + 2 ^ 24 + (JV - V + 1) * 2 ^ F < 2 ^ 60
  hE2 : T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) + theta * T < 2 ^ 60
  hE3 : T * (2 ^ 8 + 2 ^ 16) + cap < 2 ^ 60
  hE4 : 2 ^ 40 + 2 ^ 40 + C < 2 ^ 60

theorem planFacts {sT : Nat} (h : planOk sT = true) : PlanFacts := by
  unfold planOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨_, hr⟩, hn⟩ := h
  unfold Sizes.ranges at hr
  simp only [Bool.and_eq_true] at hr
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hF⟩, hsh⟩, _⟩, hV⟩, _⟩, _⟩, hd⟩, hJ⟩, _⟩ := hr
  unfold noOverflow at hn
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true] at hn
  obtain ⟨_, _, _, hW, _, _, _, hZ, hE2, hE3, hE4, _⟩ := hn
  have hW' := of_decide_eq_true hW
  unfold Ty BW BC BIG off1 off2 at hW'
  exact ⟨by simpa using hF, by simpa using hsh, by simpa using hV, by simpa using hd,
    by simpa using hJ, hW', of_decide_eq_true hZ, of_decide_eq_true hE2, of_decide_eq_true hE3,
    of_decide_eq_true hE4⟩

/-! ## The relation, as equalities of casts -/

/-- WHAT THE CORNER VALUES DELIVER (L3): each line of `CellRel`, read in the field, is an equality
between casts of integers. -/
structure CastRel (c : Cells) (tab : Nat → Nat) : Prop where
  small : ∀ m f t, (c.cell m f t).natAbs < 2 ^ 18
  bytes : ∀ t, t < T → ∀ j, j < 21 →
    0 ≤ c.cell .row (NR + j) t + 128 ∧ c.cell .row (NR + j) t + 128 < 256
  mid : ∀ t, t < T → ∀ x, x < JV → ∃ n : Nat, n < 2 ^ 16 ∧ ((midZ c x t : Int) : K) = ((n : Int) : K)
  low : ∀ t, t < T → ∀ x, x < JV → ∃ n : Nat, n < 2 ^ 8 ∧ ((lowZ c x t : Int) : K) = ((n : Int) : K)
  top : ∀ t, t < T → ∀ x, x < JV → ∃ n : Nat, n < 2 ^ 16 ∧
    ((topNum c x t : Int) : K) = ((2 ^ (sh + 15) * (n : Int) : Int) : K)
  row : ∀ t, t < T → ∀ x, x < JV → ∃ u : Nat, u < 2 ^ 16 ∧
    ((midZ c x t + 2 ^ 16 * tvZ c x t : Int) : K) = (((u : Int) + 2 ^ 16 * (tab u : Int) : Int) : K)
  clip : ∀ t, t < T → costed t = true →
    ((numZ c .paid t + numZ c .slackClip t : Int) : K) = (((C : Nat) : Int) : K)
  table : ∀ t, t < T → costed t = true →
    ((numZ c .slackTable t + (Finset.range JV).sum (fun x => tvZ c x t) : Int) : K)
      = ((((JV - V + 1 : Nat) : Int) * 2 ^ F : Int) : K)
  mean : (((Finset.range T).sum (fun t => if costed t = true then
      numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t else 0) : Int) : K)
      = (((theta : Int) * (RC : Int) : Int) : K)
  count : (((Finset.range T).sum (fun t => if costed t = true then
      numZ c .over t + numZ c .slackCap t else 0) : Int) : K)
      = ((((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K)

section Bounds
variable {c : Cells} {tab : Nat → Nat}

theorem cell_bd (h : CastRel c tab) (m : Matrix) (f t : Nat) :
    -(2 : Int) ^ 18 < c.cell m f t ∧ c.cell m f t < 2 ^ 18 := by
  have := h.small m f t
  constructor <;> omega

theorem numZ_bd (h : CastRel c tab) (n : Number) {t : Nat} (ht : t < T) :
    0 ≤ numZ c n t ∧ numZ c n t < 256 ^ n.digits.2 := by
  have hd : ∀ l, l < n.digits.2 → 0 ≤ c.cell .row (NR + n.digits.1 + l) t + 128 ∧
      c.cell .row (NR + n.digits.1 + l) t + 128 < 256 := by
    intro l hl
    have hl' : n.digits.1 + l < 21 := by
      cases n <;> simp only [Number.digits] at hl ⊢ <;> omega
    have hb := h.bytes t ht _ hl'
    rwa [← Nat.add_assoc] at hb
  refine ⟨?_, digits_lt _ _ hd⟩
  unfold numZ
  exact Finset.sum_nonneg fun l hl =>
    mul_nonneg (by positivity) (hd l (Finset.mem_range.mp hl)).1

theorem abs_logit_le (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (hA : ∀ t, t < T → ∀ k, k < d → (act c t k).natAbs ≤ 2047) {t : Nat} (ht : t < T) (v : Nat) :
    |logit c t v| ≤ (d : Int) * (2047 * 4096) := by
  unfold logit
  rw [sumZ_eq]
  calc |(Finset.range d).sum fun k => act c t k * c.Wh k v|
      ≤ (Finset.range d).sum fun k => |act c t k * c.Wh k v| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ (Finset.range d).sum fun _ => (2047 * 4096 : Int) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [abs_mul]
        have h1 : |act c t k| ≤ 2047 := by
          have := hA t ht k (Finset.mem_range.mp hk); rw [Int.abs_eq_natAbs]; exact_mod_cast this
        have h2 : |c.Wh k v| ≤ 4096 := by
          have := hW k v; rw [Int.abs_eq_natAbs]; exact_mod_cast this
        exact mul_le_mul h1 h2 (abs_nonneg _) (by norm_num)
    _ = (d : Int) * (2047 * 4096) := by simp

/-- The middle digit, in the integers. -/
theorem mid_int (h : CastRel c tab) {t x : Nat} (ht : t < T) (hx : x < JV) :
    0 ≤ midZ c x t ∧ midZ c x t < 2 ^ 16 := by
  obtain ⟨n, hn, he⟩ := h.mid t ht x hx
  have h1 := cell_bd h .wide (4 * d + x) t
  have h2 := cell_bd h .wide (4 * d + JV + x) t
  have hb : |midZ c x t - (n : Int)| < 2 ^ 63 := by
    unfold midZ off2
    rw [abs_lt]
    split <;> constructor <;> push_cast <;> omega
  have := int_eq_of_cast_eq he hb
  omega

theorem low_int (h : CastRel c tab) {t x : Nat} (ht : t < T) (hx : x < JV) :
    0 ≤ lowZ c x t ∧ lowZ c x t < 2 ^ 8 := by
  obtain ⟨n, hn, he⟩ := h.low t ht x hx
  have h1 := cell_bd h .wide (4 * d + 2 * JV + x) t
  have hb : |lowZ c x t - (n : Int)| < 2 ^ 63 := by
    unfold lowZ off1
    rw [abs_lt]
    split <;> constructor <;> push_cast <;> omega
  have := int_eq_of_cast_eq he hb
  omega

theorem tvZ_bd (h : CastRel c tab) (x t : Nat) : -(2 : Int) ^ 35 < tvZ c x t ∧ tvZ c x t < 2 ^ 35 := by
  have c0 := cell_bd h .wide (4 * d + 3 * JV + x) t
  have c1 := cell_bd h .wide (4 * d + 4 * JV + x) t
  have c2 := cell_bd h .wide (4 * d + 5 * JV + x) t
  unfold tvZ offE
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  constructor <;> push_cast <;> omega

/-- A key of the table, in the integers: the table value is the row of the middle digit. -/
theorem row_int (P : PlanFacts) (htab : TableOk tab) (h : CastRel c tab) {t x : Nat} (ht : t < T)
    (hx : x < JV) : tvZ c x t = (tab (midZ c x t).toNat : Int) := by
  obtain ⟨u, hu, he⟩ := h.row t ht x hx
  obtain ⟨hm0, hm1⟩ := mid_int h ht hx
  obtain ⟨hv0, hv1⟩ := tvZ_bd h x t
  have htu : tab u ≤ 2 ^ 24 := by have := (htab.2 u).2; rwa [P.hF] at this
  have hb : |midZ c x t + 2 ^ 16 * tvZ c x t - ((u : Int) + 2 ^ 16 * (tab u : Int))| < 2 ^ 63 := by
    rw [abs_lt]; constructor <;> omega
  have heq := int_eq_of_cast_eq he hb
  have hmu : (midZ c x t).toNat = u := by omega
  rw [hmu]; omega

theorem tv_range (P : PlanFacts) (htab : TableOk tab) (h : CastRel c tab) {t x : Nat} (ht : t < T)
    (hx : x < JV) : 1 ≤ tvZ c x t ∧ tvZ c x t ≤ 2 ^ 24 := by
  rw [row_int P htab h ht hx]
  have h1 := htab.2 (midZ c x t).toNat
  rw [P.hF] at h1
  constructor
  · exact_mod_cast h1.1
  · exact_mod_cast h1.2

/-- The top digit's equation, in the integers: the plan's second row «W-HD0». -/
theorem top_int (P : PlanFacts) (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (hA : ∀ t, t < T → ∀ k, k < d → (act c t k).natAbs ≤ 2047) (h : CastRel c tab) {t x : Nat}
    (ht : t < T)
    (hx : x < JV) : ∃ n : Nat, topNum c x t = 2 ^ (sh + 15) * (n : Int) := by
  obtain ⟨n, hn, he⟩ := h.top t ht x hx
  refine ⟨n, int_eq_of_cast_eq he ?_⟩
  obtain ⟨hm0, hm1⟩ := mid_int h ht hx
  obtain ⟨hl0, hl1⟩ := low_int h ht hx
  have hp := numZ_bd h .paid ht
  have ho := numZ_bd h .over ht
  simp only [Number.digits] at hp ho
  have hL1 := abs_le.mp (abs_logit_le hW hA ht (win t))
  have hL2 := abs_le.mp (abs_logit_le hW hA ht x)
  have hPW := P.hW
  unfold topNum liftZ BIG
  rw [abs_lt]
  rcases P.hsh with h7 | h8
  · rw [h7] at hPW ⊢
    split_ifs <;> constructor <;> push_cast <;> omega
  · rw [h8] at hPW ⊢
    split_ifs <;> constructor <;> push_cast <;> omega

theorem clip_int (P : PlanFacts) (h : CastRel c tab) {t : Nat} (ht : t < T)
    (hc : costed t = true) : numZ c .paid t + numZ c .slackClip t = (C : Int) := by
  have hp := numZ_bd h .paid ht
  have hs := numZ_bd h .slackClip ht
  simp only [Number.digits] at hp hs
  have hE := P.hE4
  refine int_eq_of_cast_eq (h.clip t ht hc) ?_
  rw [abs_lt]; constructor <;> omega

theorem table_int (P : PlanFacts) (htab : TableOk tab) (h : CastRel c tab) {t : Nat} (ht : t < T)
    (hc : costed t = true) :
    numZ c .slackTable t + (Finset.range JV).sum (fun x => tvZ c x t)
      = ((JV - V + 1 : Nat) : Int) * 2 ^ F := by
  have hs := numZ_bd h .slackTable ht
  simp only [Number.digits] at hs
  have h0 : 0 ≤ (Finset.range JV).sum (fun x => tvZ c x t) :=
    Finset.sum_nonneg fun x hx => by
      have := (tv_range P htab h ht (Finset.mem_range.mp hx)).1; omega
  have h1 : (Finset.range JV).sum (fun x => tvZ c x t) ≤ (JV : Int) * 2 ^ 24 := by
    have := Finset.sum_le_card_nsmul (Finset.range JV) (fun x => tvZ c x t) (2 ^ 24)
      fun x hx => (tv_range P htab h ht (Finset.mem_range.mp hx)).2
    simpa using this
  have hZ := P.hZ
  refine int_eq_of_cast_eq (h.table t ht hc) ?_
  rw [P.hF] at hZ ⊢
  rw [abs_lt]; constructor <;> omega

theorem RC_le_T : RC ≤ T := by unfold RC; omega

theorem mean_int (P : PlanFacts) (h : CastRel c tab) :
    (Finset.range T).sum (fun t => if costed t = true then
      numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t else 0)
      = (theta : Int) * (RC : Int) := by
  have hterm : ∀ t ∈ Finset.range T, 0 ≤ (if costed t = true then
      numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t else 0) ∧
      (if costed t = true then
      numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t else 0)
        ≤ 2 ^ 40 + 2 ^ 8 * (C : Int) + 2 ^ 40 := by
    intro t htm
    have ht := Finset.mem_range.mp htm
    have hp := numZ_bd h .paid ht
    have ho := numZ_bd h .over ht
    have hs := numZ_bd h .slackMean ht
    simp only [Number.digits] at hp ho hs
    have hC : (0 : Int) ≤ (C : Int) := Int.natCast_nonneg _
    have h1 : 0 ≤ (C : Int) * numZ c .over t := mul_nonneg hC ho.1
    have h2 : (C : Int) * numZ c .over t ≤ (C : Int) * 2 ^ 8 :=
      mul_le_mul_of_nonneg_left (by omega) hC
    split <;> constructor <;> omega
  have h0 := Finset.sum_nonneg fun t ht => (hterm t ht).1
  have h1 := Finset.sum_le_card_nsmul (Finset.range T) _ _ fun t ht => (hterm t ht).2
  rw [Finset.card_range, nsmul_eq_mul] at h1
  have h2 : (theta : Int) * (RC : Int) ≤ (theta : Int) * (T : Int) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast RC_le_T) (Int.natCast_nonneg _)
  have h3 : (0 : Int) ≤ (theta : Int) * (RC : Int) := by positivity
  have hE : ((T * (2 ^ 40 + 2 ^ 8 * C + 2 ^ 40) + theta * T : Nat) : Int) < 2 ^ 60 := by
    exact_mod_cast P.hE2
  push_cast at hE
  refine int_eq_of_cast_eq h.mean ?_
  rw [abs_lt]; constructor <;> linarith

theorem count_int (P : PlanFacts) (h : CastRel c tab) :
    (Finset.range T).sum (fun t => if costed t = true then
      numZ c .over t + numZ c .slackCap t else 0) = ((if RC > 0 then cap else 0 : Nat) : Int) := by
  have hterm : ∀ t ∈ Finset.range T, 0 ≤ (if costed t = true then
      numZ c .over t + numZ c .slackCap t else 0) ∧
      (if costed t = true then numZ c .over t + numZ c .slackCap t else 0)
        ≤ (2 ^ 8 + 2 ^ 16 : Int) := by
    intro t htm
    have ht := Finset.mem_range.mp htm
    have ho := numZ_bd h .over ht
    have hs := numZ_bd h .slackCap ht
    simp only [Number.digits] at ho hs
    split <;> constructor <;> omega
  have h0 := Finset.sum_nonneg fun t ht => (hterm t ht).1
  have h1 := Finset.sum_le_card_nsmul (Finset.range T) _ _ fun t ht => (hterm t ht).2
  rw [Finset.card_range, nsmul_eq_mul] at h1
  have h2 : ((if RC > 0 then cap else 0 : Nat) : Int) ≤ (cap : Int) := by split <;> simp
  have h3 : (0 : Int) ≤ ((if RC > 0 then cap else 0 : Nat) : Int) := Int.natCast_nonneg _
  have hE : ((T * (2 ^ 8 + 2 ^ 16) + cap : Nat) : Int) < 2 ^ 60 := by exact_mod_cast P.hE3
  push_cast at hE
  refine int_eq_of_cast_eq h.count ?_
  rw [abs_lt]; constructor <;> linarith

/-- **FROM THE FIELD TO THE INTEGERS.** -/
theorem intRel_of_castRel (P : PlanFacts) (htab : TableOk tab)
    (hW : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12)
    (hA : ∀ t, t < T → ∀ k, k < d → (act c t k).natAbs ≤ 2047)
    (h : CastRel c tab) : IntRel c tab where
  bytes := h.bytes
  mid := fun _ ht _ hx => (mid_int h ht hx).1
  low := fun _ ht _ hx => (low_int h ht hx).1
  top := fun _ ht _ hx => top_int P hW hA h ht hx
  row := fun _ ht _ hx => row_int P htab h ht hx
  clip := fun _ ht hc => clip_int P h ht hc
  table := fun _ ht hc => table_int P htab h ht hc
  mean := mean_int P h
  count := count_int P h

end Bounds

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.intRel_of_castRel
