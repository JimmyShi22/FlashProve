-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Ints.lean: LEMMA 1's LAST STEP, IN INTEGERS ALONE (L5 of the road).
The integers that the head's forms hold at a corner (`midZ`, `lowZ`, `tvZ`, `numZ`, `topNum`); what
the step from the field to the integers must deliver of them (`IntRel`); and the theorem
`says_of_intRel`: IntRel gives (a), (b), (c) of Head.lean's head. No field element occurs here.
-/
import Mathlib
import Johnson.Desc.Kinds.HeadLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open Norm (lt ls d lPd T S2)

/-! ## The three folds of `Says` -/

theorem sumZ_eq (n : Nat) (f : Nat → Int) : sumZ n f = (Finset.range n).sum f := by
  unfold sumZ
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
    simp

theorem foldlMax_le (n : Nat) (g : Nat → Int) (B : Int) :
    (List.range n).foldl (fun m v => max m (g v)) 0 ≤ B ↔ 0 ≤ B ∧ ∀ v, v < n → g v ≤ B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, max_le_iff, ih]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨h0, fun v hv => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h | h
      · exact h1 v h
      · subst h; exact h2
    · rintro ⟨h0, h1⟩
      exact ⟨⟨h0, fun v hv => h1 v (Nat.lt_succ_of_lt hv)⟩, h1 n (Nat.lt_succ_self n)⟩

theorem foldlMax_nonneg (n : Nat) (g : Nat → Int) :
    0 ≤ (List.range n).foldl (fun m v => max m (g v)) 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    exact le_trans ih (le_max_left _ _)

theorem filter_length_eq (n : Nat) (p : Nat → Bool) :
    (((List.range n).filter p).length : Int)
      = (Finset.range n).sum fun t => if p t = true then (1 : Int) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.filter_append, List.length_append, Finset.sum_range_succ]
    push_cast
    rw [ih]
    by_cases h : p n = true <;> simp [h]

variable [Sizes] [Policy] [Request] [Token]

/-! ## The integers at a corner -/

/-- A hidden number of position t: its digits, each a cell and 128. -/
def numZ (c : Cells) (n : Number) (t : Nat) : Int :=
  (Finset.range n.digits.2).sum fun l => 256 ^ l * (c.cell .row (NR + n.digits.1 + l) t + 128)

/-- The margin's middle digit at entry x and position t. -/
def midZ (c : Cells) (x t : Nat) : Int :=
  (if x < V ∧ checked t = true then (off2 : Int) else 0)
    + (c.cell .wide (4 * d + x) t + 256 * c.cell .wide (4 * d + JV + x) t)

/-- Its low digit. -/
def lowZ (c : Cells) (x t : Nat) : Int :=
  (if x < V ∧ checked t = true then (off1 : Int) else 0) + c.cell .wide (4 * d + 2 * JV + x) t

/-- The middle digit's table value. -/
def tvZ (c : Cells) (x t : Nat) : Int :=
  (offE : Int) + (Finset.range 3).sum fun l => 256 ^ l * c.cell .wide (4 * d + (3 + l) * JV + x) t

/-- What lifts every margin of a position with a cost. -/
def liftZ (c : Cells) (t : Nat) : Int := numZ c .paid t + (BIG : Int) * numZ c .over t

/-- 2^(sh+15) times the top digit: the margin less its two lower digits. -/
def topNum (c : Cells) (x t : Nat) : Int :=
  (if x < V ∧ checked t = true then logit c t (win t) - logit c t x else 0)
    + (if x < V ∧ costed t = true then liftZ c t else 0)
    - (if checked t = true ∧ x < win t then 1 else 0)
    - 2 ^ sh * midZ c x t - lowZ c x t

/-- WHAT THE STEP FROM THE FIELD TO THE INTEGERS DELIVERS. -/
structure IntRel (c : Cells) (tab : Nat → Nat) : Prop where
  bytes : ∀ t, t < T → ∀ j, j < 21 →
    0 ≤ c.cell .row (NR + j) t + 128 ∧ c.cell .row (NR + j) t + 128 < 256
  mid : ∀ t, t < T → ∀ x, x < JV → 0 ≤ midZ c x t
  low : ∀ t, t < T → ∀ x, x < JV → 0 ≤ lowZ c x t
  top : ∀ t, t < T → ∀ x, x < JV → ∃ n : Nat, topNum c x t = 2 ^ (sh + 15) * (n : Int)
  row : ∀ t, t < T → ∀ x, x < JV → tvZ c x t = (tab (midZ c x t).toNat : Int)
  clip : ∀ t, t < T → costed t = true → numZ c .paid t + numZ c .slackClip t = (C : Int)
  table : ∀ t, t < T → costed t = true →
    numZ c .slackTable t + (Finset.range JV).sum (fun x => tvZ c x t)
      = ((JV - V + 1 : Nat) : Int) * 2 ^ F
  mean : (Finset.range T).sum (fun t => if costed t = true then
      numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t else 0)
      = (theta : Int) * (RC : Int)
  count : (Finset.range T).sum (fun t => if costed t = true then
      numZ c .over t + numZ c .slackCap t else 0) = ((if RC > 0 then cap else 0 : Nat) : Int)

/-! ## Small facts -/

theorem V_le_JV : V ≤ JV := by
  unfold JV
  have hS : 0 < S2 := by unfold S2; positivity
  have h := Nat.div_add_mod (V + S2 - 1) S2
  have h2 := Nat.mod_lt (V + S2 - 1) hS
  have h3 : S2 * ((V + S2 - 1) / S2) = (V + S2 - 1) / S2 * S2 := Nat.mul_comm _ _
  omega

theorem checked_of_costed {t : Nat} (h : costed t = true) : checked t = true := by
  unfold costed at h
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem win_lt (hreq : Request.ok = true) (hy : y < V) (t : Nat) : win t < V := by
  unfold win
  split
  · rename_i h
    unfold Request.ok at hreq
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hreq
    exact hreq.2 _ h
  · exact hy

theorem numZ_nonneg {c : Cells} {tab : Nat → Nat} (h : IntRel c tab) (n : Number) {t : Nat}
    (ht : t < T) : 0 ≤ numZ c n t := by
  unfold numZ
  refine Finset.sum_nonneg fun l hl => ?_
  have hl' : n.digits.1 + l < 21 := by
    have := Finset.mem_range.mp hl
    cases n <;> simp only [Number.digits] at this ⊢ <;> omega
  have hb := (h.bytes t ht _ hl').1
  rw [← Nat.add_assoc] at hb
  positivity

/-! ## The argument -/

section Main
variable {c : Cells} {tab : Nat → Nat}

/-- At an entry from V on there is no margin: the three digits add up to 0, so the middle one is 0. -/
theorem mid_zero_of_pad (hreq : Request.ok = true) (hy : y < V) (h : IntRel c tab) {t x : Nat}
    (ht : t < T) (hx : x < JV) (hV : V ≤ x) : midZ c x t = 0 := by
  obtain ⟨n, hn⟩ := h.top t ht x hx
  have hm := h.mid t ht x hx
  have hl := h.low t ht x hx
  have hw := win_lt hreq hy t
  have h1 : ¬ (x < V ∧ checked t = true) := fun hh => by omega
  have h2 : ¬ (x < V ∧ costed t = true) := fun hh => by omega
  have h3 : ¬ (checked t = true ∧ x < win t) := fun hh => by omega
  unfold topNum at hn
  rw [if_neg h1, if_neg h2, if_neg h3] at hn
  have hp : (0 : Int) < 2 ^ sh := by positivity
  have hq : (0 : Int) ≤ 2 ^ (sh + 15) * (n : Int) := by positivity
  have h4 : 2 ^ sh * midZ c x t ≤ 0 := by linarith
  exact le_antisymm (nonpos_of_mul_nonpos_right h4 hp) hm

/-- At a real pair the margin is its three digits. -/
theorem margin_eq (h : IntRel c tab) {t x : Nat} (ht : t < T) (hx : x < V)
    (hc : checked t = true) : ∃ n : Nat,
    logit c t (win t) - logit c t x + (if costed t = true then liftZ c t else 0)
        - (if x < win t then 1 else 0)
      = lowZ c x t + 2 ^ sh * midZ c x t + 2 ^ (sh + 15) * (n : Int) := by
  obtain ⟨n, hn⟩ := h.top t ht x (lt_of_lt_of_le hx V_le_JV)
  refine ⟨n, ?_⟩
  unfold topNum at hn
  rw [if_pos ⟨hx, hc⟩] at hn
  by_cases hk : costed t = true
  · by_cases hw : x < win t
    · rw [if_pos ⟨hx, hk⟩, if_pos ⟨hc, hw⟩] at hn
      rw [if_pos hk, if_pos hw]; linarith
    · rw [if_pos ⟨hx, hk⟩, if_neg (fun hh => hw hh.2)] at hn
      rw [if_pos hk, if_neg hw]; linarith
  · by_cases hw : x < win t
    · rw [if_neg (fun hh => hk hh.2), if_pos ⟨hc, hw⟩] at hn
      rw [if_neg hk, if_pos hw]; linarith
    · rw [if_neg (fun hh => hk hh.2), if_neg (fun hh => hw hh.2)] at hn
      rw [if_neg hk, if_neg hw]; linarith

theorem one_le_tv (htab : TableOk tab) (h : IntRel c tab) {t x : Nat} (ht : t < T) (hx : x < JV) :
    1 ≤ tvZ c x t := by
  rw [h.row t ht x hx]
  exact_mod_cast (htab.2 _).1

/-- At a position with a cost no middle digit of a vocabulary entry is 0: the table's values and a
slack that is not negative add up to 2^F, row 0 holds 2^F, every row at least 1, and V ≥ 2. -/
theorem one_le_mid (hV2 : 2 ≤ V) (hreq : Request.ok = true) (hy : y < V) (htab : TableOk tab)
    (h : IntRel c tab) {t x0 : Nat} (ht : t < T) (hc : costed t = true) (hx0 : x0 < V) :
    1 ≤ midZ c x0 t := by
  by_contra hlt
  have hx0J : x0 < JV := lt_of_lt_of_le hx0 V_le_JV
  have hm0 : midZ c x0 t = 0 := le_antisymm (by omega) (h.mid t ht x0 hx0J)
  have hsplit : (Finset.range JV).sum (fun x => tvZ c x t)
      = (Finset.range V).sum (fun x => tvZ c x t) + (Finset.Ico V JV).sum (fun x => tvZ c x t) := by
    rw [Finset.range_eq_Ico]
    exact (Finset.sum_Ico_consecutive _ (Nat.zero_le V) V_le_JV).symm
  have hpad : (Finset.Ico V JV).sum (fun x => tvZ c x t) = ((JV - V : Nat) : Int) * 2 ^ F := by
    have : ∀ x ∈ Finset.Ico V JV, tvZ c x t = (2 : Int) ^ F := by
      intro x hx
      obtain ⟨hxV, hxJ⟩ := Finset.mem_Ico.mp hx
      rw [h.row t ht x hxJ, mid_zero_of_pad hreq hy h ht hxJ hxV]
      simp only [Int.toNat_zero]
      rw [htab.1]; push_cast; rfl
    rw [Finset.sum_congr rfl this, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have hx0v : tvZ c x0 t = (2 : Int) ^ F := by
    rw [h.row t ht x0 hx0J, hm0]
    simp only [Int.toNat_zero]
    rw [htab.1]; push_cast; rfl
  obtain ⟨x1, hx1, hne⟩ : ∃ x1, x1 < V ∧ x1 ≠ x0 := by
    by_cases h0 : x0 = 0
    · exact ⟨1, by omega, by omega⟩
    · exact ⟨0, by omega, fun hh => h0 hh.symm⟩
  have hreal : (2 : Int) ^ F + 1 ≤ (Finset.range V).sum (fun x => tvZ c x t) := by
    rw [← Finset.add_sum_erase (Finset.range V) (fun x => tvZ c x t) (Finset.mem_range.mpr hx0)]
    have hmem : x1 ∈ (Finset.range V).erase x0 :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_range.mpr hx1⟩
    have hnn : ∀ i ∈ (Finset.range V).erase x0, 0 ≤ tvZ c i t := by
      intro i hi
      have hiV := Finset.mem_range.mp (Finset.mem_of_mem_erase hi)
      linarith [one_le_tv htab h ht (lt_of_lt_of_le hiV V_le_JV)]
    have h1 := Finset.single_le_sum hnn hmem
    have h2 := one_le_tv htab h ht (lt_of_lt_of_le hx1 V_le_JV)
    simp only at h1 ⊢
    rw [hx0v]; linarith
  have heq := h.table t ht hc
  have hs := numZ_nonneg h .slackTable ht
  rw [hsplit, hpad] at heq
  have hcast : ((JV - V + 1 : Nat) : Int) = ((JV - V : Nat) : Int) + 1 := by push_cast; ring
  rw [hcast] at heq
  nlinarith

/-- At a position with a cost: the cost is at most paid + BIG over. -/
theorem cost_le_lift (hV2 : 2 ≤ V) (hreq : Request.ok = true) (hy : y < V) (htab : TableOk tab)
    (h : IntRel c tab) {t : Nat} (ht : t < T) (hc : costed t = true) : cost c t ≤ liftZ c t := by
  have hck := checked_of_costed hc
  have hp : (0 : Int) < 2 ^ sh := by positivity
  have key : ∀ v, v < V →
      logit c t v - logit c t (win t) + (if v < win t then 1 else 0) ≤ liftZ c t - 2 ^ sh := by
    intro v hv
    obtain ⟨n, hn⟩ := margin_eq h ht hv hck
    rw [if_pos hc] at hn
    have hm := one_le_mid hV2 hreq hy htab h ht hc hv
    have hl := h.low t ht v (lt_of_lt_of_le hv V_le_JV)
    have hq : (0 : Int) ≤ 2 ^ (sh + 15) * (n : Int) := by positivity
    have hmm : (2 : Int) ^ sh ≤ 2 ^ sh * midZ c v t := le_mul_of_one_le_right hp.le hm
    linarith
  have h0 : 0 ≤ liftZ c t - 2 ^ sh := by
    have := key (win t) (win_lt hreq hy t)
    simpa using this
  have := (foldlMax_le V _ (liftZ c t - 2 ^ sh)).mpr ⟨h0, key⟩
  unfold cost gap
  linarith

/-- **FROM THE INTEGERS TO (a), (b), (c).** -/
theorem says_of_intRel (hV2 : 2 ≤ V) (hreq : Request.ok = true) (hy : y < V) (htab : TableOk tab)
    (h : IntRel c tab) : Says c := by
  have hC : (0 : Int) ≤ (C : Int) := Int.natCast_nonneg _
  have hBIG : (0 : Int) ≤ (BIG : Int) := Int.natCast_nonneg _
  refine ⟨?_, ?_, ?_⟩
  · -- (a)
    rw [sumZ_eq, ← h.mean]
    refine Finset.sum_le_sum fun t htm => ?_
    have ht := Finset.mem_range.mp htm
    by_cases hc : costed t = true
    · simp only [hc, if_true]
      have h1 := cost_le_lift hV2 hreq hy htab h ht hc
      have hp := numZ_nonneg h .paid ht
      have ho := numZ_nonneg h .over ht
      have hs := numZ_nonneg h .slackMean ht
      unfold liftZ at h1
      rcases eq_or_lt_of_le ho with ho0 | ho1
      · rw [← ho0] at h1 ⊢
        have := min_le_left (cost c t) (C : Int)
        linarith
      · have := min_le_right (cost c t) (C : Int)
        have h2 : (C : Int) ≤ (C : Int) * numZ c .over t :=
          le_mul_of_one_le_right hC (by omega)
        linarith
    · simp [hc]
  · -- (b)
    have hle : (((List.range T).filter
        fun t => costed t && decide ((C : Int) < cost c t)).length : Int) ≤ (cap : Int) := by
      rw [filter_length_eq]
      have hcnt : ((if RC > 0 then cap else 0 : Nat) : Int) ≤ (cap : Int) := by
        split <;> simp
      refine le_trans ?_ (le_trans (le_of_eq h.count) hcnt)
      refine Finset.sum_le_sum fun t htm => ?_
      have ht := Finset.mem_range.mp htm
      by_cases hc : costed t = true
      · simp only [hc, Bool.true_and, decide_eq_true_eq, if_true]
        have ho := numZ_nonneg h .over ht
        have hs := numZ_nonneg h .slackCap ht
        split
        · rename_i hgt
          have h1 := cost_le_lift hV2 hreq hy htab h ht hc
          have hk := h.clip t ht hc
          have hsc := numZ_nonneg h .slackClip ht
          unfold liftZ at h1
          have : 1 ≤ numZ c .over t := by
            by_contra hlt
            have h0 : numZ c .over t = 0 := le_antisymm (by omega) ho
            rw [h0] at h1
            linarith
          linarith
        · linarith
      · simp [hc]
    exact_mod_cast hle
  · -- (c)
    intro heT
    have hT : 0 < T := by unfold T; positivity
    have ht : T - 1 < T := by omega
    have hr : r < e := by
      unfold Request.ok at hreq
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hreq
      exact hreq.1.1
    have hck : checked (T - 1) = true := by
      unfold checked
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    have hnc : ¬ costed (T - 1) = true := by
      unfold costed
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      omega
    refine le_antisymm ?_ (foldlMax_nonneg _ _)
    unfold gap
    refine (foldlMax_le V _ 0).mpr ⟨le_refl _, fun v hv => ?_⟩
    obtain ⟨n, hn⟩ := margin_eq h ht hv hck
    rw [if_neg hnc] at hn
    have hm := h.mid (T - 1) ht v (lt_of_lt_of_le hv V_le_JV)
    have hl := h.low (T - 1) ht v (lt_of_lt_of_le hv V_le_JV)
    have hq : (0 : Int) ≤ 2 ^ (sh + 15) * (n : Int) :=
      mul_nonneg (pow_nonneg (by norm_num) _) (Int.natCast_nonneg n)
    have hmm : (0 : Int) ≤ 2 ^ sh * midZ c v (T - 1) := mul_nonneg (pow_nonneg (by norm_num) _) hm
    linarith only [hn, hl, hq, hmm]

end Main

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.says_of_intRel
