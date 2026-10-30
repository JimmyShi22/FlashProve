-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/Closed.lean: THE HEAD's FORMS AT THE CELLS, IN CLOSED FORM, AT ANY POINT (L2 of
the road). `Filled c`: the classes are filled from the cells as HeadLaw.lean fills them. Under it each
form's value is a sum over entries x and positions t of (the entry's weight) (the position's weight)
(the integer of Ints.lean at x, t). Lemma 1 takes these sums at the corners; Lemma 2a compares them.
-/
import Mathlib
import Johnson.Desc.Kinds.Law.Corner

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E invE)
open Norm (lt ls d lPd T S2)

variable [Sizes] [Policy] [Request] [Token]

/-- The number of positions with a cost. -/
theorem RC_eq : (RC : K) = (Finset.range T).sum fun t => if costed t = true then (1 : K) else 0 := by
  have h : (Finset.range T).filter (fun t => costed t = true) = Finset.Ico r (min e (T - 1)) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico, costed, checked,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [Finset.sum_boole, h, Nat.card_Ico]
  rfl

/-- An entry of a whole block lies below the length. -/
theorem block_lt {n S i j : Nat} (hi : i < n / S) (hj : j < S) : S * i + j < n := by
  have h1 : S * (i + 1) ≤ S * (n / S) := Nat.mul_le_mul_left S hi
  have h2 : S * (n / S) ≤ n := Nat.mul_div_le n S
  have h3 : S * (i + 1) = S * i + S := Nat.mul_succ S i
  omega

section In
variable [FinalNorm.In] [In]

/-- The letters that come in are the weights that they are taken for: BELOW A KEY's LENGTH an entry's
weight is its block's times the equality weight of zl at its place in the block; the three sums are
sums of the entries' weights. -/
structure FilledIn : Prop where
  hew : ∀ k x, x < len k → ew k x = ewh k (x / S2) * eq FinalNorm.zl (x % S2)
  hwsum : ∀ k, wsum k = sumTo (len k) fun x => ew k x
  hwx : ∀ k, wx k = sumTo (len k) fun x => if first k + x < V then ew k x else 0
  hbelow : ∀ v, v ≤ V → below v = sumTo v fun x => ew .marginTop x

variable {c : Cells}

/-- The weight of position t. -/
def Wt (t : Nat) : K := rd (eq FinalNorm.zt t)
/-- The weight of entry x of key k. -/
def Ut (k : Key) (x : Nat) : K := rd (ew k x)
/-- The weight of a position with a cost. -/
def Ph (t : Nat) : K := if costed t = true then Wt t else 0

theorem rd_phiC (t : Nat) : rd (phiC t) = Ph t := by
  unfold phiC Ph Wt
  split
  · rfl
  · exact rd_zero

theorem rd_ERC : rd ERC = (Finset.range T).sum Ph := by
  unfold ERC
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun t _ => rd_phiC t

theorem rd_readAt_short (c : Cells) (m : Matrix) (g : Nat → E) (i : Nat) :
    rd (readAt c (m, .short g) i)
      = (Finset.range T).sum fun t => rd (g t) * ((c.cell m i t : Int) : K) := by
  show rd (sumTo T fun t => g t * ofInt (c.cell m i t)) = _
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun t _ => by rw [rd_mul, rd_ofInt]

theorem rd_readAt_long (c : Cells) (m : Matrix) (f g : Nat → E) (i : Nat) :
    rd (readAt c (m, .long f g) i) = (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
      rd (f j) * rd (g t) * ((c.cell m (S2 * i + j) t : Int) : K) := by
  show rd (sumTo S2 fun j => sumTo T fun t => f j * g t * ofInt (c.cell m (S2 * i + j) t)) = _
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [rd_sumTo]
  exact Finset.sum_congr rfl fun t _ => by rw [rd_mul, rd_mul, rd_ofInt]

theorem rd_ON : rd ON = (Finset.range T).sum fun t => if checked t = true then Wt t else 0 := by
  unfold ON
  rw [rd_sumTo]
  refine Finset.sum_congr rfl fun t _ => ?_
  split
  · rfl
  · exact rd_zero

theorem rd_wx (hI : FilledIn) (k : Key) :
    rd (wx k) = (Finset.range (len k)).sum fun x => if first k + x < V then Ut k x else 0 := by
  rw [hI.hwx, rd_sumTo]
  refine Finset.sum_congr rfl fun x _ => ?_
  split
  · rfl
  · exact rd_zero

theorem rd_wsum (hI : FilledIn) (k : Key) : rd (wsum k) = (Finset.range (len k)).sum (Ut k) := by
  rw [hI.hwsum, rd_sumTo]; rfl

theorem rd_below (hI : FilledIn) (v : Nat) (hv : v ≤ V) :
    rd (below v) = (Finset.range v).sum (Ut .marginTop) := by
  rw [hI.hbelow v hv, rd_sumTo]; rfl

theorem S2_pos : 0 < S2 := by unfold S2; positivity

theorem Ut_block (hI : FilledIn) (k : Key) (i j : Nat) (hj : j < S2) (hx : S2 * i + j < len k) :
    Ut k (S2 * i + j) = rd (ewh k i) * rd (eq FinalNorm.zl j) := by
  unfold Ut
  rw [hI.hew k _ hx, rd_mul]
  have h1 : (S2 * i + j) / S2 = i := by
    rw [Nat.mul_add_div S2_pos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have h2 : (S2 * i + j) % S2 = j := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
  rw [h1, h2]

theorem S2_dvd_JV : S2 ∣ JV := ⟨(V + S2 - 1) / S2, by unfold JV; exact Nat.mul_comm _ _⟩

theorem S2_dvd_len (P : PlanFacts) (k : Key) : S2 ∣ len k := by
  have hJ := S2_dvd_JV
  have ha : S2 ∣ JVa := Nat.dvd_of_mod_eq_zero P.hJVa
  cases k <;> simp only [len]
  · exact hJ
  · exact hJ
  · exact hJ
  · exact ha
  · exact Nat.dvd_sub hJ ha

/-- The weights of the positions add up to 1. -/
theorem sum_Wt (hzt : (FinalNorm.zt).size = lt) : (Finset.range T).sum Wt = 1 := by
  have := sum_rd_eq FinalNorm.zt
  rw [hzt] at this
  exact this

theorem sum_range_ite_lt {M : Type} [AddCommMonoid M] {a b : Nat} (h : a ≤ b) (f : Nat → M) :
    (Finset.range b).sum (fun x => if x < a then f x else 0) = (Finset.range a).sum f := by
  rw [← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem two_ne_zero_K : (2 : K) ≠ 0 := by
  intro h
  have h2 : ((2 : Int) : K) = ((0 : Int) : K) := by push_cast; exact h
  have := int_eq_of_cast_eq h2 (by norm_num)
  omega

theorem cast_logit (c : Cells) (t v : Nat) : ((logit c t v : Int) : K)
    = (Finset.range d).sum fun k => ((act c t k : Int) : K) * ((c.Wh k v : Int) : K) := by
  unfold logit
  rw [sumZ_eq]
  push_cast
  rfl

theorem rd_UH (hI : FilledIn) (k t : Nat) : rd (UH c k t) = if checked t = true then
    (Finset.range JV).sum (fun x => if x < V then
      Ut .marginTop x * (((c.Wh k (win t) : Int) : K) - ((c.Wh k x : Int) : K)) else 0) else 0 := by
  unfold UH
  split
  · rw [rd_sub, rd_mul, rd_ofInt, rd_wx hI, rd_sumTo]
    have hlen : len Key.marginTop = JV := rfl
    have h1 : (Finset.range V).sum (fun v => rd (ew Key.marginTop v * ofInt (c.Wh k v)))
        = (Finset.range JV).sum fun x => if x < V then
            Ut .marginTop x * ((c.Wh k x : Int) : K) else 0 := by
      rw [sum_range_ite_lt V_le_JV]
      exact Finset.sum_congr rfl fun v _ => by rw [rd_mul, rd_ofInt]; rfl
    rw [h1, hlen, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [first, Nat.zero_add]
    split <;> ring
  · exact rd_zero

theorem rd_trueSum (hI : FilledIn) : rd (trueSum c)
    = (Finset.range JV).sum fun x => (Finset.range T).sum fun t => Ut .marginTop x * Wt t *
        (((if x < V ∧ checked t = true then logit c t (win t) - logit c t x else 0 : Int)) : K) := by
  unfold trueSum
  rw [rd_sumTo]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [rd_sumTo]
  simp only [rd_mul, rd_ofInt, rd_UH hI]
  by_cases hc : checked t = true
  · simp only [hc, if_true, and_true, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x < V
    · simp only [hx, if_true]
      push_cast
      rw [cast_logit, cast_logit, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      unfold Wt
      ring
    · simp [hx]
  · simp [hc]

theorem rd_ties (hI : FilledIn) (hreq : Request.ok = true) (hy : y < V) :
    rd (sumTo T fun t => if checked t = true then eq FinalNorm.zt t * below (win t) else (0 : E))
      = (Finset.range JV).sum fun x => (Finset.range T).sum fun t => Ut .marginTop x * Wt t *
        (((if checked t = true ∧ x < win t then 1 else 0 : Int)) : K) := by
  rw [rd_sumTo]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : checked t = true
  · simp only [hc, if_true, true_and]
    have hw : win t ≤ JV := le_trans (le_of_lt (win_lt hreq hy t)) V_le_JV
    rw [rd_mul, rd_below hI _ (le_of_lt (win_lt hreq hy t)), ← sum_range_ite_lt hw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold Wt
    by_cases hx : x < win t <;> simp [hx]
    ring
  · simp [hc, rd_zero]

end In

section Filled
variable [FinalNorm.In] [In] [Heard] [Reads]

/-- The classes are filled from the cells. -/
structure Filled (c : Cells) : Prop where
  hentry : ∀ r i, entry r i = ((readAt c r.of i : E) : Form)
  hclaimed : logits.claimed.var = ((invE (2 ^ lPd) * trueSum c : E) : Form)
  hin : FilledIn

variable {c : Cells}

/-- A number under the weights of the positions with a cost. -/
theorem cv_atCosts (hF : Filled c) (n : Number) :
    cv (atCosts n) = (Finset.range T).sum fun t => Ph t * ((numZ c n t : Int) : K) := by
  unfold atCosts
  rw [cv_sumTo]
  have h1 : ∀ l, cv ((256 : Nat) ^ l • (entry Read.rowAtCosts (NR + n.digits.1 + l) + off1 * ERC))
      = (Finset.range T).sum fun t =>
          Ph t * ((256 : K) ^ l * (((c.cell .row (NR + n.digits.1 + l) t : Int) : K) + 128)) := by
    intro l
    rw [cv_smulN, cv_addE, rd_nmul, hF.hentry, cv_coe, rd_ERC]
    show _ * (rd (readAt c (.row, .short phiC) _) + _) = _
    rw [rd_readAt_short, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [rd_phiC]
    unfold off1
    push_cast
    ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum]
  unfold numZ
  push_cast
  rfl

/-- A number, summed plainly over the positions with a cost. -/
theorem cv_summed (hF : Filled c) (n : Number) :
    cv (summed n) = (Finset.range T).sum fun t =>
      if costed t = true then ((numZ c n t : Int) : K) else 0 := by
  unfold summed
  rw [cv_sumTo]
  have h1 : ∀ l, cv ((256 : Nat) ^ l • (entry Read.rowCount (NR + n.digits.1 + l) + off1 * RC))
      = (Finset.range T).sum fun t => if costed t = true then
          ((256 : K) ^ l * (((c.cell .row (NR + n.digits.1 + l) t : Int) : K) + 128)) else 0 := by
    intro l
    rw [cv_smulN, cv_addN, hF.hentry, cv_coe]
    show _ * (rd (readAt c (.row, .short fun t => if costed t then 1 else 0) _) + _) = _
    rw [rd_readAt_short]
    push_cast
    rw [RC_eq, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    unfold off1
    by_cases hc : costed t = true
    · simp only [hc, if_true, rd_one]; push_cast; ring
    · simp only [hc, if_false, rd_zero, Bool.false_eq_true]; ring
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : costed t = true
  · simp only [hc, if_true]
    unfold numZ
    push_cast
    rfl
  · simp [hc]

/-- A number that wide holds in limbs, under a key's weights: blocks become entries. -/
theorem cv_wideAt (hF : Filled c) (k : Key) (f0 nl stride : Nat) (hlen : S2 ∣ len k)
    (hdiv : ∀ l, l < nl → S2 ∣ f0 + l * stride) :
    cv (wideAt k f0 nl stride) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * (Finset.range nl).sum fun l =>
        (256 : K) ^ l * ((c.cell .wide (f0 + l * stride + x) t : Int) : K) := by
  unfold wideAt
  rw [cv_sumTo]
  conv_rhs => rw [← Nat.div_mul_cancel hlen, ← sum_blocks S2 _ (len k / S2)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [cv_sumTo]
  have h1 : ∀ l ∈ Finset.range nl,
      cv (((256 : E) ^ l * ewh k i) • entry Read.wideAtKeys ((f0 + l * stride) / S2 + i))
        = (Finset.range S2).sum fun j => (Finset.range T).sum fun t =>
          Ut k (S2 * i + j) * Wt t *
            ((256 : K) ^ l * ((c.cell .wide (f0 + l * stride + (S2 * i + j)) t : Int) : K)) := by
    intro l hl
    rw [cv_smulE, rd_mul, rd_pow, rd_ofNat, hF.hentry, cv_coe]
    show _ * rd (readAt c (.wide, .long (eq FinalNorm.zl) (eq FinalNorm.zt)) _) = _
    rw [rd_readAt_long, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hidx : S2 * ((f0 + l * stride) / S2 + i) + j = f0 + l * stride + (S2 * i + j) := by
      rw [Nat.mul_add, Nat.mul_div_cancel' (hdiv l (Finset.mem_range.mp hl))]; omega
    rw [hidx, Ut_block hF.hin k i j (Finset.mem_range.mp hj)
      (block_lt (Finset.mem_range.mp hi) (Finset.mem_range.mp hj))]
    unfold Wt
    push_cast
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.mul_sum]

/-- The middle digit under a key's weights. -/
theorem cv_mid (P : PlanFacts) (hF : Filled c) (k : Key) (v0 : Nat) (hv : first k = v0)
    (hv0 : S2 ∣ v0) :
    cv (mid k v0) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * ((midZ c (v0 + x) t : Int) : K) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hdiv : ∀ l, l < 2 → S2 ∣ 4 * d + v0 + l * JV := fun l _ =>
    Dvd.dvd.add (Dvd.dvd.add (Dvd.dvd.mul_left hd 4) hv0) (Dvd.dvd.mul_left S2_dvd_JV l)
  unfold mid
  rw [cv_Eadd, rd_mul, rd_mul, rd_natCast, rd_wx hF.hin, rd_ON,
    cv_wideAt hF k _ _ _ (S2_dvd_len P k) hdiv, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e0 : 4 * d + v0 + 0 * JV + x = 4 * d + (v0 + x) := by ring
  have e1 : 4 * d + v0 + 1 * JV + x = 4 * d + JV + (v0 + x) := by ring
  rw [hv, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, e0, e1]
  unfold midZ
  by_cases h1 : v0 + x < V <;> by_cases h2 : checked t = true <;> simp [h1, h2] <;> ring

/-- The low digit, for a key whose first entry is 0. -/
theorem cv_low (P : PlanFacts) (hF : Filled c) (k : Key) (hv : first k = 0) :
    cv (low k) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * ((lowZ c x t : Int) : K) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hdiv : ∀ l, l < 1 → S2 ∣ 4 * d + 2 * JV + l * JV := fun l _ =>
    Dvd.dvd.add (Dvd.dvd.add (Dvd.dvd.mul_left hd 4) (Dvd.dvd.mul_left S2_dvd_JV 2))
      (Dvd.dvd.mul_left S2_dvd_JV l)
  unfold low
  rw [cv_Eadd, rd_mul, rd_mul, rd_natCast, rd_wx hF.hin, rd_ON,
    cv_wideAt hF k _ _ _ (S2_dvd_len P k) hdiv, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have e0 : 4 * d + 2 * JV + 0 * JV + x = 4 * d + 2 * JV + x := by ring
  rw [hv, Finset.sum_range_succ, Finset.sum_range_zero, e0, Nat.zero_add]
  unfold lowZ
  by_cases h1 : x < V <;> by_cases h2 : checked t = true <;> simp [h1, h2] <;> ring

/-- The table value under a key's weights. -/
theorem cv_tableValue (P : PlanFacts) (hF : Filled c) (hzt : (FinalNorm.zt).size = lt) (k : Key)
    (v0 : Nat) (hv0 : S2 ∣ v0) :
    cv (tableValue k v0) = (Finset.range (len k)).sum fun x => (Finset.range T).sum fun t =>
      Ut k x * Wt t * ((tvZ c (v0 + x) t : Int) : K) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hdiv : ∀ l, l < 3 → S2 ∣ 4 * d + 3 * JV + v0 + l * JV := fun l _ =>
    Dvd.dvd.add (Dvd.dvd.add (Dvd.dvd.add (Dvd.dvd.mul_left hd 4) (Dvd.dvd.mul_left S2_dvd_JV 3))
      hv0) (Dvd.dvd.mul_left S2_dvd_JV l)
  unfold tableValue
  rw [cv_Eadd, rd_nmul, rd_wsum hF.hin, cv_wideAt hF k _ _ _ (S2_dvd_len P k) hdiv, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h1 : (offE : K) * Ut k x = (Finset.range T).sum fun t => Ut k x * Wt t * (offE : K) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_Wt hzt]; ring
  rw [h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hidx : ∀ l, 4 * d + 3 * JV + v0 + l * JV + x = 4 * d + (3 + l) * JV + (v0 + x) := by
    intro l; ring
  simp only [hidx]
  unfold tvZ
  push_cast
  ring

theorem wx_lift (hF : Filled c) :
    rd (wx .marginTop) * (cv (atCosts .paid) + (BIG : K) * cv (atCosts .over))
      = (Finset.range JV).sum fun x => (Finset.range T).sum fun t => Ut .marginTop x * Wt t *
        (((if x < V ∧ costed t = true then liftZ c t else 0 : Int)) : K) := by
  have hlen : len Key.marginTop = JV := rfl
  rw [rd_wx hF.hin, cv_atCosts hF, cv_atCosts hF, Finset.mul_sum, ← Finset.sum_add_distrib,
    Finset.sum_mul_sum, hlen]
  refine Finset.sum_congr rfl fun x _ => ?_
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [first, Nat.zero_add]
  unfold Ph liftZ
  by_cases hx : x < V <;> by_cases hc : costed t = true <;> simp [hx, hc]
  ring

/-- **The top digit's key**: 2^-(sh+15) times the margin less its two lower digits. -/
theorem cv_top (P : PlanFacts) (hF : Filled c) (hreq : Request.ok = true) (hy : y < V) :
    cv top = ((2 : K) ^ (sh + 15))⁻¹ * (Finset.range JV).sum fun x => (Finset.range T).sum fun t =>
      Ut .marginTop x * Wt t * ((topNum c x t : Int) : K) := by
  have hlen : len Key.marginTop = JV := rfl
  have hsplit : ∀ x t, Ut .marginTop x * Wt t * ((topNum c x t : Int) : K)
      = Ut .marginTop x * Wt t *
          (((if x < V ∧ checked t = true then logit c t (win t) - logit c t x else 0 : Int)) : K)
        + Ut .marginTop x * Wt t * (((if x < V ∧ costed t = true then liftZ c t else 0 : Int)) : K)
        - Ut .marginTop x * Wt t * (((if checked t = true ∧ x < win t then 1 else 0 : Int)) : K)
        - (2 : K) ^ sh * (Ut .marginTop x * Wt t * ((midZ c (0 + x) t : Int) : K))
        - Ut .marginTop x * Wt t * ((lowZ c x t : Int) : K) := by
    intro x t
    unfold topNum
    rw [Nat.zero_add]
    push_cast
    ring
  simp only [hsplit, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [← rd_trueSum hF.hin, ← wx_lift hF, ← rd_ties hF.hin hreq hy, ← hlen,
    ← cv_mid P hF .marginTop 0 rfl (dvd_zero _), ← cv_low P hF .marginTop rfl]
  simp only [top, cv_smulE, cv_sub, cv_add, cv_smulN, cv_ofConst, hF.hclaimed, rd_mul,
    rd_inv, rd_pow]
  have h2 : ((2 : K) ^ lPd) ≠ 0 := pow_ne_zero _ two_ne_zero_K
  have hr2 : rd (2 : E) = 2 := by rw [rd_ofNat]; norm_num
  push_cast
  rw [hr2, mul_inv_cancel_left₀ h2]

theorem cv_clip (hF : Filled c) : cv clip = (Finset.range T).sum fun t =>
    Ph t * ((numZ c .paid t + numZ c .slackClip t - (C : Int) : Int) : K) := by
  unfold clip
  rw [cv_subE, cv_add, rd_nmul, cv_atCosts hF, cv_atCosts hF, rd_ERC, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  push_cast
  ring

theorem cv_tableValuesAtCosts (P : PlanFacts) (hF : Filled c) :
    cv tableValuesAtCosts = (Finset.range T).sum fun t =>
      Ph t * (((Finset.range JV).sum (fun x => tvZ c x t) : Int) : K) := by
  have hd : S2 ∣ d := Nat.dvd_of_mod_eq_zero P.hdS
  have hdiv : ∀ l, S2 ∣ 4 * d + (3 + l) * JV := fun l =>
    Dvd.dvd.add (Dvd.dvd.mul_left hd 4) (Dvd.dvd.mul_left S2_dvd_JV _)
  have h1 : ∀ l, cv (sumTo (JV / S2) fun i =>
      (256 : Nat) ^ l • entry Read.wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
      = (Finset.range T).sum fun t => Ph t * (Finset.range JV).sum fun x =>
          (256 : K) ^ l * ((c.cell .wide (4 * d + (3 + l) * JV + x) t : Int) : K) := by
    intro l
    rw [cv_sumTo]
    have h2 : ∀ i, cv ((256 : Nat) ^ l • entry Read.wideAtCosts ((4 * d + (3 + l) * JV) / S2 + i))
        = (Finset.range S2).sum fun j => (Finset.range T).sum fun t => Ph t *
            ((256 : K) ^ l * ((c.cell .wide (4 * d + (3 + l) * JV + (S2 * i + j)) t : Int) : K)) := by
      intro i
      rw [cv_smulN, hF.hentry, cv_coe]
      show _ * rd (readAt c (.wide, .long (fun _ => 1) phiC) _) = _
      rw [rd_readAt_long, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      have hidx : S2 * ((4 * d + (3 + l) * JV) / S2 + i) + j
          = 4 * d + (3 + l) * JV + (S2 * i + j) := by
        rw [Nat.mul_add, Nat.mul_div_cancel' (hdiv l)]; omega
      rw [hidx, rd_one, rd_phiC]
      push_cast
      ring
    simp only [h2]
    rw [sum_blocks S2 (fun x => (Finset.range T).sum fun t => Ph t *
      ((256 : K) ^ l * ((c.cell .wide (4 * d + (3 + l) * JV + x) t : Int) : K))) (JV / S2),
      Nat.div_mul_cancel S2_dvd_JV, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum]
  unfold tableValuesAtCosts
  rw [cv_Eadd, rd_nmul, rd_ERC, cv_sumTo]
  simp only [h1]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Finset.mul_sum, Finset.sum_comm]
  unfold tvZ
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem cv_table (P : PlanFacts) (hF : Filled c) : cv table = (Finset.range T).sum fun t =>
    Ph t * ((numZ c .slackTable t + (Finset.range JV).sum (fun x => tvZ c x t)
      - ((JV - V + 1 : Nat) : Int) * 2 ^ F : Int) : K) := by
  unfold table
  rw [cv_subE, cv_add, rd_nmul, cv_atCosts hF, cv_tableValuesAtCosts P hF, rd_ERC, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  push_cast
  ring

theorem cv_mean (hF : Filled c) : cv mean = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .paid t + (C : Int) * numZ c .over t + numZ c .slackMean t
    else 0) - (theta : Int) * (RC : Int) : Int) : K) := by
  unfold mean
  rw [cv_subN, cv_add, cv_add, cv_smulN, cv_summed hF, cv_summed hF, cv_summed hF, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

theorem cv_count (hF : Filled c) : cv count = (((Finset.range T).sum (fun t =>
    if costed t = true then numZ c .over t + numZ c .slackCap t else 0)
      - ((if RC > 0 then cap else 0 : Nat) : Int) : Int) : K) := by
  unfold count
  rw [cv_sub, cv_add, cv_natCast, cv_summed hF, cv_summed hF, ← Finset.sum_add_distrib]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  split <;> simp

end Filled

end VerifiableInference.Desc.Kinds.Head.Law
