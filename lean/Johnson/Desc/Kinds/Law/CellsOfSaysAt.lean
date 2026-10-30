--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Kinds/Law/CellsOfSaysAt.lean.
WHAT IT DOES NOT SHOW. A TOY: a MADE-UP stream (feature 0 has the
value 1 at position 0 alone), MADE-UP weights (one weight 1, at feature 0 and entry 1), a made-up
request (Law/CellsWithCostsAt.lean's: 1024 tokens 0; positions 0 to 1022 checked), A MADE-UP POLICY
(C = theta = 300, cap = 1: NOT the stored example's 256 | 256 | 0), the table of two values, AT
WHICH THE FORMAT's TABLE PARTS IN ROW 1 (the same cells at the library's own table: Law/
CellsOfSaysEX.lean): no stored model, no file in scope, not what the prover's program lays. The
sizes are typed in as numbers there. |Wh| <= 2^12 stays a premise of both_of_says: no test or
relation of ours gives it
(HeadOk.lean: "a weight of the head below BW (the key file's)"). No soundness, no probability,
nothing on hiding.
LETTERS. No top statement has a letter under "there is": withAll c | withAll cY are functions |
definitions. sT is read by planOk alone.
WHAT IT IS. (1) Law/CellsOfSays.lean's clause on the activations FALLS: it follows from the norm's
relation. (2) Its premises are met by cells with A POSITION OVER, A TOP DIGIT THAT IS NOT 0 AND A
SLACK THAT DOES NOT DIVIDE.
  fair_of, says_withAll, slackA_eq, both_of_says   THE CONVERSE OF LEMMA 1, WHOLE, at the table of
                    two values: planOk, Request.ok, y < V, CellRelN c, Says c.toCells, |Wh| <= 2^12,
                    C < 2^40: CellRelN, CellRel at stepTab and Says hold of withAll c.
  policyY, bY, wY, cY   the letters.
  x_Y, v_Y, sig_Y, r_Y, yw_Y, act_Y, runs_Y, cellRelN_Y   the library's integer program on that
                    stream, in numbers; the norm's relation holds of cY.
  logit_Y, gap_Y, cost_Y, costA_Y   at position 0 entry 1 has the logit 71 and BEATS THE TOKEN: the
                    gap 71, the cost 327, above the clip; elsewhere the cost is 256.
  fair_Y            the text's own claim holds: the clipped costs' mean is at most 300; one position
                    is over, and the cap is 1.
  over_Y, paid_Y, spent_Y, totalZ_Y, total_Y, slack_Y, share_Y   position 0 is over and pays
                    nothing; the clipped costs add up to 261932; the slack 44968 is dealt as 44 at
                    the first 979 positions and 43 at the other 44.
  mar_Y0, digits_Y0   at position 0 the lifted margins are 2^37 and 2^37 - 71: top digit 16383 |
                    16382, middle digit 32768 | 65535, low digit 0 | 185.
  both_Y            BOTH RELATIONS ON CELLS HOLD WHOLE OF withAll cY, and the claim: no premise.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.CellsOfSays
import Johnson.Desc.Kinds.Law.CellsFromLogitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

/-- **Fair WITHOUT ITS CLAUSE ON THE ACTIVATIONS**: that they are at most 2047 follows from the
norm's relation (Law/NormProof.lean: act_le: the clamp's key). -/
theorem fair_of [Sizes] [Policy] [Request] [Token] {sT : Nat} (hplan : planOk sT = true)
    {c : NCells} (h : CellRelN c) (hs : Says c.toCells)
    (hw : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) (hC : C < 2 ^ 40) : Fair c :=
  ⟨hs, hw, fun _ ht _ hk => act_le sT c hplan h ht hk, hC⟩

/-- The claim speaks of the logits alone, and these are c's. -/
theorem says_withAll [Sizes] [Policy] [Request] [Token] {c : NCells} (h : Says c.toCells) :
    Says (withAll c).toCells :=
  ⟨by
    have := h.a
    simpa only [cost_withAll] using this, by
    have := h.b
    simpa only [cost_withAll] using this, fun e1 => h.c e1⟩

/-- The mean's slack, where the clipped costs' sum is known. (Stated with letters: at closed numbers
the kernel would set out to reckon the sum itself.) -/
theorem slackA_eq [Sizes] [Policy] [Request] [Token] (c : NCells) (S : Nat)
    (h : ((Finset.range Norm.T).sum fun t => if costed t = true then spentA c t else 0) = S) :
    slackA c = theta * RC - S := by
  unfold slackA
  rw [h]

/-- **THE CONVERSE OF LEMMA 1, WHOLE (HeadNormLaw.lean: Lemma1WholeStatement), AGAINST THE TABLE OF
TWO VALUES**: its premises and no bound on the activations. -/
theorem both_of_says [Sizes] [Policy] [Request] [Token] {sT : Nat} (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : y < V) {c : NCells} (h : CellRelN c) (hs : Says c.toCells)
    (hw : ∀ k v, (c.Wh k v).natAbs ≤ 2 ^ 12) (hC : C < 2 ^ 40) :
    CellRelN (withAll c) ∧ CellRel (withAll c).toCells stepTab ∧ Says (withAll c).toCells := by
  obtain ⟨a1, a2, _⟩ := both_withAll hplan hreq hy (fair_of hplan h hs hw hC) h
  exact ⟨a1, a2, says_withAll hs⟩

end VerifiableInference.Desc.Kinds.Head.Law

namespace VerifiableInference.Desc.Kinds.Head.Law.AtY

open Norm (lt ls d lPd T S2)
open Inst.Model (NORM.V NORM.sig NORM.R NORM.yw NORM.out rhu clamp isqrt Fits16)
open AtX (sizesX requestX tokenX request_X token_X win_X costed_X rc_X checked_X)

/-- A policy that lets one position be over: the clip and the mean's bound 300, the cap 1. -/
@[reducible] def policyY : Policy := { C := 300, theta := 300, cap := 1 }

attribute [local instance] sizesX policyY requestX tokenX

/-- The stream: at position 0 feature 0 has the value 1; else 0. -/
def bY : Nat → Nat → Nat → Int := fun t l k => if t = 0 ∧ l = 0 ∧ k = 0 then 1 else 0

/-- The head's weights: 1 at feature 0 and vocabulary entry 1, WHICH IS NOT THE TOKEN; else 0. -/
def wY : Nat → Nat → Int := fun k v => if k = 0 ∧ v = 1 then 1 else 0

theorem plan_Y : planOk 4 = true := by decide

theorem x_Y (t k : Nat) : xH bY t k = if t = 0 ∧ k = 0 then 1 else 0 := by
  unfold xH Inst.Model.Ledger.xOf bY
  by_cases h : t = 0 <;> by_cases h2 : k = 0 <;> simp [Finset.sum_range_succ, h, h2]

theorem v_Y (t : Nat) : NORM.V d (xH bY t) = if t = 0 then 1 else 0 := by
  unfold NORM.V
  rw [Finset.sum_eq_single 0]
  · rw [x_Y]
    by_cases h : t = 0 <;> simp [h]
  · intro j _ hj
    rw [x_Y, if_neg (fun h => hj h.2)]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by decide : 0 < d)) h

theorem sig_Y (t : Nat) : NORM.sig npOf d (xH bY t) = 231 := by
  unfold NORM.sig isqrt
  rw [v_Y]
  by_cases h : t = 0
  · rw [if_pos h]
    show ((Nat.sqrt ((1 : Int) + 53687).toNat : Nat) : Int) = 231
    have e : ((1 : Int) + 53687).toNat = 53688 := rfl
    have e2 : 231 = Nat.sqrt 53688 := Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩
    rw [e, ← e2]
    rfl
  · rw [if_neg h]
    show ((Nat.sqrt ((0 : Int) + 53687).toNat : Nat) : Int) = 231
    have e : ((0 : Int) + 53687).toNat = 53687 := rfl
    have e2 : 231 = Nat.sqrt 53687 := Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩
    rw [e, ← e2]
    rfl

theorem r_Y (t : Nat) : NORM.R npOf d (xH bY t) = 76156649543 := by
  unfold NORM.R
  rw [sig_Y]
  show ((2 : Int) ^ 44 + 231 / 2) / 231 = 76156649543
  norm_num

theorem yw_Y (t k : Nat) : awH bY t k = if t = 0 ∧ k = 0 then 71 else 0 := by
  unfold awH NORM.yw rhu
  rw [r_Y, x_Y]
  show ((if t = 0 ∧ k = 0 then (1 : Int) else 0) * 76156649543 + 2 ^ (30 - 1)) / 2 ^ 30 = _
  by_cases h : t = 0 ∧ k = 0
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

theorem act_Y (t k : Nat) : actH bY t k = if t = 0 ∧ k = 0 then 71 else 0 := by
  have e : actH bY t k = clamp 2047 (awH bY t k) := rfl
  rw [e, yw_Y]
  unfold clamp
  by_cases h : t = 0 ∧ k = 0
  · rw [if_pos h]
    norm_num
  · rw [if_neg h]
    norm_num

theorem runs_Y : RunsN bY := by
  refine ⟨fun t _ => ⟨by decide, by decide, by decide, by decide, fun l _ j _ => ?_, ?_⟩,
    fun t _ k _ => ?_⟩
  · unfold bY
    split <;> norm_num
  · have e : NORM.V d (Inst.Model.Ledger.xOf (bY t)) = if t = 0 then 1 else 0 := v_Y t
    rw [e]
    show (if t = 0 then (1 : Int) else 0) + 53687 < 2 ^ 78
    split <;> norm_num
  · rw [yw_Y]
    unfold Fits16
    split <;> norm_num

/-- The cells: the honest cells of that stream, with these weights. -/
def cY : NCells := { honestN bY with Wh := wY }

theorem cellRelN_Y : CellRelN cY := by
  have h := honest_meets (planN plan_Y) runs_Y
  exact ⟨h.small, h.smallS, h.rows, h.remLow, h.remHigh, h.clamp, h.digits⟩

theorem act_cY {t k : Nat} (ht : t < T) (hk : k < d) :
    act cY.toCells t k = if t = 0 ∧ k = 0 then 71 else 0 := by
  have e : act cY.toCells t k = act (honestN bY).toCells t k := rfl
  rw [e, act_honest ht hk, act_Y]

/-- **At position 0 the logit of entry 1 is 71; every other logit is 0.** -/
theorem logit_Y {t : Nat} (ht : t < T) (v : Nat) :
    logit cY.toCells t v = if t = 0 ∧ v = 1 then 71 else 0 := by
  unfold logit
  rw [sumZ_eq, Finset.sum_eq_single 0]
  · rw [act_cY ht (by decide)]
    show (if t = 0 ∧ (0 : Nat) = 0 then (71 : Int) else 0) *
      (if (0 : Nat) = 0 ∧ v = 1 then 1 else 0) = _
    by_cases h : t = 0 <;> by_cases h2 : v = 1 <;> simp [h, h2]
  · intro k _ hk
    show _ * (if k = 0 ∧ v = 1 then (1 : Int) else 0) = 0
    rw [if_neg (fun h => hk h.1), mul_zero]
  · intro h
    exact absurd (Finset.mem_range.mpr (by decide : 0 < d)) h

/-- **At position 0 another entry beats the token by 71.** -/
theorem gap_Y {t : Nat} (ht : t < T) : gap cY.toCells t = if t = 0 then 71 else 0 := by
  apply le_antisymm
  · unfold gap
    refine foldl_max_ub _ _ _ 0 (by split <;> norm_num) fun v _ => ?_
    rw [logit_Y ht, logit_Y ht, win_X, if_neg (Nat.not_lt_zero v),
      if_neg (fun h : t = 0 ∧ (0 : Nat) = 1 => absurd h.2 (by decide))]
    by_cases h : t = 0 <;> by_cases h2 : v = 1 <;> simp [h, h2]
  · by_cases h : t = 0
    · rw [if_pos h]
      have := le_gap cY.toCells t (v := 1) (by decide)
      rw [logit_Y ht, logit_Y ht, win_X, if_pos ⟨h, rfl⟩,
        if_neg (fun h : t = 0 ∧ (0 : Nat) = 1 => absurd h.2 (by decide)),
        if_neg (Nat.not_lt_zero 1)] at this
      linarith
    · rw [if_neg h]
      exact gap_nonneg _ _

theorem cost_Y {t : Nat} (ht : t < T) : cost cY.toCells t = if t = 0 then 327 else 256 := by
  unfold cost
  rw [gap_Y ht]
  show _ + (2 : Int) ^ 8 = _
  split <;> norm_num

theorem costA_Y {t : Nat} (ht : t < T) : costA cY t = if t = 0 then 327 else 256 := by
  unfold costA
  rw [cost_Y ht]
  split <;> rfl

theorem lt_T {t : Nat} (ht : t < 1023) : t < T := show t < 2 ^ 10 by omega

/-- **THE TEXT's OWN CLAIM HOLDS OF THESE CELLS, AND THE THREE BOUNDS.** -/
theorem fair_Y : Fair cY := by
  refine ⟨⟨?_, ?_, fun h => absurd h (by decide)⟩, fun k v => ?_, fun t ht k hk => ?_, by decide⟩
  · rw [sumZ_eq, ← sum_costed_const]
    refine Finset.sum_le_sum fun t _ => ?_
    by_cases hc : costed t = true
    · simp only [hc, if_true]
      exact min_le_right _ _
    · simp [hc]
  · rw [filter_len]
    have e : ((Finset.range T).sum fun t => if (costed t &&
        decide ((C : Int) < cost cY.toCells t)) = true then 1 else 0) =
        (Finset.range T).sum fun t => if t = 0 then 1 else 0 := by
      refine Finset.sum_congr rfl fun t ht => ?_
      have hT := Finset.mem_range.mp ht
      rw [cost_Y hT]
      by_cases h0 : t = 0
      · subst h0
        have hc : costed 0 = true := costed_X (by decide)
        rw [hc]
        decide
      · rw [if_neg h0, if_neg h0, if_neg]
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _
        decide
    rw [e, Finset.sum_ite_eq']
    split <;> decide
  · show (if k = 0 ∧ v = 1 then (1 : Int) else 0).natAbs ≤ 2 ^ 12
    split <;> decide
  · rw [act_cY ht hk]
    split <;> decide

/-- **Position 0 is over; no other is.** -/
theorem over_Y {t : Nat} (ht : t < 1023) : overA cY t = if t = 0 then 1 else 0 := by
  unfold overA
  rw [costA_Y (lt_T ht)]
  have hc := costed_X ht
  by_cases h : t = 0
  · rw [if_pos h, if_pos h, if_pos ⟨hc, by decide⟩]
  · rw [if_neg h, if_neg h, if_neg (fun x => absurd x.2 (by decide))]

/-- Position 0 pays nothing; every other pays its cost, 256. -/
theorem paid_Y {t : Nat} (ht : t < 1023) : paidA cY t = if t = 0 then 0 else 256 := by
  unfold paidA
  rw [costA_Y (lt_T ht)]
  have hc := costed_X ht
  by_cases h : t = 0
  · rw [if_pos h, if_pos h, if_neg (fun x => absurd x.2 (by decide))]
  · rw [if_neg h, if_neg h, if_pos ⟨hc, by decide⟩]

theorem costed_lt {t : Nat} (hc : costed t = true) : t < 1023 := checked_X (checked_of_costed hc)

theorem spent_Y {t : Nat} (hc : costed t = true) :
    (spentA cY t : Int) = 256 + if t = r then 44 else 0 := by
  unfold spentA
  rw [paid_Y (costed_lt hc), over_Y (costed_lt hc)]
  have hC : C = 300 := rfl
  have hr : r = 0 := rfl
  rw [hC, hr]
  by_cases h : t = 0 <;> simp [h]

theorem totalZ_Y :
    (((Finset.range T).sum fun t => if costed t = true then spentA cY t else 0 : Nat) : Int)
      = 256 * (RC : Int) + (if RC > 0 then 44 else 0) := by
  rw [Nat.cast_sum, ← sum_costed_const, ← sum_costed_first, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  by_cases hc : costed t = true
  · rw [if_pos hc, if_pos hc, if_pos hc, spent_Y hc]
  · simp [hc]

theorem total_Y :
    ((Finset.range T).sum fun t => if costed t = true then spentA cY t else 0) = 261932 := by
  have e := totalZ_Y
  have h0 : RC > 0 := by rw [rc_X]; norm_num
  rw [if_pos h0, rc_X] at e
  have e3 : (256 : Int) * ((1023 : Nat) : Int) + 44 = ((261932 : Nat) : Int) := by norm_num
  rw [e3] at e
  exact Int.ofNat.inj e

/-- **The mean's slack is 44968: it does not divide by the 1023 positions: 43 each, and 1 more at
the first 979.** -/
theorem slack_Y : slackA cY = 44968 := by
  rw [slackA_eq cY 261932 total_Y, rc_X]
  rfl

theorem share_Y (i : Nat) : share (slackA cY) RC i = if i < 979 then 44 else 43 := by
  rw [slack_Y, rc_X]
  unfold share
  show 44968 / 1023 + (if i < 44968 % 1023 then 1 else 0) = _
  norm_num
  split <;> rfl

/-- **At position 0 the lifted margins are 2^37, and 2^37 - 71 at the entry that beats the token.**
-/
theorem mar_Y0 {x : Nat} (hx : x < V) : marA cY x 0 = if x = 1 then 2 ^ 37 - 71 else 2 ^ 37 := by
  have h0 : (0 : Nat) < 1023 := by decide
  have hc := costed_X h0
  have h3 := checked_of_costed hc
  have hn : ¬ (checked 0 = true ∧ x < 0) := fun h => Nat.not_lt_zero x h.2
  unfold marA
  rw [if_pos ⟨hx, h3⟩, if_pos ⟨hx, hc⟩, paid_Y h0, over_Y h0, logit_Y (lt_T h0), logit_Y (lt_T h0),
    win_X, if_neg hn]
  unfold BIG
  by_cases h : x = 1 <;> simp [h]

/-- **ITS THREE DIGITS: THE TOP ONE IS NOT 0.** -/
theorem digits_Y0 {x : Nat} (hx : x < V) :
    topA cY x 0 = (if x = 1 then 16382 else 16383) ∧
      midA cY x 0 = (if x = 1 then 65535 else 32768) ∧
      lowA cY x 0 = if x = 1 then 185 else 0 := by
  unfold topA midA lowA topD midD
  rw [mar_Y0 hx]
  show (if _ / (2 : Int) ^ 8 < 2 ^ 16 then (0 : Int) else _ / (2 : Int) ^ 8 / 2 ^ 15 - 1) = _ ∧
    (if _ / (2 : Int) ^ 8 < 2 ^ 16 then _ / (2 : Int) ^ 8 else _ / (2 : Int) ^ 8 % 2 ^ 15 + 2 ^ 15)
      = _ ∧ _ % (2 : Int) ^ 8 = _
  by_cases h : x = 1
  · simp only [h, if_true]
    norm_num
  · simp only [h, if_false]
    norm_num

/-- **BOTH RELATIONS ON CELLS, WHOLE, OF CELLS WITH A POSITION OVER, A TOP DIGIT THAT IS NOT 0 AND A
SLACK THAT DOES NOT DIVIDE: NO PREMISE IS LEFT.** -/
theorem both_Y :
    CellRelN (withAll cY) ∧ CellRel (withAll cY).toCells stepTab ∧ TableOk stepTab ∧
      (dataOf (withAll cY)).Holds ∧ (withAll cY).Wh = wY ∧
      (∀ n t, numZ (withAll cY).toCells n t = (numA cY n t : Int)) ∧ Says (withAll cY).toCells := by
  obtain ⟨a1, a2, a3, a4, a5, _, a7, _⟩ :=
    both_withAll plan_Y request_X token_X fair_Y cellRelN_Y
  exact ⟨a1, a2, a3, a4, a5, a7, says_withAll fair_Y.claim⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtY
