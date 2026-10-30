-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/PolicyHonest.lean: the honest prover's rule for the head's integers: from the policy
to the six hidden numbers, the digits and the relations.

This is the completeness half, the counterpart of Inst/Model/Head/PolicySound.lean. Both are about
the one statement of the relations, `HRel` (Inst/Model/Head/PolicyDefs.lean).
The file writes out the honest prover's rule at the step table, in steps 1 to 8. Of that rule the
implementation's protocol text (not in this repository) states only the declared cost and the
overflow count (c and b here; steps 2 to 4). The other four
hidden numbers (off the counted positions all six are 0) and the rule for a margin's three digits
are written out in this file. A pair (v, t) is called real if t is covered and v < V. All is at sh =
8, F = 24, BIG = 2^37, the public term Pub = 0.
  `EX_one`, `EX_ge_two`, `EX_step`    rows 1, 2, 3, .. of the step table are 2, 1, 1, .. (row 0 is
                                    2^24: `TablesSanity.tab9`)
  `dK0`, `dK1`, `dK2`, `ix`, `digits`, `dK1_pos`
                                    the rule for the three digits, with the bit in which the two
                                    upper digits overlap; it represents every D in [0, 2^39)
  `step2`                           steps 2, 3: if 2 V ≤ 2^24, the table's values at gap + 2^8 add
                                    up to at most 2^24: so the honest cost is the cost gap + 2^8
                                    (`costOf`, `gapOf`: Inst/Model/ProgramR.lean)
  `hc`, `hb`, `hk`, `slack`, `hu`, `hz`  steps 4 to 7: the clip; k = C − c; the unused amount,
                                    spread from r on with at most 2^40 − 1 at a position; z at r
  `honH`, `honD`                    steps 4 to 8: the six hidden numbers and the digits as functions
                                    of the logits, the policy's numbers and the request
  (`Fit`, in Inst/Model/Head/PolicyDefs.lean)       what is assumed beyond the policy: a bound on
                                    the logits at the T positions and V tokens; C, θ < 2^40; cap <
                                    2^16; 2 V ≤ 2^24
  `honest_exists`                   `PolOK`, `Fit` ⇒ there are h, d with `HRel`, and `Full` at every
                                    position
  `lgK_abs`, `honest_RinfR`         for the integer program at the reference sizes: for every
                                    instance of `RinfR`, whatever the index, the rule's integers
                                    meet the relations and are `Full` at every position, if C, θ <
                                    2^40 and cap < 2^16

Notation:
  `PolOK` (Inst/Model/ProgramR.lean): a `Prop`: the policy's three clauses (a), (b), (c) of the
    comment at the top of that file.
  `AcceptancePolicy` (Inst/Model/ProgramR.lean): the three numbers of the acceptance policy: the clip (C), the
    bound on the mean cost (θ), the limit on the number of positions above the clip (cap).
  covered: r ≤ t < e (`rhoR`, Inst/Model/Head/PolicyDefs.lean); counted: `Instance.cnt`
    (Inst/Model/ProgramR.lean): covered, and below T − 1: their checked token is a token of the
    request; checked token: `Instance.w`.
Limits.
Nothing here is about cells, looked-up values (the keys: `key` of Policy/Rel/LedgerHead.lean), the
field or the protocol: integers only. "The rule's integers meet the relations" is not "the prover's
proof is accepted".
Outside the policy the implementation's prover stops and makes no proof; `honH` and `honD` are total
functions and still give numbers there, which mean nothing: a negative unused amount gives u = 0;
cap < Σ b gives z_r < 0; a wrong y gives a negative margin, a negative middle digit, and row 0 of
the table.
"Whatever the index": an index of this library is well formed, so the head's weights are in [−2^12,
2^12). In the implementation a request's proof takes this bound as a hypothesis; the commitment's
certificate is meant to show it, not the verifier of a request.
The bound on the logits in `Fit`, 68,715,282,431, is the greatest L with (2 L + 1) + 2^23 ≤ 2^37:
the verifier's test BIG ≥ S + 2^(sh+15), in which S = 2 d 2^23 + 1 takes the place of 2 L + 1, a
bound on the difference of two logits plus the tie-break term.
The verifier sees no logit: it tests the width d, and admits d ≤ 8,191, all within this bound; by
`lgK_abs` the widths 8,192 to 8,195 are within it too, which the verifier rejects: the theorems here
are wider than the implementation by that much.
At the reference sizes the logits are at most 5,120 · 2,047 · 2^12 = 42,928,701,440 (`lgK_abs`).
That the request is well-formed (`Head3`) is not asked: of it only e ≤ T is used, which the type of
an instance gives (`Instance.e_le`).
The rule's last step (the prover's choice of y) is not here: y is part of the instance. The
exponential tables are not treated, nor is sh = 7, which the implementation's verifier also admits.
The rule is one solution of the relations; nothing says that it is the only one. θ ≤ C and cap ≤ T,
which the implementation's verifier also tests, are not needed here and are not asked. Only the
condition on cap (cap < 2^16) has a theorem that shows that it is needed (`cap_bites`).
(Words of this library: lean/GLOSSARY.md.)
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.Head.PolicyDefs
import Inst.Model.TablesSanity

set_option autoImplicit false

namespace Inst.Model.Head.Policy.Honest

open Inst.Model Finset

/-! ## The step table -/

theorem exG_ge_two : ∀ u, exG (u + 2) = 1
  | 0 => by norm_num [exG]
  | u + 1 => by
      have h := exG_ge_two u
      show (exG (u + 2) * 484 + (2 ^ 32 - 1)) / 2 ^ 32 = 1
      rw [h]
      norm_num

theorem EX_one : EX 1 = 2 := by norm_num [EX, exG]
theorem EX_ge_two (u : ℕ) : EX (u + 2) = 1 := by unfold EX; rw [exG_ge_two]; norm_num

/-- from row 1 on the table's values are 1 or 2 -/
theorem EX_step {u : ℕ} (hu : 1 ≤ u) : 1 ≤ EX u ∧ EX u ≤ 2 := by
  rcases u with _ | _ | u
  · omega
  · rw [show 0 + 1 = 1 from rfl, EX_one]; norm_num
  · rw [EX_ge_two]; norm_num

/-! ## The three digits of a margin -/

/-- K_2 = D mod 2^sh; m = floor(D / 2^sh); if m < 2^15: K_1 = m, K_0 = 0; else K_1 = 2^15 + (m mod
2^15), K_0 = floor(m / 2^15) − 1 -/
def dK2 (D : ℤ) : ℤ := D % 2 ^ 8
/-- the digit K_1 that the rule at dK2 gives for m = i -/
def ix (i : ℤ) : ℤ := if i < 2 ^ 15 then i else 2 ^ 15 + i % 2 ^ 15
def dK1 (D : ℤ) : ℤ := ix (D / 2 ^ 8)
def dK0 (D : ℤ) : ℤ := if D / 2 ^ 8 < 2 ^ 15 then 0 else D / 2 ^ 8 / 2 ^ 15 - 1

theorem digits {D : ℤ} (h0 : 0 ≤ D) (h1 : D < 2 ^ 39) : D = dK2 D + 2 ^ 8 * dK1 D + 2 ^ 23 * dK0 D ∧
    (0 ≤ dK0 D ∧ dK0 D < 2 ^ 16) ∧ (0 ≤ dK1 D ∧ dK1 D < 2 ^ 16) ∧ (0 ≤ dK2 D ∧ dK2 D < 2 ^ 8) := by
  unfold dK0 dK1 dK2 ix
  split_ifs <;> omega

theorem dK1_pos {D : ℤ} (h : 2 ^ 8 ≤ D) : 1 ≤ dK1 D := by
  unfold dK1 ix
  split_ifs <;> omega

/-! ## The spreading of the unused amount -/

/-- for s ≥ 0: Σ_{i<n} clamp(s − i M, 0, M) = min(s, n M), at M = 2^40 − 1 -/
theorem sum_spread (s : ℤ) (hs : 0 ≤ s) :
    ∀ n : ℕ, ∑ i ∈ range n, max 0 (min (2 ^ 40 - 1) (s - (i : ℤ) * (2 ^ 40 - 1))) =
      min s ((n : ℤ) * (2 ^ 40 - 1))
  | 0 => by simp [hs]
  | n + 1 => by
      rw [sum_range_succ, sum_spread s hs n]
      push_cast
      omega

/-! ## The rule -/

/-- a position's six numbers are not negative and within their bytes -/
def Full (h : Hid) (t : ℕ) : Prop :=
  (0 ≤ h.c t ∧ 0 ≤ h.b t ∧ 0 ≤ h.u t ∧ 0 ≤ h.k t ∧ 0 ≤ h.z t ∧ 0 ≤ h.zs t) ∧ h.Bytes t

/-- step 1: let top_t be the greatest logit, f_t its first index and gap_t = top_t − l_t[w_t] +
[f_t < w_t]: the same number as the gap of the relation (for w < V) -/
theorem gap_step1 (V : ℕ) (l : ℕ → ℤ) {w : ℕ} (hw : w < V) :
    gapOf V l w = l (argTo l (V - 1)) - l w + if argTo l (V - 1) < w then 1 else 0 := by
  obtain ⟨a0, a1, a2⟩ := argTo_spec l (V - 1)
  refine le_antisymm ?_ (le_gapOf V l (w := w) (by omega))
  obtain ⟨j, hj, e⟩ := (maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (V - 1)).2
  unfold gapOf
  rw [← e]
  show l j - l w + (if j < w then 1 else 0) ≤ _
  have h1 := a1 j hj
  by_cases hlt : j < argTo l (V - 1)
  · have := a2 j hlt
    split_ifs <;> omega
  · split_ifs <;> omega

section Rule
variable {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P)

/-- step 4: at a counted position, with the cost n_t (`costOf`): if n_t <= C: c_t = n_t, b_t = 0;
else c_t = 0, b_t = 1 -/
def hc (t : ℕ) : ℤ := if t ∈ x.cnt ∧ costOf lg x t ≤ pol.C then costOf lg x t else 0
def hb (t : ℕ) : ℤ := if t ∈ x.cnt ∧ (pol.C : ℤ) < costOf lg x t then 1 else 0
/-- step 5: k_t = C − c_t at a counted position -/
def hk (t : ℕ) : ℤ := if t ∈ x.cnt then pol.C - hc lg pol x t else 0
/-- step 6: sl = θ NB − Σ (c_t + C b_t) -/
def slack : ℤ := pol.theta * x.NB - ∑ t ∈ x.cnt, (hc lg pol x t + pol.C * hb lg pol x t)
/-- step 6: u_t = clamp(sl − (t − r) (2^40 − 1), 0, 2^40 − 1) at a counted position -/
def hu (t : ℕ) : ℤ :=
  if t ∈ x.cnt then max 0 (min (2 ^ 40 - 1) (slack lg pol x - ((t - x.r : ℕ) : ℤ) * (2 ^ 40 - 1)))
  else 0
/-- step 7: where NB > 0: z_r = cap − sum b_t; z_t = 0 elsewhere -/
def hz (t : ℕ) : ℤ := if t = x.r ∧ 0 < x.NB then pol.cap - ∑ s ∈ x.cnt, hb lg pol x s else 0

/-- the first five numbers; the margin depends on c and b only -/
def pre : Hid := ⟨hc lg pol x, hb lg pol x, hu lg pol x, hk lg pol x, hz lg pol x, fun _ => 0⟩

/-- step 8: the digits and the looked-up value. At a pair (v, t) that is not real: 0, 0, 0 and EX[0]
= 2^24. These are the digits: the value of the array d1 (`pd1`, Inst/Model/Head/PolicyCells.lean) is
K_1 − 32,896 at a real pair and 0 at every other. -/
def honD : Dig where
  K0 := fun v t => if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK0 (marg lg x (pre lg pol x) t v) else 0
  K1 := fun v t => if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK1 (marg lg x (pre lg pol x) t v) else 0
  K2 := fun v t => if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK2 (marg lg x (pre lg pol x) t v) else 0
  ex := fun v t =>
    if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then EX (dK1 (marg lg x (pre lg pol x) t v)).toNat else 2 ^ 24

/-- the six hidden numbers of the honest prover; step 8: zs_t = 2^24 − Σ_{v<V} ex at a counted
position -/
def honH : Hid :=
  { pre lg pol x with
    zs := fun t => if t ∈ x.cnt then 2 ^ 24 - ∑ v ∈ range P.V, (honD lg pol x).ex v t else 0 }

theorem marg_honH (t v : ℕ) : marg lg x (honH lg pol x) t v = marg lg x (pre lg pol x) t v := rfl

variable {lg pol x}

theorem mem_cnt {t : ℕ} : t ∈ x.cnt ↔ x.r ≤ t ∧ t < x.e ∧ t < P.T - 1 := by
  unfold Instance.cnt
  rw [mem_Ico]
  omega

theorem gap_le (hf : Fit P lg pol) {t : ℕ} (ht : t < P.T) :
    gapOf P.V (lg t) (x.w t) ≤ 137430564863 := by
  obtain ⟨j, hj, e⟩ :=
    (maxTo_spec (fun v => lg t v - lg t (x.w t) + if v < x.w t then 1 else 0) (P.V - 1)).2
  have hV := x.w_lt t
  have a := abs_le.1 (hf.lg t ht j (by omega))
  have b := abs_le.1 (hf.lg t ht (x.w t) hV)
  unfold gapOf
  rw [← e]
  show lg t j - lg t (x.w t) + (if j < x.w t then 1 else 0) ≤ 137430564863
  split_ifs <;> omega

theorem cost_ge (t : ℕ) : 2 ^ 8 ≤ costOf lg x t := by
  have := gapOf_nonneg P.V (lg t) (x.w_lt t)
  unfold costOf
  omega

/-- steps 2, 3: with i_v = floor((l_t[w_t] + gap_t + 2^sh − l_t[v] − [v < w_t]) / 2^sh), if 2 V ≤
2^24, the values EX[ix(i_v)] add up over v < V to at most 2^F: so the honest cost is gap_t + 2^sh -/
theorem step2 (hV : 2 * P.V ≤ 2 ^ 24) (t : ℕ) :
    ∑ v ∈ range P.V, EX
        (ix ((lg t (x.w t) + costOf lg x t - lg t v - if v < x.w t then 1 else 0) / 2 ^ 8)).toNat ≤
      2 ^ 24 := by
  have u : ∑ v ∈ range P.V,
        EX (ix
            ((lg t (x.w t) + costOf lg x t - lg t v - if v < x.w t then 1 else 0) / 2 ^ 8)).toNat ≤
      ∑ _v ∈ range P.V, (2 : ℤ) :=
    sum_le_sum fun v hv => by
      have g := le_gapOf P.V (lg t) (w := x.w t) (mem_range.1 hv)
      have h1 := dK1_pos (D := lg t (x.w t) + costOf lg x t - lg t v - if v < x.w t then 1 else 0)
        (by unfold costOf; split_ifs at g ⊢ <;> omega)
      exact (EX_step (by unfold dK1 at h1; omega)).2
  rw [sum_const, card_range, nsmul_eq_mul] at u
  have hV2 : (2 : ℤ) * P.V ≤ 2 ^ 24 := by exact_mod_cast hV
  linarith

/-- c + C b = min(cost, C) at a counted position -/
theorem hc_add {t : ℕ} (ht : t ∈ x.cnt) :
    hc lg pol x t + pol.C * hb lg pol x t = min (costOf lg x t) pol.C := by
  unfold hc hb
  by_cases h : costOf lg x t ≤ pol.C
  · rw [if_pos ⟨ht, h⟩, if_neg (fun h' => absurd h'.2 (not_lt.2 h)), min_eq_left h]; ring
  · rw [if_neg (fun h' => h h'.2), if_pos ⟨ht, not_le.1 h⟩, min_eq_right (le_of_lt (not_le.1 h))]; ring

theorem hc_range (t : ℕ) : 0 ≤ hc lg pol x t ∧ hc lg pol x t ≤ pol.C := by
  have := cost_ge (lg := lg) (x := x) t
  have hC : (0 : ℤ) ≤ pol.C := Int.natCast_nonneg _
  unfold hc
  split_ifs with h
  · exact ⟨by omega, h.2⟩
  · exact ⟨le_refl 0, hC⟩

theorem hb_range (t : ℕ) : 0 ≤ hb lg pol x t ∧ hb lg pol x t ≤ 1 := by
  unfold hb
  split_ifs <;> norm_num

theorem sum_hb :
    ∑ t ∈ x.cnt, hb lg pol x t =
      ((x.cnt.filter fun t => (pol.C : ℤ) < costOf lg x t).card : ℤ) := by
  rw [card_filter]
  push_cast
  refine sum_congr rfl fun t ht => ?_
  unfold hb
  by_cases h : (pol.C : ℤ) < costOf lg x t
  · rw [if_pos ⟨ht, h⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.2), if_neg h]

theorem slack_range (hp : PolOK lg pol x) (hf : Fit P lg pol) :
    0 ≤ slack lg pol x ∧ slack lg pol x ≤ (x.NB : ℤ) * (2 ^ 40 - 1) := by
  have e : ∑ t ∈ x.cnt, (hc lg pol x t + pol.C * hb lg pol x t) =
      ∑ t ∈ x.cnt, min (costOf lg x t) pol.C :=
    sum_congr rfl fun t ht => hc_add ht
  have h0 : 0 ≤ ∑ t ∈ x.cnt, (hc lg pol x t + pol.C * hb lg pol x t) :=
    sum_nonneg fun t _ =>
      add_nonneg (hc_range t).1 (mul_nonneg (Int.natCast_nonneg _) (hb_range t).1)
  have h1 : (pol.theta : ℤ) * x.NB ≤ (2 ^ 40 - 1) * x.NB :=
    mul_le_mul_of_nonneg_right (by have : (pol.theta : ℤ) < 2 ^ 40 := by exact_mod_cast hf.theta
                                   omega) (Int.natCast_nonneg _)
  unfold slack
  constructor
  · rw [e]; have := hp.a; omega
  · linarith

theorem sum_hu (hp : PolOK lg pol x) (hf : Fit P lg pol) :
    ∑ t ∈ x.cnt, hu lg pol x t = slack lg pol x := by
  obtain ⟨s0, s1⟩ := slack_range hp hf
  have e : ∑ t ∈ x.cnt, hu lg pol x t =
      ∑ t ∈ x.cnt, max 0 (min (2 ^ 40 - 1) (slack lg pol x - ((t - x.r : ℕ) : ℤ) * (2 ^ 40 - 1))) :=
    sum_congr rfl fun t ht => by unfold hu; rw [if_pos ht]
  rw [e]
  unfold Instance.cnt
  rw [sum_Ico_eq_sum_range]
  have e2 : ∑ i ∈ range (min x.e (P.T - 1) - x.r),
        max 0 (min (2 ^ 40 - 1) (slack lg pol x - ((x.r + i - x.r : ℕ) : ℤ) * (2 ^ 40 - 1))) =
      ∑ i ∈ range x.NB, max 0 (min (2 ^ 40 - 1) (slack lg pol x - (i : ℤ) * (2 ^ 40 - 1))) :=
    sum_congr rfl fun i _ => by rw [Nat.add_sub_cancel_left]
  rw [e2, sum_spread _ s0, min_eq_left s1]

theorem sum_hz :
    ∑ t ∈ x.cnt, hz lg pol x t =
      if 0 < x.NB then (pol.cap : ℤ) - ∑ s ∈ x.cnt, hb lg pol x s else 0 := by
  split_ifs with h
  · have hr : x.r ∈ x.cnt := by
      unfold Instance.cnt
      unfold Instance.NB at h
      rw [mem_Ico]; omega
    rw [sum_eq_single x.r (fun t _ hne => by unfold hz; rw [if_neg fun h' => hne h'.1])
        (fun h' => absurd hr h')]
    unfold hz
    rw [if_pos ⟨rfl, h⟩]
  · exact sum_eq_zero fun t _ => by unfold hz; rw [if_neg fun h' => h h'.2]

/-- under `Fit`: the margin at a counted position, v < V, is in [2^8, 2^39) -/
theorem marg_cnt (hf : Fit P lg pol) {t v : ℕ} (ht : t ∈ x.cnt) (hv : v < P.V) :
    2 ^ 8 ≤ marg lg x (pre lg pol x) t v ∧ marg lg x (pre lg pol x) t v < 2 ^ 39 := by
  have htT : t < P.T := by have := mem_cnt.1 ht; omega
  have a := abs_le.1 (hf.lg t htT v hv)
  have b := abs_le.1 (hf.lg t htT (x.w t) (x.w_lt t))
  have g := le_gapOf P.V (lg t) (w := x.w t) hv
  have g1 := gap_le (x := x) hf htT
  have e : marg lg x (pre lg pol x) t v =
      lg t (x.w t) + (hc lg pol x t + 2 ^ 37 * hb lg pol x t) -
        lg t v - if v < x.w t then 1 else 0 := by
    unfold marg rhoC
    rw [if_pos ht, one_mul]
    rfl
  rw [e]
  unfold hc hb
  by_cases h : costOf lg x t ≤ pol.C
  · rw [if_pos ⟨ht, h⟩, if_neg (fun h' => absurd h'.2 (not_lt.2 h))]
    unfold costOf
    split_ifs at g ⊢ <;> omega
  · rw [if_neg (fun h' => h h'.2), if_pos ⟨ht, not_le.1 h⟩]
    split_ifs <;> omega

/-- a covered position that is not counted is the last one, and its checked token is y -/
theorem last_of {t : ℕ} (h1 : x.r ≤ t) (h2 : t < x.e) (ht : t ∉ x.cnt) :
    t = P.T - 1 ∧ x.e = P.T ∧ x.w t = x.y.val := by
  have h := x.e_le
  have h4 : ¬ (x.r ≤ t ∧ t < x.e ∧ t < P.T - 1) := fun h' => ht (mem_cnt.2 h')
  have e1 : t = P.T - 1 := by omega
  refine ⟨e1, by omega, ?_⟩
  unfold Instance.w Instance.tok
  rw [dif_neg (by omega)]

/-- under `PolOK`, `Fit`: the margin at the last position (covered, not counted), v < V, is in
[0, 2^39) -/
theorem marg_last (hp : PolOK lg pol x) (hf : Fit P lg pol) {t v : ℕ} (h1 : x.r ≤ t) (h2 : t < x.e)
    (ht : t ∉ x.cnt) (hv : v < P.V) :
    0 ≤ marg lg x (pre lg pol x) t v ∧ marg lg x (pre lg pol x) t v < 2 ^ 39 := by
  obtain ⟨e1, e2, e3⟩ := last_of h1 h2 ht
  have htT : t < P.T := lt_of_lt_of_le h2 x.e_le
  have a := abs_le.1 (hf.lg t htT v hv)
  have b := abs_le.1 (hf.lg t htT (x.w t) (x.w_lt t))
  have g := le_gapOf P.V (lg t) (w := x.w t) hv
  have g0 : gapOf P.V (lg t) (x.w t) = 0 := by rw [e3, e1]; exact hp.c (lt_of_le_of_lt h1 h2) e2
  have e : marg lg x (pre lg pol x) t v = lg t (x.w t) - lg t v - if v < x.w t then 1 else 0 := by
    unfold marg rhoC
    rw [if_neg ht, zero_mul, add_zero]
  rw [e]
  rw [g0] at g
  split_ifs at g ⊢ <;> omega

theorem marg_cov (hp : PolOK lg pol x) (hf : Fit P lg pol) {t v : ℕ} (h1 : x.r ≤ t)
    (h2 : t < x.e) (hv : v < P.V) :
    0 ≤ marg lg x (pre lg pol x) t v ∧ marg lg x (pre lg pol x) t v < 2 ^ 39 := by
  by_cases ht : t ∈ x.cnt
  · have := marg_cnt hf ht hv
    exact ⟨by omega, this.2⟩
  · exact marg_last hp hf h1 h2 ht hv

/-- under `Fit`, at a counted position every looked-up value at v < V is 1 or 2 -/
theorem ex_cnt (hf : Fit P lg pol) {t v : ℕ} (ht : t ∈ x.cnt) (hv : v < P.V) :
    1 ≤ (honD lg pol x).ex v t ∧ (honD lg pol x).ex v t ≤ 2 := by
  have hm := mem_cnt.1 ht
  have h1 := dK1_pos (marg_cnt hf ht hv).1
  show 1 ≤ (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then EX (dK1 (marg lg x (pre lg pol x) t v)).toNat
        else 2 ^ 24) ∧
    (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then EX (dK1 (marg lg x (pre lg pol x) t v)).toNat
        else 2 ^ 24) ≤ 2
  rw [if_pos ⟨⟨hm.1, hm.2.1⟩, hv⟩]
  exact EX_step (by omega)

theorem sum_ex (hf : Fit P lg pol) {t : ℕ} (ht : t ∈ x.cnt) :
    1 ≤ ∑ v ∈ range P.V, (honD lg pol x).ex v t ∧
    ∑ v ∈ range P.V, (honD lg pol x).ex v t ≤ 2 ^ 24 := by
  have hV : 0 < P.V := lt_of_le_of_lt (Nat.zero_le _) x.y.isLt
  have l : ∑ _v ∈ range P.V, (1 : ℤ) ≤ ∑ v ∈ range P.V, (honD lg pol x).ex v t :=
    sum_le_sum fun v hv => (ex_cnt hf ht (mem_range.1 hv)).1
  have u : ∑ v ∈ range P.V, (honD lg pol x).ex v t ≤ ∑ _v ∈ range P.V, (2 : ℤ) :=
    sum_le_sum fun v hv => (ex_cnt hf ht (mem_range.1 hv)).2
  rw [sum_const, card_range, nsmul_eq_mul] at l u
  have hV2 : (2 : ℤ) * P.V ≤ 2 ^ 24 := by exact_mod_cast hf.V
  have hV1 : (1 : ℤ) ≤ P.V := by exact_mod_cast hV
  constructor <;> linarith

/-! ## The theorems -/

/-- Under `PolOK` and `Fit`: at every position each of the six numbers is not negative and within
its bytes. -/
theorem honest_bytes (hp : PolOK lg pol x) (hf : Fit P lg pol) (t : ℕ) :
    Full (honH lg pol x) t := by
  have hC : (pol.C : ℤ) < 2 ^ 40 := by exact_mod_cast hf.C
  have hcap : (pol.cap : ℤ) < 2 ^ 16 := by exact_mod_cast hf.cap
  have c := hc_range (lg := lg) (pol := pol) (x := x) t
  have b := hb_range (lg := lg) (pol := pol) (x := x) t
  have u : 0 ≤ hu lg pol x t ∧ hu lg pol x t < 2 ^ 40 := by
    unfold hu
    split_ifs <;> omega
  have k : 0 ≤ hk lg pol x t ∧ hk lg pol x t < 2 ^ 40 := by
    unfold hk
    split_ifs <;> omega
  have z : 0 ≤ hz lg pol x t ∧ hz lg pol x t < 2 ^ 16 := by
    have s0 : 0 ≤ ∑ s ∈ x.cnt, hb lg pol x s := sum_nonneg fun s _ => (hb_range s).1
    have s1 : ∑ s ∈ x.cnt, hb lg pol x s ≤ pol.cap := by rw [sum_hb]; exact_mod_cast hp.b
    unfold hz
    split_ifs <;> omega
  have zs : 0 ≤ (honH lg pol x).zs t ∧ (honH lg pol x).zs t < 2 ^ 24 := by
    show 0 ≤ (if t ∈ x.cnt then 2 ^ 24 - ∑ v ∈ range P.V, (honD lg pol x).ex v t else 0) ∧
      (if t ∈ x.cnt then 2 ^ 24 - ∑ v ∈ range P.V, (honD lg pol x).ex v t else 0) < 2 ^ 24
    split_ifs with ht
    · have := sum_ex hf ht
      omega
    · norm_num
  exact ⟨⟨c.1, b.1, u.1, k.1, z.1, zs.1⟩, lt_of_le_of_lt c.2 hC,
    lt_of_le_of_lt b.2 (by norm_num), u.2, k.2, z.2, zs.2⟩

/-- Under `PolOK` and `Fit`: the honest numbers meet the relations. -/
theorem honest_rel (hp : PolOK lg pol x) (hf : Fit P lg pol) :
    HRel lg pol x (honH lg pol x) (honD lg pol x) where
  nonneg := fun t _ => (honest_bytes hp hf t).1
  B1 := fun t h1 h2 v hv => by
    have hm := marg_cov hp hf h1 h2 hv
    have hd := digits hm.1 hm.2
    rw [marg_honH]
    show marg lg x (pre lg pol x) t v =
        (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK2 (marg lg x (pre lg pol x) t v) else 0) +
          2 ^ 8 *
            (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK1 (marg lg x (pre lg pol x) t v) else 0) +
          2 ^ 23 *
            (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK0 (marg lg x (pre lg pol x) t v) else 0) ∧
      (0 ≤ (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK0 (marg lg x (pre lg pol x) t v) else 0) ∧
        (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK0 (marg lg x (pre lg pol x) t v) else 0) <
          2 ^ 16) ∧
      (0 ≤ (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK1 (marg lg x (pre lg pol x) t v) else 0) ∧
        (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK1 (marg lg x (pre lg pol x) t v) else 0) <
          2 ^ 16) ∧
      (0 ≤ (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK2 (marg lg x (pre lg pol x) t v) else 0) ∧
        (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK2 (marg lg x (pre lg pol x) t v) else 0) < 2 ^ 8)
    simp only [if_pos (show (x.r ≤ t ∧ t < x.e) ∧ v < P.V from ⟨⟨h1, h2⟩, hv⟩)]
    exact hd
  HE := fun t h1 h2 v hv => by
    show (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then EX (dK1 (marg lg x (pre lg pol x) t v)).toNat
        else 2 ^ 24) =
      EX (if (x.r ≤ t ∧ t < x.e) ∧ v < P.V then dK1 (marg lg x (pre lg pol x) t v) else 0).toNat
    simp only [if_pos (show (x.r ≤ t ∧ t < x.e) ∧ v < P.V from ⟨⟨h1, h2⟩, hv⟩)]
  Z := fun t ht => by
    show (if t ∈ x.cnt then 2 ^ 24 - ∑ v ∈ range P.V, (honD lg pol x).ex v t else 0) +
        ∑ v ∈ range P.V, (honD lg pol x).ex v t = 2 ^ 24
    rw [if_pos ht]; ring
  B2 := by
    show ∑ t ∈ x.cnt, (hc lg pol x t + pol.C * hb lg pol x t + hu lg pol x t) = pol.theta * x.NB
    rw [sum_add_distrib, sum_hu hp hf]
    unfold slack
    ring
  B3 := by
    show ∑ t ∈ x.cnt, (hb lg pol x t + hz lg pol x t) = if 0 < x.NB then (pol.cap : ℤ) else 0
    rw [sum_add_distrib, sum_hz]
    split_ifs with h
    · ring
    · have hc0 : x.cnt = ∅ := card_eq_zero.1 (by rw [x.card_cnt]; omega)
      rw [hc0]; simp
  B4 := fun t ht => by
    show hc lg pol x t + hk lg pol x t = pol.C
    unfold hk
    rw [if_pos ht]; ring

/-- At rhoC_t = 0 all six are 0 -/
theorem honest_off {t : ℕ} (ht : t ∉ x.cnt) :
    (honH lg pol x).c t = 0 ∧ (honH lg pol x).b t = 0 ∧ (honH lg pol x).u t = 0 ∧
    (honH lg pol x).k t = 0 ∧ (honH lg pol x).z t = 0 ∧ (honH lg pol x).zs t = 0 := by
  refine ⟨if_neg fun h => ht h.1, if_neg fun h => ht h.1, if_neg ht, if_neg ht,
    if_neg fun h => ht ?_, if_neg ht⟩
  have h2 := h.2
  unfold Instance.NB at h2
  unfold Instance.cnt
  rw [mem_Ico, h.1]; omega

/-- at a pair that is not real: the digits are 0 and ex = 2^24 = EX[0] -/
theorem honest_offD {t v : ℕ} (h : ¬ ((x.r ≤ t ∧ t < x.e) ∧ v < P.V)) :
    (honD lg pol x).K0 v t = 0 ∧
    (honD lg pol x).K1 v t = 0 ∧
    (honD lg pol x).K2 v t = 0 ∧
    (honD lg pol x).ex v t = 2 ^ 24 :=
  ⟨if_neg h, if_neg h, if_neg h, if_neg h⟩

theorem honest_exists (hp : PolOK lg pol x) (hf : Fit P lg pol) :
    ∃ h d, HRel lg pol x h d ∧ ∀ t, Full h t :=
  ⟨honH lg pol x, honD lg pol x, honest_rel hp hf, honest_bytes hp hf⟩

/-! ## Sanity lemmas -/

/-- Sanity lemma: the condition on cap is not idle. With one counted position and θ < C, numbers
within their bytes that meet the relations force cap < 2^16. -/
theorem cap_bites {h : Hid} {d : Dig} (hr : HRel lg pol x h d) (hb : ∀ t, h.Bytes t)
    (h1 : x.NB = 1) (hθ : pol.theta < pol.C) : pol.cap < 2 ^ 16 := by
  have hc : x.cnt = {x.r} := by
    unfold Instance.NB at h1
    unfold Instance.cnt
    rw [show min x.e (P.T - 1) = x.r + 1 by omega]
    exact Nat.Ico_succ_singleton x.r
  have hm : x.r ∈ x.cnt := by rw [hc]; exact mem_singleton_self _
  obtain ⟨c0, b0, u0, -, -, -⟩ := hr.nonneg x.r hm
  have B2 := hr.B2
  have B3 := hr.B3
  rw [hc, sum_singleton, h1] at B2
  rw [hc, sum_singleton, h1, if_pos Nat.one_pos] at B3
  have hz := (hb x.r).2.2.2.2.1
  have hθ' : (pol.theta : ℤ) < pol.C := by exact_mod_cast hθ
  have hb0 : h.b x.r = 0 := by
    by_contra hne
    have : 1 ≤ h.b x.r := by omega
    have : (pol.C : ℤ) * 1 ≤ pol.C * h.b x.r :=
      mul_le_mul_of_nonneg_left this (Int.natCast_nonneg _)
    push_cast at B2
    omega
  have : (pol.cap : ℤ) < 2 ^ 16 := by omega
  exact_mod_cast this

/-- Sanity lemma: at a counted position whose checked token is the least token of largest logit,
with 2^8 ≤ C: c = 2^8, b = 0, k = C − 2^8. -/
theorem exact_values {t : ℕ} (ht : t ∈ x.cnt)
    (hg : gapOf P.V (lg t) (x.w t) = 0) (hC : 2 ^ 8 ≤ pol.C) :
    (honH lg pol x).c t = 2 ^ 8 ∧
    (honH lg pol x).b t = 0 ∧
    (honH lg pol x).k t = pol.C - 2 ^ 8 := by
  have e : costOf lg x t = 2 ^ 8 := by unfold costOf; rw [hg]; norm_num
  have hC' : (2 : ℤ) ^ 8 ≤ pol.C := by exact_mod_cast hC
  have c : hc lg pol x t = 2 ^ 8 := by unfold hc; rw [if_pos ⟨ht, by rw [e]; exact hC'⟩, e]
  refine ⟨c, if_neg fun h => ?_, ?_⟩
  · have := h.2
    rw [e] at this
    omega
  · show hk lg pol x t = _
    unfold hk
    rw [if_pos ht, c]

end Rule

/-! ## For the integer program -/

/-- |lg| ≤ d · 2,047 · 2^12 at every position and token, for every index: the normalisation's output
is clamped at 2,047, and the head's weights of a well-formed index are in [−2^12, 2^12) -/
theorem lgK_abs (P : Params) (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (i : Index P)
    (prompt : Fin P.T → Fin P.V) (pos v : ℕ) :
    |lgK P κ nf tbs i.val prompt pos v| ≤ P.d * (2047 * 2 ^ 12) := by
  unfold lgK dot
  calc
    |∑ j ∈ range P.d,
      nrmK P κ nf tbs i.val prompt pos j * i.val.H j v| ≤
          ∑ j ∈ range P.d, |nrmK P κ nf tbs i.val prompt pos j * i.val.H j v| := abs_sum_le_sum_abs
            _ _
    _ ≤ ∑ _j ∈ range P.d, (2047 * 2 ^ 12 : ℤ) := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (by norm_num)
        · rw [abs_le]
          unfold nrmK NORM.out clamp
          omega
        · have h := i.property.2.2 j v
          rw [abs_le]
          split_ifs at h <;> omega
    _ = P.d * (2047 * 2 ^ 12) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- For every instance of the relation at the reference sizes the rule's integers meet the relations
and are within their bytes, whatever the index, the scales of the layers, the final normalisation
and the tables, if C, θ < 2^40 and cap < 2^16. -/
theorem honest_RinfR (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (pol : AcceptancePolicy)
    (hC : pol.C < 2 ^ 40) (hθ : pol.theta < 2 ^ 40) (hcap : pol.cap < 2 ^ 16) (i : Index ppref)
    (x : Instance ppref) (h : RinfR ppref κ nf tbs pol i x) :
    HRel (lgK ppref κ nf tbs i.val x.prompt) pol x (honH (lgK ppref κ nf tbs i.val x.prompt) pol x)
      (honD (lgK ppref κ nf tbs i.val x.prompt) pol x) ∧
    ∀ t, Full (honH (lgK ppref κ nf tbs i.val x.prompt) pol x) t := by
  have hf : Fit ppref (lgK ppref κ nf tbs i.val x.prompt) pol :=
    ⟨fun t _ v _ => le_trans (lgK_abs ppref κ nf tbs i x.prompt t v) (by norm_num [ppref]),
      hC, hθ, hcap, by norm_num [ppref]⟩
  exact ⟨honest_rel h.2.2 hf, honest_bytes h.2.2 hf⟩

end Inst.Model.Head.Policy.Honest
