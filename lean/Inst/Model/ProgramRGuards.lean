-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/ProgramRGuards.lean: the relation for a stretch of a reply holds of some requests with
counted positions, and it reads the policy's numbers. Three definitions (`miss`, `xAll`, `xOne`) and
theorems on them. Used by Inst/Model/RequestGuards2.lean (`xOne` and the lemmas on the all-zero
index) and by Cm/RelTrue.lean and Cm/TargetPartBite2.lean.

A theorem about the relation `RinfR` (Inst/Model/ProgramR.lean, which defines the terms) would say
little if the relation held only of requests without a counted position (there it is the relation
"the next token", whatever the policy: `RinfR_next`), or if it did not read the policy. Here, at the
reference sizes, for all valid settings (there is one: Inst/Model/Scales.lean, `lawful_ref`), at the
all-zero index `iZero` (Inst/Model/ScalesSanity.lean):
  1  `runs_iZero`, `lg_zero`, `gap_zero'`, `cost_zero`: the program runs on every prompt; all logits
     are 0; the gap of a token w is 0 if w = 0 and 1 otherwise; so the cost of a position is 2^8 or
     2^8 + 1.
     `zero_true_of`: true instances of `RinfS` (`RinfPP` of Inst/Model/Scales.lean at settings whose
     policy is exact match).
  2  `miss`, `rinfR_zero_iff`: which requests are in the relation at the clip C = 2^8 and the bound
     θ = 2^8 on the mean, whatever the limit cap (`Head3` requires y = 0 of the requests that do not
     cover the last position, so every member has y = 0).
  3  `xAll`, `all_exact`: a request with 1,023 counted positions in the relation at exact match.
  4  `xOne`, `one_cap`, `one_not_exact`: the same request with x_1 = 1: cap is read.
  5  `one_mean`, `slack_one`, `one_mean_not`, `one_clip_not`, `one_clip_sum_not`: the same request
     under four more policies: θ is read; C is read in the count of the positions above the clip and
     in the clipped sum, and a larger clip can refuse what a smaller one admits.
Also, for every P, lg, pol and x, `sweep`: see its statement.
Limits: The index is made up: all its matrices are zero, so no gap above 1 occurs, and nothing is
said of an index that computes anything. The gap 1 comes only from the rule for ties: the token 1
has the same logit as the token 0, so the "member that is not an exact match" checks the loser of a
tie, not a token of smaller logit. The logits are the same at every position and for every prompt,
so these lemmas do not see which position's logits are compared with which token: a relation that
read the logits of another position, or the token x_t in the place of x_(t+1), would pass them all.
Which of the policies used here the implementation accepts: its checks on the three numbers, as this
library renders them (a reading, no theorem), are Inst/Model/ProgTests.lean: `PolTests` (C < 2^32,
θ ≤ C, cap ≤ T); all policies that this file writes out pass them but `one_clip_not`'s
(2^8, 2^8 + 1, 0), whose θ is above C (and `rinfR_zero_iff` holds for every cap, also above T): the
relation `RinfR` is defined there all the same.
Nothing is said of a protocol, a prover or a verifier: these are facts on the relation only.
No settings are written out in this file.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Inst.Model.ProgramR
import Inst.Model.ScalesSanity

set_option autoImplicit false

namespace Inst.Model.ProgramRGuards

open Finset ScalesSanity

/-! ## 1. The all-zero index -/

/-- for all valid settings the program runs on the all-zero index, whatever the prompt -/
theorem runs_iZero {pp : ScalesAndPolicy} (h : Lawful pp) (prompt : Fin ppref.T → Fin ppref.V) :
    RunsK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val prompt :=
  (zero_true h prompt).1

/-- all logits of the all-zero index are 0 -/
theorem lg_zero (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables)
    (prompt : Fin ppref.T → Fin ppref.V) (pos v : ℕ) :
    lgK ppref κ nf tbs iZero.val prompt pos v = 0 := by
  simp [lgK, iZero, iW, dot_zero]

/-- where all logits are 0, the gap of the token w is 0 at w = 0 and 1 at every other token -/
theorem gap_zero' {l : ℕ → ℤ} (hl : ∀ v, l v = 0) {w : ℕ} (hw : w < ppref.V) :
    gapOf ppref.V l w = if w = 0 then 0 else 1 := by
  split
  · rename_i h0
    subst h0
    exact (gapOf_eq_zero_iff ppref.V l hw).2
      ⟨fun v _ => by rw [hl, hl], fun v hv => absurd hv (Nat.not_lt_zero v)⟩
  · rename_i h0
    refine le_antisymm ?_ ?_
    · obtain ⟨j, -, e⟩ := (maxTo_spec (fun v => l v - l w + if v < w then 1 else 0) (ppref.V - 1)).2
      unfold gapOf
      rw [← e]
      show l j - l w + (if j < w then 1 else 0) ≤ 1
      rw [hl, hl]
      split <;> norm_num
    · have := le_gapOf ppref.V l (w := w) (v := 0) (by decide)
      rwa [hl, hl, if_pos (Nat.pos_of_ne_zero h0), sub_zero, zero_add] at this

section Zero
variable (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) (x : Instance ppref)

/-- the cost of a position at the all-zero index: 2^8, and 1 more where the checked token is not
0 -/
theorem cost_zero (t : ℕ) :
    costOf (lgK ppref κ nf tbs iZero.val x.prompt) x t = if x.w t = 0 then 256 else 257 := by
  unfold costOf
  rw [gap_zero' (lg_zero κ nf tbs x.prompt t) (x.w_lt t)]
  split <;> norm_num

end Zero

/-- The relation "every covered token is the least token of largest logit": for all valid settings,
the all-zero index and every well-formed request whose checked tokens at the covered positions are
the token 0 give a true instance. -/
theorem zero_true_of {pp : ScalesAndPolicy} (h : Lawful pp) (x : Instance ppref) (h3 : Head3 x)
    (hx : ∀ t, x.r ≤ t → t < x.e → x.w t = 0) :
    RinfS ppref pp.kap pp.nf (fun _ => tbRef) iZero x :=
  ⟨runs_iZero h x.prompt,
    h3,
    fun t hr he => by rw [gap_zero' (lg_zero _ _ _ _ t) (x.w_lt t), if_pos (hx t hr he)]⟩

/-! ## 2. The relation at the all-zero index, at C = θ = 2^8 -/

/-- the counted positions whose checked token is not the token 0 -/
def miss (x : Instance ppref) : Finset ℕ := x.cnt.filter fun t => x.w t ≠ 0

/-- At valid settings, the all-zero index, the clip 2^8 and the bound 2^8 on the mean, a request is
in the relation if and only if it is well-formed, at most cap counted positions check another token
than 0, and y = 0 if the last position is covered. -/
theorem rinfR_zero_iff {pp : ScalesAndPolicy} (h : Lawful pp) (cap : ℕ) (x : Instance ppref) :
    RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨256, 256, cap⟩ iZero x ↔
    Head3 x ∧ (miss x).card ≤ cap ∧ (x.e = ppref.T → x.y.val = 0) := by
  have hf : (x.cnt.filter fun t =>
        (((⟨256, 256, cap⟩ : AcceptancePolicy).C : ℕ) : ℤ) <
          costOf (lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val x.prompt) x t) = miss x := by
    unfold miss
    refine filter_congr fun t _ => ?_
    rw [cost_zero]
    show ((256 : ℕ) : ℤ) < _ ↔ _
    split
    · rename_i h0
      simp [h0]
    · rename_i h0
      simp [h0]
  have hg : gapOf ppref.V
          (lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val x.prompt (ppref.T - 1)) x.y.val = 0 ↔
      x.y.val = 0 := by
    rw [gap_zero' (lg_zero _ _ _ _ _) x.y.isLt]
    split
    · rename_i h0
      simp [h0]
    · rename_i h0
      simp [h0]
  constructor
  · rintro ⟨-, h2, h3⟩
    exact ⟨h2, hf ▸ h3.b, fun he => hg.1 (h3.c h2.1 he)⟩
  · rintro ⟨h2, hb, hc⟩
    refine ⟨runs_iZero h x.prompt, h2, ⟨?_, by rw [hf]; exact hb, fun _ he => hg.2 (hc he)⟩⟩
    have hm : ∀ t ∈ x.cnt,
        min (costOf (lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val x.prompt) x t)
            (((⟨256, 256, cap⟩ : AcceptancePolicy).C : ℕ) : ℤ) =
          256 := fun t _ => by
      rw [cost_zero]
      show min _ ((256 : ℕ) : ℤ) = 256
      split <;> norm_num
    rw [sum_congr rfl hm, sum_const, x.card_cnt, nsmul_eq_mul]
    show (x.NB : ℤ) * 256 ≤ ((256 : ℕ) : ℤ) * x.NB
    push_cast
    rw [mul_comm]

/-! ## 3. 1,023 counted positions at exact match -/

/-- 1,024 tokens 0; all positions covered; the announced token is 0 -/
def xAll : Instance ppref :=
  ⟨fun _ => ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩, ⟨1024, by decide⟩⟩

theorem nb_all : xAll.NB = 1023 := by decide
theorem head3_all : Head3 xAll := by unfold Head3; decide
theorem w_all (t : ℕ) : xAll.w t = 0 := by unfold Instance.w Instance.tok; split <;> rfl

/-- For all valid settings the relation at exact match holds of a request with 1,023 counted
positions. -/
theorem all_exact {pp : ScalesAndPolicy} (h : Lawful pp) :
    RinfR ppref pp.kap pp.nf (fun _ => tbRef) AcceptancePolicy.exact iZero xAll ∧ xAll.NB = 1023 := by
  refine ⟨(rinfR_zero_iff h 0 xAll).2 ⟨head3_all, ?_, fun _ => rfl⟩, nb_all⟩
  have : miss xAll = ∅ := filter_false_of_mem fun t _ => by rw [w_all]; exact fun h => h rfl
  rw [this]
  exact Nat.le_refl _

/-! ## 4. One position above the clip -/

/-- x_1 = 1, all other tokens are 0: position 0 checks the token 1 -/
def xOne : Instance ppref :=
  ⟨fun t => if t.val = 1 then ⟨1, by decide⟩ else ⟨0, by decide⟩, ⟨0, by decide⟩,
    ⟨0, by decide⟩, ⟨1024, by decide⟩⟩

theorem nb_one : xOne.NB = 1023 := by decide
theorem head3_one : Head3 xOne := by unfold Head3; decide
theorem w_one (t : ℕ) : xOne.w t = if t = 0 then 1 else 0 := by
  unfold Instance.w Instance.tok
  split
  · show ((if t + 1 = 1 then (⟨1, by decide⟩ : Fin ppref.V)
        else ⟨0, by decide⟩) : Fin ppref.V).val = _
    by_cases h0 : t = 0
    · rw [if_pos (by omega), if_pos h0]
    · rw [if_neg (by omega), if_neg h0]
  · rename_i ht
    have : ¬ t + 1 < 1024 := ht
    rw [if_neg (by omega)]
    rfl

theorem miss_one : miss xOne = {0} := by
  ext t
  unfold miss Instance.cnt
  rw [mem_filter, mem_Ico, w_one, mem_singleton]
  show ((0 ≤ t ∧ t < min 1024 (1024 - 1)) ∧ _) ↔ _
  by_cases h0 : t = 0
  · subst h0
    simp
  · simp [h0]

/-- At valid settings, a member of the relation that is not an exact match: one counted position is
above the clip, and the policy allows one. -/
theorem one_cap {pp : ScalesAndPolicy} (h : Lawful pp) :
    RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨256, 256, 1⟩ iZero xOne :=
  (rinfR_zero_iff h 1 xOne).2 ⟨head3_one, by rw [miss_one]; exact Nat.le_refl _, fun _ => rfl⟩

/-- cap is read: at valid settings the same request is not in the relation at exact match -/
theorem one_not_exact {pp : ScalesAndPolicy} (h : Lawful pp) :
    ¬ RinfR ppref pp.kap pp.nf (fun _ => tbRef) AcceptancePolicy.exact iZero xOne := fun hr => by
  have := ((rinfR_zero_iff h 0 xOne).1 hr).2.1
  rw [miss_one] at this
  exact absurd this (by decide)

/-! ## 5. The mean, with an amount left unused -/

/-- the sum of the costs of xOne's counted positions, none of them clipped at 300 -/
theorem sum_one (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) :
    ∑ t ∈ xOne.cnt, min (costOf (lgK ppref κ nf tbs iZero.val xOne.prompt) xOne t) ((300 : ℕ) : ℤ) =
      256 * 1023 + 1 := by
  have hm : ∀ t ∈ xOne.cnt,
      min (costOf (lgK ppref κ nf tbs iZero.val xOne.prompt) xOne t) ((300 : ℕ) : ℤ) =
        256 + if t = 0 then 1 else 0 := fun t _ => by
    rw [cost_zero, w_one]
    by_cases h0 : t = 0
    · simp [h0]
    · simp [h0]
  rw [sum_congr rfl hm, sum_add_distrib, sum_const, xOne.card_cnt, nb_one,
    sum_ite_eq' xOne.cnt 0 fun _ => (1 : ℤ), if_pos (by unfold Instance.cnt; decide)]
  norm_num

theorem none_above (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) :
    (xOne.cnt.filter fun t =>
        ((300 : ℕ) : ℤ) < costOf (lgK ppref κ nf tbs iZero.val xOne.prompt) xOne t) = ∅ :=
  filter_false_of_mem fun t _ => by
    rw [cost_zero]
    split <;> norm_num

/-- At valid settings, a member with an unused amount: clip 300, no position above it allowed, bound
2^8 + 1 on the mean: the costs sum to 261,889, and 262,911 are allowed. -/
theorem one_mean {pp : ScalesAndPolicy} (h : Lawful pp) :
    RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨300, 257, 0⟩ iZero xOne := by
  refine ⟨runs_iZero h _, head3_one, ⟨?_, ?_, fun _ _ => ?_⟩⟩
  · show ∑ t ∈ xOne.cnt, min _ ((300 : ℕ) : ℤ) ≤ ((257 : ℕ) : ℤ) * (xOne.NB : ℤ)
    rw [sum_one, nb_one]
    norm_num
  · show (xOne.cnt.filter fun t => ((300 : ℕ) : ℤ) < _).card ≤ 0
    rw [none_above]
    exact Nat.le_refl _
  · rw [gap_zero' (lg_zero _ _ _ _ _) xOne.y.isLt]
    rfl

/-- the amount left unused at `one_mean`'s policy: θ NB less the sum of the clipped costs -/
theorem slack_one (κ : ℕ → LayerScale) (nf : NormPar) (tbs : ℕ → Tables) :
    ((257 : ℕ) : ℤ) * (xOne.NB : ℤ) -
        ∑ t ∈ xOne.cnt,
          min (costOf (lgK ppref κ nf tbs iZero.val xOne.prompt) xOne t) ((300 : ℕ) : ℤ) =
      1022 := by
  rw [sum_one, nb_one]
  norm_num

/-- θ is read: at the bound 2^8 on the mean the same request is not in the relation -/
theorem one_mean_not {pp : ScalesAndPolicy} :
    ¬ RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨300, 256, 0⟩ iZero xOne := fun hr => by
  have ha : ∑ t ∈ xOne.cnt, min _ ((300 : ℕ) : ℤ) ≤ ((256 : ℕ) : ℤ) * (xOne.NB : ℤ) := hr.2.2.a
  rw [sum_one, nb_one] at ha
  norm_num at ha

/-- C is read in the count: at the clip 2^8, with `one_mean`'s other two numbers, the same request
is not in the relation: position 0 is above the clip -/
theorem one_clip_not {pp : ScalesAndPolicy} :
    ¬ RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨256, 257, 0⟩ iZero xOne := fun hr => by
  have hb : (xOne.cnt.filter fun t =>
        ((256 : ℕ) : ℤ) <
          costOf (lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val xOne.prompt) xOne t).card ≤ 0 :=
    hr.2.2.b
  have hm : 0 ∈
      xOne.cnt.filter fun t =>
        ((256 : ℕ) : ℤ) <
            costOf (lgK ppref pp.kap pp.nf (fun _ => tbRef) iZero.val xOne.prompt) xOne t :=
    mem_filter.2 ⟨by unfold Instance.cnt; decide, by rw [cost_zero, w_one]; norm_num⟩
  exact absurd (card_pos.2 ⟨0, hm⟩) (by omega)

/-- C is read in the sum: at the clip 300, with `one_cap`'s other two numbers, the same request is
not in the relation: the cost 2^8 + 1 is not clipped -/
theorem one_clip_sum_not {pp : ScalesAndPolicy} :
    ¬ RinfR ppref pp.kap pp.nf (fun _ => tbRef) ⟨300, 256, 1⟩ iZero xOne := fun hr => by
  have ha : ∑ t ∈ xOne.cnt, min _ ((300 : ℕ) : ℤ) ≤ ((256 : ℕ) : ℤ) * (xOne.NB : ℤ) := hr.2.2.a
  rw [sum_one, nb_one] at ha
  norm_num at ha

/-! ## What the truth of a request measures, under a policy with slack -/

/-- The bit "is the request true" as a measurement: if t0 is a counted position, all counted
positions but t0 have the lowest cost 2^8 (their tokens are first choices) and 2^8 ≤ C, clause (a)
of the policy says: min(cost of t0, C) ≤ 2^8 + NB (θ − 2^8): a threshold on the clipped cost of the
one token at t0, which whoever chooses the request moves through NB. -/
theorem sweep {P : Params} (lg : ℕ → ℕ → ℤ) (pol : AcceptancePolicy) (x : Instance P) (t0 : ℕ) (h0 : t0 ∈ x.cnt)
    (hC : 2 ^ 8 ≤ pol.C) (h : ∀ t ∈ x.cnt, t ≠ t0 → costOf lg x t = 2 ^ 8) :
    (∑ t ∈ x.cnt, min (costOf lg x t) pol.C ≤ pol.theta * x.NB) ↔
    min (costOf lg x t0) (pol.C : ℤ) ≤ 2 ^ 8 + (x.NB : ℤ) * ((pol.theta : ℤ) - 2 ^ 8) := by
  have hC' : (2 : ℤ) ^ 8 ≤ (pol.C : ℤ) := by exact_mod_cast hC
  have e : ∑ t ∈ x.cnt.erase t0, min (costOf lg x t) (pol.C : ℤ) = ((x.NB : ℤ) - 1) * 2 ^ 8 := by
    rw [Finset.sum_congr rfl (g := fun _ => (2 : ℤ) ^ 8) fun t ht => by
      rw [h t (Finset.mem_of_mem_erase ht) (Finset.ne_of_mem_erase ht), min_eq_left hC']]
    rw [Finset.sum_const, Finset.card_erase_of_mem h0, x.card_cnt, nsmul_eq_mul]
    have hp : 1 ≤ x.NB := by rw [← x.card_cnt]; exact Finset.card_pos.2 ⟨t0, h0⟩
    push_cast [Nat.cast_sub hp]
    ring
  rw [← Finset.add_sum_erase _ _ h0, e]
  constructor <;> intro hh <;> nlinarith [hh]

end Inst.Model.ProgramRGuards
