-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/MeetsPolicyBounds.lean

What the claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean) gives a user, in logit gaps, and at
which policies it gives nothing. Theorems on that definition alone, for all settings, weights,
prompts and outputs. They add to Policy/Front/MeetsPolicyGuards.lean, which has exact match
(`meetsPolicy_exact_iff`), a count of costly tokens (`few_costly_of_meetsPolicy`) and monotonicity
in theta and cap (`MeetsPolicy.mono`). No goal of the library is stated here.

A policy is three natural numbers: the clip C, the bound theta, the limit cap. A token's cost is its
logit gap plus 2^8. A token's gap (`outputGap`) is how far its logit lies below the first choice's,
and 1 more where the first choice is the smaller token. Below, n is the number of counted tokens
(`countedTokens`) of the one output in question, and "every output" is short for: every output that
has scores (`HasScores`) and meets clause (c).

Main names.
* `MeetsPolicy.sum_clippedGap_le`: if the output meets the policy, the gaps of its counted tokens,
  each clipped at C - 2^8, sum to at most n (theta - 2^8). For n > 0: the mean clipped gap is at
  most theta - 2^8. It is clause (a) of the definition, read in gaps, and no new guarantee.
* `meetsPolicy_iff_budget`: the claim as a budget, with nothing lost. Besides scores and clause (c):
  one can set aside at most cap counted tokens, of whose gaps nothing is asked; each is charged
  C - 2^8; every other counted token has a gap of at most C - 2^8; and these gaps, unclipped, with
  the charges sum to at most n (theta - 2^8).
* `MeetsPolicy.sum_gap_le_of_short`, `MeetsPolicy.sum_gap_le_of_cap_zero`: two conditions under
  which the unclipped gaps of an output that meets the policy sum to at most n (theta - 2^8):
  2^8 ≤ C and n (theta - 2^8) < C - 2^8; or cap = 0. `MeetsPolicy.sum_gap_le_of_window`: the same
  bound for outputs of every length, under a condition on the policy's numbers and the window alone:
  2^8 ≤ theta and (positions - 1) (theta - 2^8) < C - 2^8.
* `MeetsPolicy.card_gap_ge_mul_le`: of n counted tokens at most n (theta - 2^8) / g have a gap of g
  or more, for 0 < g ≤ C - 2^8.
* `MeetsPolicy.clippedGap_le`: for 2^8 ≤ C no counted token's clipped gap is above the whole budget
  n (theta - 2^8). `meetsPolicy_of_one_departure`: in an output with scores and clause (c), one
  counted token whose gap is at most C - 2^8 may use up that budget, if all the other counted tokens
  are the model's next tokens.
* Policies that say little: `meetsPolicy_iff_of_clip_le_mean_anyCap` (C ≤ theta: the mean says
  nothing), `meetsPolicy_iff_of_counted_le_cap` (n ≤ cap: the count says nothing),
  `meetsPolicy_iff_of_idle` (C ≤ theta and cap at least the window less 1: every output with scores
  and clause (c) meets the policy), `meetsPolicy_iff_of_clip_lt` (C < 2^8: clauses (a) and (b) read
  no score), `meetsPolicy_iff_of_clip_eq` (C = 2^8 ≤ theta: a count of the tokens that are not the
  model's next token), `clauses_forall_iff` (for costs that may be any numbers from 2^8 on: the two
  clauses hold of every list of n costs exactly if n = 0, or C ≤ theta and n ≤ cap).
* Policies that no output with a counted token meets: `not_meetsPolicy_of_numbers`
  (theta < min(2^8, C), or C < 2^8 and cap = 0); with the number of counted tokens:
  `not_meetsPolicy_of_refuses_least`, `meetsPolicy_isModelOutput_iff`.
* A caution on the weights: `meetsPolicy_of_close_logits`. An output with scores and clause (c),
  after each of whose counted contexts no token's logit lies more than `spread` above the output
  token's, meets every policy with 2^8 + spread + 1 ≤ C, theta.
* The clip: `MeetsPolicy.raise_clip`, `MeetsPolicy.mono_clip_of_cap_zero`.

Limits.
* The claim does not bound how many counted tokens differ from the model's choice. All of them may,
  if their gaps are small enough in sum. cap limits only the tokens whose gap is above C - 2^8.
* The unit of a gap is the unit of the integer model's logits under the given weights. No definition
  here reads a scale for it: the parameter file's line s, by which a provider says how many integer
  steps make one unit of a real-valued logit, enters nowhere. 2^8 is an offset in the same unit.
* Every bound is on one output, which in a soundness statement the prover picks and may cut as it
  likes. The budget grows with n: a long output can hold one large departure, or many small ones.
  The prompt is not scored.
* Each token is scored after the output's own earlier tokens, not after the tokens that the model
  would have chosen. So a bound on gaps is no bound on the distance to the model's own output.
* A bound on gaps says something only for weights whose logits are known to be spread out
  (`meetsPolicy_of_close_logits`). Nothing here says that given weights are a sensible model.
* The theorems hold for any three natural numbers. The goals of Ladder.lean speak of public files
  with 2^8 ≤ theta ≤ C (`InScope` there, and the reader's tests): there C < 2^8, theta < 2^8 and
  C < theta do not arise, and theta = C with n ≤ cap does.
* `clauses_forall_iff` ranges over all lists of costs, not over the costs that some weights reach.
  For rejections at weights see Policy/Front/Teeth.lean and Policy/Front/TeethAllChannels.lean; for
  policies that are idle because the model's gaps are bounded,
  Policy/Front/MeetsPolicyIdleAtScales.lean.
* Clause (a) has the form of the clipped margin of Token-DiFR at temperature 0 (A. Karvonen, D.
  Reuter, R. Rinberg, L. Marks, A. Garriga-Alonso, K. Warr, "DiFR: Inference Verification Despite
  Nondeterminism", arXiv 2511.20621). To meet the policy is not to pass that paper's test: see the
  docstring of `MeetsPolicy`.
* Nothing here speaks of a protocol, a commitment, a prover or a verifier.

-/
import Policy.Front.MeetsPolicyGuards

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference

/-! ## 1. The gap of an output token -/

/-- The logit gap of the output token at `position` (counted from 0), after the prompt and the
output tokens before it. A shorthand for this file's statements: it is `outputCost` without the
offset 2^8 (`outputCost_eq_outputGap_add`). It states no goal. Its unit is that of the model's
integer logits. Beyond the output's end it reads token 0, as `outputCost` does; the theorems read it
at counted positions alone. -/
abbrev outputGap (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Token) (position : Nat) : Int :=
  logitGap settings.vocabulary (modelLogits settings weights (prompt ++ output.take position))
    (output.getD position 0)

/-- A token's cost is its gap plus 2^8. By unfolding. -/
theorem outputCost_eq_outputGap_add (settings : IntegerTransformer.Settings)
    (weights : ModelWeights settings) (prompt output : List Token) (position : Nat) :
    outputCost settings weights prompt output position =
      outputGap settings weights prompt output position + 2 ^ 8 :=
  rfl

/-- A token's cost less 2^8 is its gap. -/
theorem outputCost_sub (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Token) (position : Nat) :
    outputCost settings weights prompt output position - 2 ^ 8 =
      outputGap settings weights prompt output position := by
  rw [outputCost_eq_outputGap_add, add_sub_cancel_right]

/-- A token costs at most c exactly if its gap is at most c - 2^8. -/
theorem outputCost_le_iff (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Token) (position : Nat) (c : ℤ) :
    outputCost settings weights prompt output position ≤ c ↔
      outputGap settings weights prompt output position ≤ c - 2 ^ 8 := by
  rw [outputCost_eq_outputGap_add]
  constructor <;> intro h <;> linarith

/-- The gap of an output token of the vocabulary is at least 0. -/
theorem outputGap_nonneg {settings : IntegerTransformer.Settings} (weights : ModelWeights settings)
    (prompt : List Token) {output : List Token}
    (small : ∀ token ∈ output, token < settings.vocabulary) {position : Nat}
    (h : position < output.length) : 0 ≤ outputGap settings weights prompt output position := by
  have low := outputCost_ge weights prompt small h
  rw [outputCost_eq_outputGap_add] at low
  linarith

/-- Where the model has a value on its context, the gap of an output token of the vocabulary is 0
exactly if it is the model's next token. -/
theorem outputGap_eq_zero_iff {settings : IntegerTransformer.Settings}
    (weights : ModelWeights settings) (prompt : List Token) {output : List Token}
    (small : ∀ token ∈ output, token < settings.vocabulary) {position : Nat}
    (h : position < output.length)
    (defined : (modelNextToken settings weights (prompt ++ output.take position)).isSome = true) :
    outputGap settings weights prompt output position = 0 ↔
      modelNextToken settings weights (prompt ++ output.take position) = some output[position] := by
  rw [← outputCost_eq_iff weights prompt small h defined, outputCost_eq_outputGap_add]
  constructor
  · intro e
    rw [e, zero_add]
  · intro e
    linarith

/-- If no token's logit lies more than `spread` above the logit of `token`, the gap of `token` is at
most spread + 1. The 1 is added where the first choice is the smaller token. -/
theorem logitGap_le_of_close {vocabulary : Nat} (logits : IntegerTransformer.IntegerVector) {token : Token}
    (small : token < vocabulary) {spread : ℤ}
    (close : ∀ other < vocabulary, logits.entry other - logits.entry token ≤ spread) :
    logitGap vocabulary logits token ≤ spread + 1 := by
  have inside := (IntegerTransformer.firstArgmax_spec (fun v => logits.entry v) vocabulary
    (Nat.lt_of_le_of_lt (Nat.zero_le _) small)).1
  have near := close _ inside
  rw [logitGap_eq_choice logits small]
  split <;> omega

/-! ## 2. Clauses (a) and (b), for any costs on the positions below n -/

section Range
variable {n : ℕ} {cost : ℕ → ℤ} {policy : Inst.Model.AcceptancePolicy}

/-- Clause (a) in gaps: the costs, each clipped at C, sum to at most theta n exactly if the costs
less 2^8, each clipped at C - 2^8, sum to at most (theta - 2^8) n. An identity on whole numbers: no
condition on C or theta. -/
theorem meanClause_iff_gap :
    ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ↔
      ∑ j ∈ Finset.range n, min (cost j - 2 ^ 8) ((policy.C : ℤ) - 2 ^ 8) ≤
        ((policy.theta : ℤ) - 2 ^ 8) * (n : ℤ) := by
  have each : ∀ j ∈ Finset.range n,
      min (cost j - 2 ^ 8) ((policy.C : ℤ) - 2 ^ 8) = min (cost j) (policy.C : ℤ) - 2 ^ 8 :=
    fun j _ => by omega
  rw [Finset.sum_congr rfl each, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  constructor <;> intro h <;> linarith

/-- The sum of the clipped costs, cut in two at a set `free` of positions outside of which no cost
is above the clip. -/
theorem sum_clipped_split {free : Finset ℕ} (sub : free ⊆ Finset.range n) {C : ℤ}
    (inside : ∀ j ∈ Finset.range n \ free, cost j ≤ C) :
    ∑ j ∈ Finset.range n, min (cost j) C - (n : ℤ) * 2 ^ 8 =
      ∑ j ∈ Finset.range n \ free, (cost j - 2 ^ 8) + ∑ j ∈ free, (min (cost j) C - 2 ^ 8) := by
  have shift : ∑ j ∈ Finset.range n, (min (cost j) C - 2 ^ 8) =
      ∑ j ∈ Finset.range n, min (cost j) C - (n : ℤ) * 2 ^ 8 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have same : ∑ j ∈ Finset.range n \ free, (min (cost j) C - 2 ^ 8) =
      ∑ j ∈ Finset.range n \ free, (cost j - 2 ^ 8) :=
    Finset.sum_congr rfl fun j hj => by rw [min_eq_left (inside j hj)]
  rw [← shift, ← Finset.sum_sdiff sub, same]

/-- Clauses (a) and (b) as a budget. They hold exactly if there is a set `free` of at most cap
positions such that no position outside it costs more than C, and the costs less 2^8 outside it,
unclipped, with C - 2^8 for each member of `free`, sum to at most n (theta - 2^8). -/
theorem clauses_iff_budget :
    (∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) ↔
    ∃ free : Finset ℕ, free ⊆ Finset.range n ∧ free.card ≤ policy.cap ∧
      (∀ j ∈ Finset.range n \ free, cost j ≤ (policy.C : ℤ)) ∧
      ∑ j ∈ Finset.range n \ free, (cost j - 2 ^ 8) +
          (free.card : ℤ) * ((policy.C : ℤ) - 2 ^ 8) ≤
        (n : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) := by
  constructor
  · rintro ⟨a, b⟩
    have inside : ∀ j ∈ Finset.range n \ (Finset.range n).filter (fun j => (policy.C : ℤ) < cost j),
        cost j ≤ (policy.C : ℤ) := fun j hj =>
      not_lt.1 fun above => (Finset.mem_sdiff.1 hj).2
        (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hj).1, above⟩)
    refine ⟨(Finset.range n).filter (fun j => (policy.C : ℤ) < cost j), Finset.filter_subset _ _, b,
      inside, ?_⟩
    have split := sum_clipped_split (Finset.filter_subset _ _) inside
    have above : ∑ j ∈ (Finset.range n).filter (fun j => (policy.C : ℤ) < cost j),
        (min (cost j) (policy.C : ℤ) - 2 ^ 8) =
        ∑ _j ∈ (Finset.range n).filter (fun j => (policy.C : ℤ) < cost j),
          ((policy.C : ℤ) - 2 ^ 8) :=
      Finset.sum_congr rfl fun j hj => by
        rw [min_eq_right (le_of_lt (Finset.mem_filter.1 hj).2)]
    rw [Finset.sum_const, nsmul_eq_mul] at above
    rw [above] at split
    linarith
  · rintro ⟨free, sub, few, inside, budget⟩
    have split := sum_clipped_split sub inside
    have le : ∑ j ∈ free, (min (cost j) (policy.C : ℤ) - 2 ^ 8) ≤
        ∑ _j ∈ free, ((policy.C : ℤ) - 2 ^ 8) :=
      Finset.sum_le_sum fun j _ => sub_le_sub_right (min_le_right _ _) _
    rw [Finset.sum_const, nsmul_eq_mul] at le
    refine ⟨by linarith, le_trans (Finset.card_le_card fun j hj => ?_) few⟩
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    by_contra out
    exact absurd (inside j (Finset.mem_sdiff.2 ⟨hj1, out⟩)) (not_le.2 hj2)

/-- Smaller costs keep clauses (a) and (b). -/
theorem clauses_of_cost_le {cost' : ℕ → ℤ} (le : ∀ j < n, cost j ≤ cost' j)
    (a : ∑ j ∈ Finset.range n, min (cost' j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ))
    (b : ((Finset.range n).filter fun j => (policy.C : ℤ) < cost' j).card ≤ policy.cap) :
    ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap := by
  refine ⟨le_trans (Finset.sum_le_sum fun j hj =>
      min_le_min (le j (Finset.mem_range.1 hj)) (le_refl _)) a,
    le_trans (Finset.card_le_card fun j hj => ?_) b⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
  exact Finset.mem_filter.2 ⟨hj1, lt_of_lt_of_le hj2 (le j (Finset.mem_range.1 hj1))⟩

/-- If no cost is above a number k ≤ C, theta, then (a) and (b) hold, whatever cap is. -/
theorem clauses_of_cost_le_const {k : ℤ} (hk : ∀ j < n, cost j ≤ k) (clip : k ≤ policy.C)
    (mean : k ≤ policy.theta) :
    ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap := by
  obtain ⟨a, b⟩ := clauses_of_const (n := n) (cost := fun _ => k) (policy := policy)
    (fun _ _ => rfl) clip mean
  exact clauses_of_cost_le (cost' := fun _ => k) hk a b

/-- **The only numbers at which (a) and (b) hold of every list of n costs of at least 2^8.** They
hold of every list of n costs of at least 2^8 exactly if n = 0, or C ≤ theta and n ≤ cap. Limit: the
costs range over all whole numbers from 2^8 on, whether or not some weights reach them. So these
need not be the only policies that every output with scores and clause (c) meets. The integer
model's logits are bounded, and so are its gaps (an argument; no theorem here): a policy whose theta
and C are at least 2^8 plus the largest gap that any weights reach at the settings in question is
met by every output that has scores and meets clause (c) (`meetsPolicy_of_costs_le`). This file
gives no bound on that largest gap. A ceiling on it by two numbers of the settings:
`logitGap_le_gapCeiling` (Policy/Front/MeetsPolicyIdleAtScales.lean). At the settings of the
reference scales, for 1 ≤ n ≤ 1,023, among the policies with theta ≤ C < 2^32 (what a lawful table
of scales asks of these two numbers: `Inst.Model.Lawful`) they are the only ones that every output
of n counted tokens with scores and clause (c) meets under all weights
(`TeethAll.every_output_at_meets_iff`, Policy/Front/TeethAllChannels.lean). Under given weights more
policies are met by every such output (`meetsPolicy_of_close_logits`). -/
theorem clauses_forall_iff (n : ℕ) (policy : Inst.Model.AcceptancePolicy) :
    (∀ cost : ℕ → ℤ, (∀ j < n, (2 : ℤ) ^ 8 ≤ cost j) →
      ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
        ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) ↔
      n = 0 ∨ (policy.C ≤ policy.theta ∧ n ≤ policy.cap) := by
  constructor
  · intro all
    by_cases h0 : n = 0
    · exact Or.inl h0
    · right
      obtain ⟨a, b⟩ := all (fun _ => (policy.C : ℤ) + 2 ^ 8 + 1) (fun _ _ => by
        show (2 : ℤ) ^ 8 ≤ (policy.C : ℤ) + 2 ^ 8 + 1
        omega)
      have a' : ∑ _j ∈ Finset.range n, min ((policy.C : ℤ) + 2 ^ 8 + 1) (policy.C : ℤ) ≤
          (policy.theta : ℤ) * (n : ℤ) := a
      have b' : ((Finset.range n).filter fun _j =>
          (policy.C : ℤ) < (policy.C : ℤ) + 2 ^ 8 + 1).card ≤ policy.cap := b
      rw [min_eq_right (by omega), Finset.sum_const, Finset.card_range, nsmul_eq_mul] at a'
      rw [Finset.filter_true_of_mem fun _ _ => by omega, Finset.card_range] at b'
      have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have le : (policy.C : ℤ) ≤ (policy.theta : ℤ) :=
        le_of_mul_le_mul_right (by linarith : (policy.C : ℤ) * (n : ℤ) ≤ policy.theta * n) hn
      exact ⟨by exact_mod_cast le, b'⟩
  · rintro (rfl | ⟨clip, limit⟩) cost _
    · exact ⟨by simp, by simp⟩
    · exact clauses_of_clip_le_mean clip limit

/-- Where every cost is the least one, 2^8: (a) and (b) hold exactly if n = 0, or min(2^8,
C) ≤ theta and, in case C < 2^8, n ≤ cap. -/
theorem clauses_least_iff (hk : ∀ j < n, cost j = 2 ^ 8) :
    (∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) ↔
      n = 0 ∨ (min (2 ^ 8) policy.C ≤ policy.theta ∧ (policy.C < 2 ^ 8 → n ≤ policy.cap)) := by
  have same : ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) =
      ∑ _j ∈ Finset.range n, min (2 ^ 8) (policy.C : ℤ) :=
    Finset.sum_congr rfl fun j hj => by rw [hk j (Finset.mem_range.1 hj)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at same
  by_cases h0 : n = 0
  · subst h0
    simp
  · have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    constructor
    · rintro ⟨a, b⟩
      right
      rw [same] at a
      have m : min (2 ^ 8) (policy.C : ℤ) ≤ (policy.theta : ℤ) :=
        le_of_mul_le_mul_left
          (by linarith : (n : ℤ) * min (2 ^ 8) (policy.C : ℤ) ≤ (n : ℤ) * policy.theta) hn
      refine ⟨by omega, fun small => ?_⟩
      rw [Finset.filter_true_of_mem fun j hj => by
        rw [hk j (Finset.mem_range.1 hj)]
        exact_mod_cast small, Finset.card_range] at b
      exact b
    · rintro (h | ⟨mean, limit⟩)
      · exact absurd h h0
      · constructor
        · rw [same]
          have m : min (2 ^ 8) (policy.C : ℤ) ≤ (policy.theta : ℤ) := by omega
          have := mul_le_mul_of_nonneg_left m (le_of_lt hn)
          linarith
        · by_cases small : policy.C < 2 ^ 8
          · exact le_trans (Finset.card_filter_le _ _)
              (by rw [Finset.card_range]; exact limit small)
          · have none : ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j) = ∅ :=
              Finset.filter_false_of_mem fun j hj => by
                rw [hk j (Finset.mem_range.1 hj)]
                exact not_lt.2 (by exact_mod_cast not_lt.1 small)
            rw [none]
            exact Nat.zero_le _

/-- With C < 2^8 and costs of at least 2^8, (a) and (b) read no cost: they hold exactly if n ≤ cap
and, unless n = 0, C ≤ theta. -/
theorem clauses_iff_of_clip_lt (low : ∀ j < n, (2 : ℤ) ^ 8 ≤ cost j) (clip : policy.C < 2 ^ 8) :
    (∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) ↔
      (n = 0 ∨ policy.C ≤ policy.theta) ∧ n ≤ policy.cap := by
  have hC : (policy.C : ℤ) < 2 ^ 8 := by exact_mod_cast clip
  have same : ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) =
      ∑ _j ∈ Finset.range n, (policy.C : ℤ) :=
    Finset.sum_congr rfl fun j hj =>
      min_eq_right (le_of_lt (lt_of_lt_of_le hC (low j (Finset.mem_range.1 hj))))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at same
  have all : ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j) = Finset.range n :=
    Finset.filter_true_of_mem fun j hj => lt_of_lt_of_le hC (low j (Finset.mem_range.1 hj))
  rw [same, all, Finset.card_range]
  refine and_congr ?_ Iff.rfl
  constructor
  · intro a
    by_cases h0 : n = 0
    · exact Or.inl h0
    · right
      have hn : (0 : ℤ) < (n : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero h0
      have le : (policy.C : ℤ) ≤ (policy.theta : ℤ) :=
        le_of_mul_le_mul_right (by linarith : (policy.C : ℤ) * (n : ℤ) ≤ policy.theta * n) hn
      exact_mod_cast le
  · rintro (h0 | le)
    · rw [h0]
      simp
    · have le' : (policy.C : ℤ) ≤ (policy.theta : ℤ) := by exact_mod_cast le
      have := mul_le_mul_of_nonneg_left le' (Int.natCast_nonneg n)
      linarith

/-- Let C ≤ C', cap ≤ cap' and theta n + cap (C' - C) ≤ theta' n. Costs that meet (a) and (b) at
(C, theta, cap) meet them at (C', theta', cap'): each cost above C adds at most C' - C to the sum,
and a cost above C' is above C. -/
theorem clauses_raise_clip {policy' : Inst.Model.AcceptancePolicy} (clip : policy.C ≤ policy'.C)
    (limit : policy.cap ≤ policy'.cap)
    (room : (policy.theta : ℤ) * (n : ℤ) + (policy.cap : ℤ) * ((policy'.C : ℤ) - (policy.C : ℤ)) ≤
      (policy'.theta : ℤ) * (n : ℤ))
    (a : ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ))
    (b : ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) :
    ∑ j ∈ Finset.range n, min (cost j) (policy'.C : ℤ) ≤ (policy'.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun j => (policy'.C : ℤ) < cost j).card ≤ policy'.cap := by
  have hC : (policy.C : ℤ) ≤ (policy'.C : ℤ) := by exact_mod_cast clip
  constructor
  · have step : ∀ j ∈ Finset.range n, min (cost j) (policy'.C : ℤ) ≤
        min (cost j) (policy.C : ℤ) +
          if (policy.C : ℤ) < cost j then (policy'.C : ℤ) - (policy.C : ℤ) else 0 := by
      intro j _
      split <;> omega
    have sums := Finset.sum_le_sum step
    rw [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at sums
    have few : (((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card : ℤ) ≤
        (policy.cap : ℤ) := by exact_mod_cast b
    have := mul_le_mul_of_nonneg_right few (sub_nonneg.2 hC)
    linarith
  · refine le_trans (le_trans (Finset.card_le_card fun j hj => ?_) b) limit
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    exact Finset.mem_filter.2 ⟨hj1, lt_of_le_of_lt hC hj2⟩

end Range

/-! ## 3. The claim -/

section Claim
variable {settings : IntegerTransformer.Settings}

/-- The claim, as its four parts: scores, clause (c), clause (a), clause (b). By unfolding. -/
theorem meetsPolicy_iff_clauses (policy : Inst.Model.AcceptancePolicy) (weights : ModelWeights settings)
    (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
          min (outputCost settings weights prompt output position) (policy.C : ℤ)
        ≤ (policy.theta : ℤ) * (countedTokens settings prompt output : ℤ) ∧
      ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) < outputCost settings weights prompt output position).card ≤ policy.cap :=
  ⟨fun h => ⟨h.toHasScores, h.afterFullWindow, h.meanCost, h.aboveClip⟩,
    fun h => { toHasScores := h.1, meanCost := h.2.2.1, aboveClip := h.2.2.2,
               afterFullWindow := h.2.1 }⟩

/-- Every counted token of an output that has scores costs at least 2^8. -/
theorem outputCost_ge_of_counted {weights : ModelWeights settings} {prompt output : List Token}
    (scores : HasScores settings weights prompt output) :
    ∀ position < countedTokens settings prompt output,
      (2 : ℤ) ^ 8 ≤ outputCost settings weights prompt output position :=
  fun _ hp => outputCost_ge weights prompt
    (fun token member => scores.inVocabulary token (List.mem_append_right _ member))
    (lt_of_lt_of_le hp (Nat.min_le_left _ _))

/-- **If the output meets the policy, the mean clipped gap of its counted tokens is at most
theta - 2^8.** That is: if the output meets the policy, the gaps of its counted tokens, each clipped
at C - 2^8, sum to at most theta - 2^8 times their number (where no token is counted, both sides are
0). It is clause (a) in gaps, so it holds at every policy, and it is as strong as clause (a) and no
stronger. With C ≤ theta it holds of any gaps, since a clipped gap is at most C - 2^8
(`meetsPolicy_iff_of_clip_le_mean_anyCap`); with C ≤ 2^8 the clip is at most 0 and this clause reads
no gap (`meetsPolicy_iff_of_clip_lt`, `meetsPolicy_iff_of_clip_eq`). So it bounds gaps only for
2^8 ≤ theta < C. On lists of costs the bound is reached: if every cost is theta ≤ C, both sides are
(theta - 2^8) n (by reckoning; that such costs meet the clauses is `clauses_of_const`,
Policy/Front/MeetsPolicyGuards.lean). At weights: Policy/Front/Teeth.lean (`meetsPolicy_iff_xz`) has
outputs all of whose tokens have the one cost 2^8 + 2,047 (a + b). The unit is that of the model's
integer logits under the given weights; no scale for it is read. The counted tokens are those of
this one output, which in a soundness statement the prover picks and may cut as it likes. A token
above the clip enters as C - 2^8, whatever its gap: for the unclipped gaps see
`meetsPolicy_iff_budget`. -/
theorem MeetsPolicy.sum_clippedGap_le {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (h : MeetsPolicy settings policy weights prompt output) :
    ∑ position ∈ Finset.range (countedTokens settings prompt output),
        min (outputGap settings weights prompt output position) ((policy.C : ℤ) - 2 ^ 8)
      ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  have a := (meanClause_iff_gap (cost := outputCost settings weights prompt output)).1 h.meanCost
  simp only [outputCost_sub] at a
  exact a

/-- **The claim as a budget, with nothing lost.** The output meets the policy exactly if it has
scores, meets clause (c), and there is a set `free` of at most cap counted positions such that:
every other counted token has a gap of at most C - 2^8; and the gaps of these others, unclipped,
with C - 2^8 for each member of `free`, sum to at most n (theta - 2^8), where n is the number of
counted tokens. Of the gaps of the tokens at the positions of `free` nothing is asked. `HasScores`
still asks that they are tokens of the vocabulary and that the model has a value on their contexts,
and they are part of the later tokens' contexts. So, for 2^8 ≤ C, what an output may depart from the
model's choices is: up to cap tokens of any gap, each at the price C - 2^8, and gaps of
n (theta - 2^8) in all. (Below C = 2^8 the price is negative, and every counted token has to be set
aside.) The number of tokens that depart is not bounded: all may, if their gaps are small enough in
sum. The unit of a gap is that of the given weights' integer logits. n counts the tokens of this one
output, which in a soundness statement the prover picks and may cut as it likes. -/
theorem meetsPolicy_iff_budget (policy : Inst.Model.AcceptancePolicy) (weights : ModelWeights settings)
    (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      ∃ free : Finset ℕ, free ⊆ Finset.range (countedTokens settings prompt output) ∧
        free.card ≤ policy.cap ∧
        (∀ position ∈ Finset.range (countedTokens settings prompt output) \ free,
          outputGap settings weights prompt output position ≤ (policy.C : ℤ) - 2 ^ 8) ∧
        ∑ position ∈ Finset.range (countedTokens settings prompt output) \ free,
            outputGap settings weights prompt output position +
            (free.card : ℤ) * ((policy.C : ℤ) - 2 ^ 8) ≤
          (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) :=
  (meetsPolicy_iff_clauses policy weights prompt output).trans
    (and_congr_right fun _ => and_congr_right fun _ =>
      (clauses_iff_budget (n := countedTokens settings prompt output)
        (cost := outputCost settings weights prompt output) (policy := policy)).trans
        (by simp only [outputCost_sub, outputCost_le_iff]))

/-- With cap = 0: if the output meets the policy, the gaps of its counted tokens, unclipped, sum to
at most theta - 2^8 times their number, so their mean is at most theta - 2^8; and each of them is at
most C - 2^8 (`outputCost_le_clip_of_cap_zero`, Policy/Front/MeetsPolicyGuards.lean). The unit of a
gap is that of the given weights' integer logits. The counted tokens are those of this one output,
which in a soundness statement the prover picks and may cut as it likes. -/
theorem MeetsPolicy.sum_gap_le_of_cap_zero {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (h : MeetsPolicy settings policy weights prompt output) (limit : policy.cap = 0) :
    ∑ position ∈ Finset.range (countedTokens settings prompt output),
        outputGap settings weights prompt output position
      ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  have a := h.sum_clippedGap_le
  have same : ∑ position ∈ Finset.range (countedTokens settings prompt output),
        min (outputGap settings weights prompt output position) ((policy.C : ℤ) - 2 ^ 8) =
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
        outputGap settings weights prompt output position :=
    Finset.sum_congr rfl fun j hj => min_eq_left
      ((outputCost_le_iff settings weights prompt output j _).1
        (outputCost_le_clip_of_cap_zero h limit j (Finset.mem_range.1 hj)))
  rwa [same] at a

/-- **A condition on the numbers and the output's length under which the unclipped gaps of an output
that meets the policy are bounded.** Let 2^8 ≤ C and n (theta - 2^8) < C - 2^8, where n is the
number of counted tokens. If the output meets the policy, then no counted token reaches the clip
(every gap is below C - 2^8), so cap is not used, and the mean of the unclipped gaps is at most
theta - 2^8. The other way round: a token at or above the clip needs C - 2^8 ≤ n (theta - 2^8), that
is, an output that is long enough. With n = 0 both parts speak of no token. Without 2^8 ≤ C the
statement is false: (100, 100, 2) meets `short` at n = 2 and is met by every output of two counted
tokens that has scores and meets clause (c), while no gap is below 0. The form with 2^8 ≤ theta in
its place: `MeetsPolicy.sum_gap_le_of_short_of_mean`. The unit of a gap is that of the given
weights' integer logits. n counts the tokens of this one output, which in a soundness statement the
prover picks and may cut as it likes: so a user has this bound only for outputs that are short
enough, and for all outputs only under `MeetsPolicy.sum_gap_le_of_window`. -/
theorem MeetsPolicy.sum_gap_le_of_short {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (h : MeetsPolicy settings policy weights prompt output) (clip : 2 ^ 8 ≤ policy.C)
    (short : (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) <
      (policy.C : ℤ) - 2 ^ 8) :
    (∀ position < countedTokens settings prompt output,
        outputGap settings weights prompt output position < (policy.C : ℤ) - 2 ^ 8) ∧
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
        outputGap settings weights prompt output position
        ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  have hC : (0 : ℤ) ≤ (policy.C : ℤ) - 2 ^ 8 := by
    have : (2 : ℤ) ^ 8 ≤ (policy.C : ℤ) := by exact_mod_cast clip
    linarith
  have below : ∀ position < countedTokens settings prompt output,
      outputGap settings weights prompt output position < (policy.C : ℤ) - 2 ^ 8 := by
    intro j hj
    by_contra reach
    have hc : (policy.C : ℤ) ≤ outputCost settings weights prompt output j := by
      rw [outputCost_eq_outputGap_add]
      linarith [not_lt.1 reach]
    have member : j ∈ (Finset.range (countedTokens settings prompt output)).filter
        (fun position => (policy.C : ℤ) ≤ outputCost settings weights prompt output position) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hc⟩
    have one : (1 : ℤ) ≤ (((Finset.range (countedTokens settings prompt output)).filter
        fun position =>
          (policy.C : ℤ) ≤ outputCost settings weights prompt output position).card : ℤ) := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.card_pos.2 ⟨j, member⟩)
    have few := few_costly_of_meetsPolicy h (le_refl (policy.C : ℤ))
    have := mul_le_mul_of_nonneg_right one hC
    linarith
  refine ⟨below, ?_⟩
  have a := h.sum_clippedGap_le
  have same : ∑ position ∈ Finset.range (countedTokens settings prompt output),
        min (outputGap settings weights prompt output position) ((policy.C : ℤ) - 2 ^ 8) =
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
        outputGap settings weights prompt output position :=
    Finset.sum_congr rfl fun j hj => min_eq_left (le_of_lt (below j (Finset.mem_range.1 hj)))
  rwa [same] at a

/-- `MeetsPolicy.sum_gap_le_of_short` with 2^8 ≤ theta in the place of 2^8 ≤ C: with `short` it
gives 2^8 < C. -/
theorem MeetsPolicy.sum_gap_le_of_short_of_mean {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (h : MeetsPolicy settings policy weights prompt output) (mean : 2 ^ 8 ≤ policy.theta)
    (short : (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) <
      (policy.C : ℤ) - 2 ^ 8) :
    (∀ position < countedTokens settings prompt output,
        outputGap settings weights prompt output position < (policy.C : ℤ) - 2 ^ 8) ∧
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
          outputGap settings weights prompt output position
        ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  refine h.sum_gap_le_of_short ?_ short
  have hθ : (0 : ℤ) ≤ (policy.theta : ℤ) - 2 ^ 8 := by
    have : (2 : ℤ) ^ 8 ≤ (policy.theta : ℤ) := by exact_mod_cast mean
    linarith
  have := mul_nonneg (Int.natCast_nonneg (countedTokens settings prompt output)) hθ
  have le : (2 : ℤ) ^ 8 ≤ (policy.C : ℤ) := by linarith
  exact_mod_cast le

/-- **A condition on the policy's numbers and the window under which the unclipped gaps of every
output that meets the policy are bounded.** Let 2^8 ≤ theta and (positions - 1)
(theta - 2^8) < C - 2^8, where positions is the window of the settings (1,024 at valid settings). If
an output meets the policy, whatever its length, no counted token reaches the clip, and the gaps of
its counted tokens, unclipped, sum to at most theta - 2^8 times their number. An output has at most
positions - 1 counted tokens, since the prompt is not empty. At such a policy neither the clip nor
cap is ever used. (25856, 512, 1) is no such policy: 1,023 · 256 is not below 25,600. The unit of a
gap is that of the given weights' integer logits. The counted tokens are those of one output, which
in a soundness statement the prover picks and may cut as it likes. -/
theorem MeetsPolicy.sum_gap_le_of_window {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (h : MeetsPolicy settings policy weights prompt output) (mean : 2 ^ 8 ≤ policy.theta)
    (wide : ((settings.positions - 1 : ℕ) : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) <
      (policy.C : ℤ) - 2 ^ 8) :
    (∀ position < countedTokens settings prompt output,
        outputGap settings weights prompt output position < (policy.C : ℤ) - 2 ^ 8) ∧
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
          outputGap settings weights prompt output position
        ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  refine h.sum_gap_le_of_short_of_mean mean (lt_of_le_of_lt ?_ wide)
  have hθ : (0 : ℤ) ≤ (policy.theta : ℤ) - 2 ^ 8 := by
    have : (2 : ℤ) ^ 8 ≤ (policy.theta : ℤ) := by exact_mod_cast mean
    linarith
  have hp := List.length_pos_iff.2 h.promptNonempty
  have few : countedTokens settings prompt output ≤ settings.positions - 1 := by
    unfold countedTokens
    omega
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast few) hθ

/-- **A count of the large gaps of an output that meets the policy.** If the output meets the
policy, then for every number g ≤ C - 2^8 the number of counted tokens with a gap of g or more,
times g, is at most n (theta - 2^8). So, for 0 < g ≤ C - 2^8, of n counted tokens at most
n (theta - 2^8) / g have a gap of g or more. It is `few_costly_of_meetsPolicy`
(Policy/Front/MeetsPolicyGuards.lean) in gaps. For g ≤ theta - 2^8 it says nothing: all n tokens may
have such a gap. For g above C - 2^8 the count at C - 2^8 holds, and cap besides. The count grows
with n. The unit of a gap is that of the given weights' integer logits. n counts the tokens of this
one output, which in a soundness statement the prover picks and may cut as it likes. -/
theorem MeetsPolicy.card_gap_ge_mul_le {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (h : MeetsPolicy settings policy weights prompt output) {g : ℤ}
    (clip : g ≤ (policy.C : ℤ) - 2 ^ 8) :
    (((Finset.range (countedTokens settings prompt output)).filter fun position =>
        g ≤ outputGap settings weights prompt output position).card : ℤ) * g ≤
      (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) := by
  have few := few_costly_of_meetsPolicy h (c := g + 2 ^ 8) (by linarith)
  have same : ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        g + 2 ^ 8 ≤ outputCost settings weights prompt output position) =
      (Finset.range (countedTokens settings prompt output)).filter fun position =>
        g ≤ outputGap settings weights prompt output position :=
    Finset.filter_congr fun j _ => by
      rw [outputCost_eq_outputGap_add]
      constructor <;> intro le <;> linarith
  rw [same, add_sub_cancel_right] at few
  exact few

/-- **For 2^8 ≤ C, no counted token of an output that meets the policy has a clipped gap above the
whole budget.** Let 2^8 ≤ C. If the output meets the policy, the clipped gap of each counted token
is at most n (theta - 2^8). So a counted token that is not above the clip has a gap of at most
n (theta - 2^8). The bound grows with n: the longer the output, the larger the one departure that it
leaves room for. That one token may use up the whole budget is `meetsPolicy_of_one_departure`. -/
theorem MeetsPolicy.clippedGap_le {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (h : MeetsPolicy settings policy weights prompt output)
    (clip : 2 ^ 8 ≤ policy.C) {position : ℕ}
    (counted : position < countedTokens settings prompt output) :
    min (outputGap settings weights prompt output position) ((policy.C : ℤ) - 2 ^ 8)
      ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  have hC : (0 : ℤ) ≤ (policy.C : ℤ) - 2 ^ 8 := by
    have : (2 : ℤ) ^ 8 ≤ (policy.C : ℤ) := by exact_mod_cast clip
    linarith
  have nonneg : ∀ j ∈ Finset.range (countedTokens settings prompt output),
      0 ≤ min (outputGap settings weights prompt output j) ((policy.C : ℤ) - 2 ^ 8) := fun j hj =>
    le_min (outputGap_nonneg weights prompt
      (fun token member => h.inVocabulary token (List.mem_append_right _ member))
      (lt_of_lt_of_le (Finset.mem_range.1 hj) (Nat.min_le_left _ _))) hC
  exact le_trans
    (Finset.single_le_sum
      (f := fun j => min (outputGap settings weights prompt output j) ((policy.C : ℤ) - 2 ^ 8))
      nonneg (Finset.mem_range.2 counted))
    h.sum_clippedGap_le

/-- With C ≤ theta clause (a) says nothing: the claim is scores, clause (c), and "at most cap
counted tokens cost more than C". -/
theorem meetsPolicy_iff_of_clip_le_mean_anyCap {policy : Inst.Model.AcceptancePolicy}
    (clip : policy.C ≤ policy.theta) (weights : ModelWeights settings)
    (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) < outputCost settings weights prompt output position).card ≤ policy.cap := by
  rw [meetsPolicy_iff_clauses]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨fun h => h.2, fun b => ⟨?_, b⟩⟩
  exact (clauses_of_clip_le_mean (n := countedTokens settings prompt output)
    (cost := outputCost settings weights prompt output)
    (policy := ⟨policy.C, policy.theta, countedTokens settings prompt output⟩) clip (le_refl _)).1

/-- **A policy that every output with scores and clause (c) meets.** With C ≤ theta and
positions ≤ cap + 1, where positions is the window of the settings (1,024 at valid settings), the
claim is: the output has scores and meets clause (c). Clauses (a) and (b) hold of every output that
has scores, whatever its length: it has at most positions - 1 counted tokens. The form at one
output: `meetsPolicy_iff_of_clip_le_mean` (Policy/Front/MeetsPolicyGuards.lean). This theorem gives
a condition that is enough, at all settings. That at the settings of the reference scales no other
policy with theta ≤ C < 2^32 is met, under all weights, by every output with scores and clause (c):
`TeethAll.every_output_meets_iff` (Policy/Front/TeethAllChannels.lean). Under given weights others
are (`meetsPolicy_of_close_logits`). -/
theorem meetsPolicy_iff_of_idle {policy : Inst.Model.AcceptancePolicy} (clip : policy.C ≤ policy.theta)
    (limit : settings.positions ≤ policy.cap + 1) (weights : ModelWeights settings)
    (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      ∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position] := by
  constructor
  · intro h
    exact ⟨h.toHasScores, h.afterFullWindow⟩
  · rintro ⟨scores, after⟩
    have hp := List.length_pos_iff.2 scores.promptNonempty
    have few : countedTokens settings prompt output ≤ policy.cap := by
      unfold countedTokens
      omega
    exact (meetsPolicy_iff_of_clip_le_mean clip few).2 ⟨scores, after⟩

/-- With at most cap counted tokens clause (b) says nothing: the claim is scores, clause (c), and
the bound on the mean clipped gap. -/
theorem meetsPolicy_iff_of_counted_le_cap {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (limit : countedTokens settings prompt output ≤ policy.cap) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
          min (outputGap settings weights prompt output position) ((policy.C : ℤ) - 2 ^ 8)
        ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ) := by
  rw [meetsPolicy_iff_clauses]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [meanClause_iff_gap]
  simp only [outputCost_sub]
  exact ⟨fun h => h.1, fun a => ⟨a, (Finset.card_filter_le _ _).trans
    (by rw [Finset.card_range]; exact limit)⟩⟩

/-- With C < 2^8 clauses (a) and (b) read no score. Every token costs more than C, so the claim is:
scores, clause (c), C ≤ theta unless no token is counted, and at most cap counted tokens. -/
theorem meetsPolicy_iff_of_clip_lt {policy : Inst.Model.AcceptancePolicy} (clip : policy.C < 2 ^ 8)
    (weights : ModelWeights settings) (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      (countedTokens settings prompt output = 0 ∨ policy.C ≤ policy.theta) ∧
      countedTokens settings prompt output ≤ policy.cap := by
  rw [meetsPolicy_iff_clauses]
  exact and_congr_right fun scores => and_congr_right fun _ =>
    clauses_iff_of_clip_lt (outputCost_ge_of_counted scores) clip

/-- With C = 2^8 ≤ theta the policy counts departures and reads no size of a gap: the claim is
scores, clause (c), and "at most cap counted tokens have a gap other than 0". By
`outputGap_eq_zero_iff` these are the counted tokens that are not the model's next token. -/
theorem meetsPolicy_iff_of_clip_eq {policy : Inst.Model.AcceptancePolicy} (clip : policy.C = 2 ^ 8)
    (mean : 2 ^ 8 ≤ policy.theta) (weights : ModelWeights settings)
    (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        outputGap settings weights prompt output position ≠ 0).card ≤ policy.cap := by
  rw [meetsPolicy_iff_of_clip_le_mean_anyCap (by rw [clip]; exact mean)]
  refine and_congr_right fun scores => and_congr_right fun _ => ?_
  have hC : (policy.C : ℤ) = 2 ^ 8 := by exact_mod_cast clip
  have same : ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) < outputCost settings weights prompt output position) =
      (Finset.range (countedTokens settings prompt output)).filter fun position =>
        outputGap settings weights prompt output position ≠ 0 :=
    Finset.filter_congr fun j hj => by
      have low := outputCost_ge_of_counted scores j (Finset.mem_range.1 hj)
      rw [outputCost_eq_outputGap_add] at low ⊢
      rw [hC]
      constructor <;> intro h <;> omega
  rw [same]

/-- An output all of whose counted tokens cost at most a number k ≤ C, theta meets the policy,
whatever cap is, if it has scores and meets clause (c). -/
theorem meetsPolicy_of_costs_le {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position])
    {k : ℤ} (clip : k ≤ policy.C) (mean : k ≤ policy.theta)
    (le : ∀ position < countedTokens settings prompt output,
      outputCost settings weights prompt output position ≤ k) :
    MeetsPolicy settings policy weights prompt output :=
  (meetsPolicy_iff_clauses policy weights prompt output).2
    ⟨scores, after, clauses_of_cost_le_const le clip mean⟩

/-- **A caution on the weights.** Let the output have scores and meet clause (c). If, after the
context of each counted token, no token's logit lies more than `spread` above that token's logit,
the output meets every policy with 2^8 + spread + 1 ≤ C and 2^8 + spread + 1 ≤ theta, whatever cap
is. So under weights whose logits lie close together every output that has scores and meets clause
(c) meets such a policy: the policy's numbers say something only against the spread of the logits of
the weights in question, and whoever makes the weights sets that spread. At spread = 0 (the token's
logit is a largest one; for every token of a row: all logits of the row are equal) the bound is 257.
-/
theorem meetsPolicy_of_close_logits {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position])
    {spread : ℤ} (clip : 2 ^ 8 + spread + 1 ≤ (policy.C : ℤ))
    (mean : 2 ^ 8 + spread + 1 ≤ (policy.theta : ℤ))
    (close : ∀ position < countedTokens settings prompt output, ∀ other < settings.vocabulary,
      (modelLogits settings weights (prompt ++ output.take position)).entry other -
        (modelLogits settings weights (prompt ++ output.take position)).entry
          (output.getD position 0) ≤ spread) :
    MeetsPolicy settings policy weights prompt output := by
  refine meetsPolicy_of_costs_le scores after clip mean fun j hj => ?_
  have hj' : j < output.length := lt_of_lt_of_le hj (Nat.min_le_left _ _)
  have small : output.getD j 0 < settings.vocabulary := by
    rw [List.getD_eq_getElem _ _ hj']
    exact scores.inVocabulary _ (List.mem_append_right _ (List.getElem_mem hj'))
  have near := logitGap_le_of_close _ small (close j hj)
  rw [outputCost_eq_outputGap_add]
  unfold outputGap
  linarith

/-- **One departure may use up the whole budget, where the weights offer such a gap.** Let the
output have scores and meet clause (c), and let every counted token but the one at `departure` be
the model's next token. If the gap of that one token is at most C - 2^8 and at most n (theta - 2^8),
the output meets the policy, whatever cap is. With `MeetsPolicy.clippedGap_le`: for a token that is
not above the clip the bound n (theta - 2^8) is the exact one, wherever the weights offer a token of
such a gap. -/
theorem meetsPolicy_of_one_departure {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
      settings.positions ≤ prompt.length + position →
        modelNextToken settings weights (prompt ++ output.take position) = some output[position])
    {departure : ℕ} (counted : departure < countedTokens settings prompt output)
    (clip : outputGap settings weights prompt output departure ≤ (policy.C : ℤ) - 2 ^ 8)
    (room : outputGap settings weights prompt output departure ≤
      (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8))
    (others : ∀ position (h : position < output.length),
      position < countedTokens settings prompt output → position ≠ departure →
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position]) :
    MeetsPolicy settings policy weights prompt output := by
  have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
    scores.inVocabulary token (List.mem_append_right _ member)
  have zero : ∀ j ∈ Finset.range (countedTokens settings prompt output), j ≠ departure →
      outputGap settings weights prompt output j = 0 := fun j hj ne =>
    have hj' : j < countedTokens settings prompt output := Finset.mem_range.1 hj
    have hj'' : j < output.length := lt_of_lt_of_le hj' (Nat.min_le_left _ _)
    (outputGap_eq_zero_iff weights prompt small hj'' (scores.defined j hj'')).2
      (others j hj'' hj' ne)
  have g0 : 0 ≤ outputGap settings weights prompt output departure :=
    outputGap_nonneg weights prompt small (lt_of_lt_of_le counted (Nat.min_le_left _ _))
  refine (meetsPolicy_iff_budget policy weights prompt output).2
    ⟨scores, after, ∅, Finset.empty_subset _, Nat.zero_le _, ?_, ?_⟩
  · intro j hj
    rw [Finset.sdiff_empty] at hj
    by_cases e : j = departure
    · rw [e]
      exact clip
    · rw [zero j hj e]
      linarith
  · rw [Finset.sdiff_empty,
      Finset.sum_eq_single_of_mem departure (Finset.mem_range.2 counted) zero]
    simp only [Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
    exact room

/-- Which policies the model's own output meets, if it is not empty: all if no token is counted;
else those with min(2^8, C) ≤ theta and, in case C < 2^8, at least as large a cap as there are
counted tokens. -/
theorem meetsPolicy_isModelOutput_iff (policy : Inst.Model.AcceptancePolicy) {weights : ModelWeights settings}
    {prompt output : List Token} (nonempty : output ≠ [])
    (isOutput : ∀ position (h : position < output.length),
      modelNextToken settings weights (prompt ++ output.take position) = some output[position]) :
    MeetsPolicy settings policy weights prompt output ↔
      countedTokens settings prompt output = 0 ∨
        (min (2 ^ 8) policy.C ≤ policy.theta ∧
          (policy.C < 2 ^ 8 → countedTokens settings prompt output ≤ policy.cap)) := by
  have scores := hasScores_of_isModelOutput nonempty isOutput
  have small : ∀ token ∈ output, token < settings.vocabulary := fun token member =>
    scores.inVocabulary token (List.mem_append_right _ member)
  have hk : ∀ j < countedTokens settings prompt output,
      outputCost settings weights prompt output j = 2 ^ 8 := fun j hj =>
    have hj' : j < output.length := lt_of_lt_of_le hj (Nat.min_le_left _ _)
    (outputCost_eq_iff weights prompt small hj' (scores.defined j hj')).2 (isOutput j hj')
  rw [meetsPolicy_iff_clauses, ← clauses_least_iff hk]
  exact ⟨fun h => h.2.2, fun h => ⟨scores, fun position hp _ => isOutput position hp, h⟩⟩

/-- **A policy and a number of counted tokens at which nothing meets it.** If theta < min(2^8, C),
or C < 2^8 and cap is less than the number of counted tokens, then no output with that many counted
tokens, at least one, meets the policy, at any weights. The second case depends on the number:
(100, 100, 2) is met by outputs of one or two counted tokens. An output without a counted token
(after a full prompt) can meet every policy. The form on the policy's numbers alone:
`not_meetsPolicy_of_numbers`. By `meetsPolicy_isModelOutput_iff` these are exactly the policies that
reject the model's own output of that many counted tokens. -/
theorem not_meetsPolicy_of_refuses_least {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (counted : 0 < countedTokens settings prompt output)
    (refuses : ¬ (min (2 ^ 8) policy.C ≤ policy.theta ∧
      (policy.C < 2 ^ 8 → countedTokens settings prompt output ≤ policy.cap))) :
    ¬ MeetsPolicy settings policy weights prompt output := by
  intro h
  obtain ⟨a, b⟩ := clauses_of_cost_le (cost := fun _ => (2 : ℤ) ^ 8)
    (outputCost_ge_of_counted h.toHasScores) h.meanCost h.aboveClip
  rcases (clauses_least_iff (cost := fun _ => (2 : ℤ) ^ 8) (fun _ _ => rfl)).1 ⟨a, b⟩ with h0 | ok
  · omega
  · exact refuses ok

/-- **If theta < min(2^8, C), or C < 2^8 and cap = 0, no output with a counted token meets the
policy**, at any weights. These are all such policies: every other policy is met by the model's own
output of one counted token, where the model has one (`meetsPolicy_isModelOutput_iff` at one counted
token). -/
theorem not_meetsPolicy_of_numbers {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (counted : 0 < countedTokens settings prompt output)
    (numbers : policy.theta < min (2 ^ 8) policy.C ∨ (policy.C < 2 ^ 8 ∧ policy.cap = 0)) :
    ¬ MeetsPolicy settings policy weights prompt output := by
  refine not_meetsPolicy_of_refuses_least counted ?_
  rintro ⟨mean, limit⟩
  rcases numbers with low | ⟨small, none⟩
  · omega
  · have := limit small
    omega

/-- Raising the clip. Let C ≤ C', cap ≤ cap', and theta n + cap (C' - C) ≤ theta' n, where n is the
number of counted tokens. An output that meets (C, theta, cap) meets (C', theta', cap'). Without the
room in theta' a larger clip can reject an output (`meetsPolicy_reads_policy`,
Policy/Front/TrueUnder.lean): each token above C enters the sum with up to C' - C more. -/
theorem MeetsPolicy.raise_clip {policy policy' : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (clip : policy.C ≤ policy'.C) (limit : policy.cap ≤ policy'.cap)
    (room : (policy.theta : ℤ) * (countedTokens settings prompt output : ℤ) +
        (policy.cap : ℤ) * ((policy'.C : ℤ) - (policy.C : ℤ)) ≤
      (policy'.theta : ℤ) * (countedTokens settings prompt output : ℤ))
    (h : MeetsPolicy settings policy weights prompt output) :
    MeetsPolicy settings policy' weights prompt output :=
  (meetsPolicy_iff_clauses policy' weights prompt output).2
    ⟨h.toHasScores, h.afterFullWindow, clauses_raise_clip clip limit room h.meanCost h.aboveClip⟩

/-- With cap = 0 the claim is monotone in all three numbers: an output that meets (C, theta, 0)
meets every (C', theta', cap') with C ≤ C' and theta ≤ theta'. -/
theorem MeetsPolicy.mono_clip_of_cap_zero {policy policy' : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token} (limit : policy.cap = 0)
    (clip : policy.C ≤ policy'.C) (mean : policy.theta ≤ policy'.theta)
    (h : MeetsPolicy settings policy weights prompt output) :
    MeetsPolicy settings policy' weights prompt output := by
  refine h.raise_clip clip (by rw [limit]; exact Nat.zero_le _) ?_
  have le : (policy.theta : ℤ) ≤ (policy'.theta : ℤ) := by exact_mod_cast mean
  have := mul_le_mul_of_nonneg_right le (Int.natCast_nonneg (countedTokens settings prompt output))
  rw [limit]
  push_cast
  linarith

end Claim

end Policy

#print axioms Policy.outputGap
#print axioms Policy.outputCost_eq_outputGap_add
#print axioms Policy.outputCost_sub
#print axioms Policy.outputCost_le_iff
#print axioms Policy.outputGap_nonneg
#print axioms Policy.outputGap_eq_zero_iff
#print axioms Policy.logitGap_le_of_close
#print axioms Policy.meanClause_iff_gap
#print axioms Policy.sum_clipped_split
#print axioms Policy.clauses_iff_budget
#print axioms Policy.clauses_of_cost_le
#print axioms Policy.clauses_of_cost_le_const
#print axioms Policy.clauses_forall_iff
#print axioms Policy.clauses_least_iff
#print axioms Policy.clauses_iff_of_clip_lt
#print axioms Policy.clauses_raise_clip
#print axioms Policy.meetsPolicy_iff_clauses
#print axioms Policy.outputCost_ge_of_counted
#print axioms Policy.MeetsPolicy.sum_clippedGap_le
#print axioms Policy.meetsPolicy_iff_budget
#print axioms Policy.MeetsPolicy.sum_gap_le_of_cap_zero
#print axioms Policy.MeetsPolicy.sum_gap_le_of_short
#print axioms Policy.MeetsPolicy.sum_gap_le_of_short_of_mean
#print axioms Policy.MeetsPolicy.sum_gap_le_of_window
#print axioms Policy.MeetsPolicy.card_gap_ge_mul_le
#print axioms Policy.MeetsPolicy.clippedGap_le
#print axioms Policy.meetsPolicy_iff_of_clip_le_mean_anyCap
#print axioms Policy.meetsPolicy_iff_of_idle
#print axioms Policy.meetsPolicy_iff_of_counted_le_cap
#print axioms Policy.meetsPolicy_iff_of_clip_lt
#print axioms Policy.meetsPolicy_iff_of_clip_eq
#print axioms Policy.meetsPolicy_of_costs_le
#print axioms Policy.meetsPolicy_of_close_logits
#print axioms Policy.meetsPolicy_of_one_departure
#print axioms Policy.meetsPolicy_isModelOutput_iff
#print axioms Policy.not_meetsPolicy_of_refuses_least
#print axioms Policy.not_meetsPolicy_of_numbers
#print axioms Policy.MeetsPolicy.raise_clip
#print axioms Policy.MeetsPolicy.mono_clip_of_cap_zero
