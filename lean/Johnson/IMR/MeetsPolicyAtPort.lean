-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/MeetsPolicyAtPort.lean

The claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean) beside two functions of the library's port
of the programs' verifier, `aboveClip` and `policyEmpty` (OnBytes/Model/Config.lean), at the
exponent 8. Theorems with proofs; no definition; no goal of the library is stated or changed here.
The general theorems on the claim are in Policy/Front/MeetsPolicyBounds.lean, and those at the
clipped-gap policy (C, theta, cap) = (25856, 512, 1) in Policy/Front/MeetsPolicyAtGap.lean. That
policy is `AtChosen.qExample` (Policy/Rel/AtChosen.lean; `qExample_eq`,
Policy/Front/MeetsPolicyAtGap.lean): hence "qExample" in two names below. Below, n is the number of
counted tokens of the one output in question.

Why the file lies in this folder: it imports a file of Policy/ and a file of OnBytes/. By
scripts/IMPORTS.txt no file of either folder may import the other; a file of Johnson/ may import
both. The other files of Johnson/IMR/ are lemmas of the proof about verify(); this file is not one
of them, and no file imports it. The theorems are in the namespace `Policy`.

* `card_above_le_aboveClip`: the number that `aboveClip` returns is an upper bound on the counted
  tokens above the clip of an output that meets the policy. `aboveClip_qExample`: at (25856, 512, 1)
  it returns 0 below n = 100 and 1 from there on.
* `policyEmpty_cases` and the five theorems on single values: for which numbers `policyEmpty`
  returns 0, 1, 2, 3, 4; n is one of them. What the claim is there, for an output of n counted
  tokens: at 1 clauses (a) and (b) read no score (`meetsPolicy_iff_of_clip_lt`,
  Policy/Front/MeetsPolicyBounds.lean); at 2 no output with a counted token meets the policy
  (`not_meetsPolicy_of_policyEmpty_two`); at 4 every output of that many counted tokens, with scores
  and clause (c), meets it (`meetsPolicy_iff_of_policyEmpty_four`); at 0, for n > 0, clauses (a) and
  (b) admit the least costs and reject some list of costs (`clauses_of_policyEmpty_zero`). At 3 a
  result can mean something: (256, 300, 0) gives 3 (`policyEmpty_three_example`), and there the
  claim is exact match (`meetsPolicy_iff_of_clip_eq`, Policy/Front/MeetsPolicyBounds.lean); no
  parameter file may set theta above C. `policyEmpty_qExample`: at (25856, 512, 1) it returns 0.

Limits.
* All theorems here are on the library's port of two functions, at the exponent 8. That the programs
  compute the same is a reading, and no theorem. Where the library's port of the verifier calls the
  two functions is a reading too, and no theorem: it calls `aboveClip` at min e (T - 1) - r
  (OnBytes/Model/Stages.lean), and `policyEmpty` only where the call names a policy, at 0 before a
  request is read and then at the same number (`cpPolicySays`, `cpPolicyHeld`,
  OnBytes/Model/VerifyHeads.lean); at the values 1 to 4 it rejects the call (`policyEnd` there).
  That min e (T - 1) - r is the number of counted tokens of a built request is a reading as well.
* That `policyEmpty` returns 0 says only that none of the function's four cases holds. A policy at 0
  can still be met by every output with scores and clause (c) at given weights
  (`meetsPolicy_of_close_logits`, Policy/Front/MeetsPolicyBounds.lean), and at valid settings with
  MF ≤ KF + 11 one such policy is, under all weights (`exists_policy_of_close_scales`,
  Policy/Front/MeetsPolicyIdleAtScales.lean).
* All limits of Policy/Front/MeetsPolicyBounds.lean hold here. The unit of a cost is that of the
  given weights' own integer logits, and n counts one output, which in a soundness statement the
  prover picks and may cut.
* No theorem here says what a verifier accepts. Nothing here speaks of a protocol, a commitment or a
  prover.

-/
import Policy.Front.MeetsPolicyBounds
import OnBytes.Model.ConfigPolicyLaws

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference

section Claim
variable {settings : IntegerTransformer.Settings}

/-- If the output meets the policy, the number of its counted tokens above the clip is at most what
`OnBytes.Model.aboveClip` returns at the number of counted tokens, the policy's three numbers and
the exponent 8. It holds at every policy; where no output with that many counted tokens meets the
policy (`not_meetsPolicy_of_refuses_least`) it says nothing. For 2^8 ≤ C and 2^8 ≤ theta that many
counted tokens may be any tokens of the vocabulary, if the output has scores and meets clause (c)
and the others are the model's next tokens (`meetsPolicy_of_few_costly`,
Policy/Front/MeetsPolicyGuards.lean); whether they lie above the clip depends on the weights. -/
theorem card_above_le_aboveClip {policy : Inst.Model.AcceptancePolicy} {weights : ModelWeights settings}
    {prompt output : List Token} (h : MeetsPolicy settings policy weights prompt output) :
    ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) < outputCost settings weights prompt output position).card ≤
      OnBytes.Model.aboveClip (countedTokens settings prompt output) policy.C policy.theta
        policy.cap 8 := by
  have b := h.aboveClip
  have kn : ((Finset.range (countedTokens settings prompt output)).filter fun position =>
      (policy.C : ℤ) < outputCost settings weights prompt output position).card ≤
      countedTokens settings prompt output :=
    (Finset.card_filter_le _ _).trans (le_of_eq (Finset.card_range _))
  have few := few_costly_of_meetsPolicy h (le_refl (policy.C : ℤ))
  have sub : ((Finset.range (countedTokens settings prompt output)).filter fun position =>
      (policy.C : ℤ) < outputCost settings weights prompt output position).card ≤
      ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) ≤ outputCost settings weights prompt output position).card :=
    Finset.card_le_card fun j hj =>
      Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hj).1, le_of_lt (Finset.mem_filter.1 hj).2⟩
  generalize ((Finset.range (countedTokens settings prompt output)).filter fun position =>
      (policy.C : ℤ) < outputCost settings weights prompt output position).card = K at b kn sub ⊢
  generalize ((Finset.range (countedTokens settings prompt output)).filter fun position =>
      (policy.C : ℤ) ≤ outputCost settings weights prompt output position).card = K' at few sub
  generalize countedTokens settings prompt output = n at kn few ⊢
  unfold OnBytes.Model.aboveClip
  simp only [OnBytes.Model.least_eight]
  by_cases hC : policy.C ≤ 256
  · rw [if_pos hC]
    exact le_min b kn
  · rw [if_neg hC]
    refine le_min ?_ (le_min b kn)
    have e1 : ((policy.C - 256 : ℕ) : ℤ) = (policy.C : ℤ) - 2 ^ 8 := by omega
    have pos : (0 : ℤ) < (policy.C : ℤ) - 2 ^ 8 := by omega
    have kk : (K : ℤ) * ((policy.C : ℤ) - 2 ^ 8) ≤ (n : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast sub) (le_of_lt pos)) few
    by_cases hθ : 256 < policy.theta
    · rw [if_pos hθ]
      have e2 : ((policy.theta - 256 : ℕ) : ℤ) = (policy.theta : ℤ) - 2 ^ 8 := by
        rw [Nat.cast_sub (le_of_lt hθ)]
        norm_num
      refine (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt (not_le.1 hC))).2 ?_
      have cast : ((K * (policy.C - 256) : ℕ) : ℤ) ≤ ((n * (policy.theta - 256) : ℕ) : ℤ) := by
        rw [Nat.cast_mul, Nat.cast_mul, e1, e2]
        exact kk
      exact_mod_cast cast
    · rw [if_neg hθ]
      have nonpos : (n : ℤ) * ((policy.theta : ℤ) - 2 ^ 8) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) (by omega)
      by_contra more
      have one : (1 : ℤ) ≤ (K : ℤ) := by omega
      have := mul_le_mul_of_nonneg_right one (le_of_lt pos)
      linarith

end Claim

/-- What `OnBytes.Model.aboveClip` returns at (25856, 512, 1) and the exponent 8: 0 below n = 100,
and 1 from there on. -/
theorem aboveClip_qExample (n : ℕ) :
    OnBytes.Model.aboveClip n 25856 512 1 8 = if n < 100 then 0 else 1 := by
  rw [OnBytes.Model.aboveClip_eq (by decide) (by decide)]
  split <;> omega

/-- What `OnBytes.Model.policyEmpty` returns at (25856, 512, 1) and the exponent 8: 0, whatever n
is. The 0 says only that none of the function's four cases holds. A policy at 0 can still be met by
every output with scores and clause (c) at given weights (`meetsPolicy_of_close_logits`,
Policy/Front/MeetsPolicyBounds.lean: where no logit lies more than 255 above the output token's). -/
theorem policyEmpty_qExample (n : ℕ) : OnBytes.Model.policyEmpty n 25856 512 1 8 = 0 :=
  OnBytes.Model.policyEmpty_zero (by decide) (by decide)

/-- `OnBytes.Model.policyEmpty` at the exponent 8, with its tests as plain comparisons. -/
theorem policyEmpty_eq (n C theta cap : ℕ) :
    OnBytes.Model.policyEmpty n C theta cap 8 =
      if C < 256 then 1 else if theta < 256 then 2 else if C < theta then 3
      else if theta = C ∧ 0 < n ∧ n ≤ cap then 4 else 0 := by
  have key : ((theta == C && n != 0 && decide (n ≤ cap)) = true) ↔
      (theta = C ∧ 0 < n ∧ n ≤ cap) := by
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩
      exact ⟨a, Nat.pos_of_ne_zero b, c⟩
    · rintro ⟨a, b, c⟩
      exact ⟨⟨a, Nat.ne_of_gt b⟩, c⟩
  unfold OnBytes.Model.policyEmpty
  simp only [OnBytes.Model.least_eight]
  by_cases h4 : (theta == C && n != 0 && decide (n ≤ cap)) = true
  · rw [if_pos h4, if_pos (key.1 h4)]
  · rw [if_neg h4, if_neg fun c => h4 (key.2 c)]

/-- The five cases of `OnBytes.Model.policyEmpty` at the exponent 8, each with its value. -/
theorem policyEmpty_cases (n C theta cap : ℕ) :
    (C < 256 ∧ OnBytes.Model.policyEmpty n C theta cap 8 = 1) ∨
    (256 ≤ C ∧ theta < 256 ∧ OnBytes.Model.policyEmpty n C theta cap 8 = 2) ∨
    (256 ≤ C ∧ C < theta ∧ OnBytes.Model.policyEmpty n C theta cap 8 = 3) ∨
    (256 ≤ theta ∧ theta = C ∧ 0 < n ∧ n ≤ cap ∧
      OnBytes.Model.policyEmpty n C theta cap 8 = 4) ∨
    (256 ≤ theta ∧ theta ≤ C ∧ (theta ≠ C ∨ n = 0 ∨ cap < n) ∧
      OnBytes.Model.policyEmpty n C theta cap 8 = 0) := by
  rw [policyEmpty_eq]
  by_cases h1 : C < 256
  · exact Or.inl ⟨h1, if_pos h1⟩
  · rw [if_neg h1]
    by_cases h2 : theta < 256
    · exact Or.inr (Or.inl ⟨by omega, h2, if_pos h2⟩)
    · rw [if_neg h2]
      by_cases h3 : C < theta
      · exact Or.inr (Or.inr (Or.inl ⟨by omega, h3, if_pos h3⟩))
      · rw [if_neg h3]
        by_cases h4 : theta = C ∧ 0 < n ∧ n ≤ cap
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            ⟨by omega, h4.1, h4.2.1, h4.2.2, if_pos h4⟩)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr
            ⟨by omega, by omega, by omega, if_neg h4⟩)))

/-- `OnBytes.Model.policyEmpty` at the exponent 8 returns 1 exactly if C < 2^8. There clauses (a)
and (b) read no score (`meetsPolicy_iff_of_clip_lt`, Policy/Front/MeetsPolicyBounds.lean). -/
theorem policyEmpty_eq_one_iff (n C theta cap : ℕ) :
    OnBytes.Model.policyEmpty n C theta cap 8 = 1 ↔ C < 2 ^ 8 := by
  rcases policyEmpty_cases n C theta cap with
    ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, h3, h4, e⟩ | ⟨h1, h2, h3, e⟩ <;>
  rw [e] <;> constructor <;> intro g <;> omega

/-- `OnBytes.Model.policyEmpty` at the exponent 8 returns 2 exactly if theta < 2^8 ≤ C. -/
theorem policyEmpty_eq_two_iff (n C theta cap : ℕ) :
    OnBytes.Model.policyEmpty n C theta cap 8 = 2 ↔ 2 ^ 8 ≤ C ∧ theta < 2 ^ 8 := by
  rcases policyEmpty_cases n C theta cap with
    ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, h3, h4, e⟩ | ⟨h1, h2, h3, e⟩ <;>
  rw [e] <;> constructor <;> intro g <;> omega

/-- `OnBytes.Model.policyEmpty` at the exponent 8 returns 3 exactly if 2^8 ≤ C < theta. A result
under such a policy can mean something: clause (a) says nothing there, and clause (b) can bind
(`meetsPolicy_iff_of_clip_le_mean_anyCap`, Policy/Front/MeetsPolicyBounds.lean). -/
theorem policyEmpty_eq_three_iff (n C theta cap : ℕ) :
    OnBytes.Model.policyEmpty n C theta cap 8 = 3 ↔ 2 ^ 8 ≤ C ∧ C < theta := by
  rcases policyEmpty_cases n C theta cap with
    ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, h3, h4, e⟩ | ⟨h1, h2, h3, e⟩ <;>
  rw [e] <;> constructor <;> intro g <;> omega

/-- `OnBytes.Model.policyEmpty` at the exponent 8 returns 4 exactly if 2^8 ≤ theta = C and
0 < n ≤ cap. -/
theorem policyEmpty_eq_four_iff (n C theta cap : ℕ) :
    OnBytes.Model.policyEmpty n C theta cap 8 = 4 ↔
      2 ^ 8 ≤ theta ∧ theta = C ∧ 0 < n ∧ n ≤ cap := by
  rcases policyEmpty_cases n C theta cap with
    ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, h3, h4, e⟩ | ⟨h1, h2, h3, e⟩ <;>
  rw [e] <;> constructor <;> intro g <;> omega

/-- At (256, 300, 0) `OnBytes.Model.policyEmpty` returns 3. A result under that policy would mean
something: by `meetsPolicy_iff_of_clip_eq` (Policy/Front/MeetsPolicyBounds.lean) the claim there is
scores, clause (c), and that no counted token has a gap other than 0, which is exact match. The
example shows that the value 3 is not "a result would mean nothing". It does not show that such a
file can occur: theta is above C, which no parameter file may set (the docstring of `policyEmpty`).
-/
theorem policyEmpty_three_example (n : ℕ) : OnBytes.Model.policyEmpty n 256 300 0 8 = 3 :=
  (policyEmpty_eq_three_iff n 256 300 0).2 (by omega)

/-- `OnBytes.Model.policyEmpty` at the exponent 8 returns 0 exactly if 2^8 ≤ theta ≤ C, and not
(theta = C and 0 < n ≤ cap). -/
theorem policyEmpty_eq_zero_iff (n C theta cap : ℕ) :
    OnBytes.Model.policyEmpty n C theta cap 8 = 0 ↔
      2 ^ 8 ≤ theta ∧ theta ≤ C ∧ ¬ (theta = C ∧ 0 < n ∧ n ≤ cap) := by
  have key : ((theta == C && n != 0 && decide (n ≤ cap)) = true) ↔
      (theta = C ∧ 0 < n ∧ n ≤ cap) := by
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩
      exact ⟨a, Nat.pos_of_ne_zero b, c⟩
    · rintro ⟨a, b, c⟩
      exact ⟨⟨a, Nat.ne_of_gt b⟩, c⟩
  unfold OnBytes.Model.policyEmpty
  simp only [OnBytes.Model.least_eight]
  by_cases h1 : C < 256
  · rw [if_pos h1]
    exact ⟨fun e => absurd e (by decide), fun ⟨_, _, _⟩ => by omega⟩
  · rw [if_neg h1]
    by_cases h2 : theta < 256
    · rw [if_pos h2]
      exact ⟨fun e => absurd e (by decide), fun ⟨_, _, _⟩ => by omega⟩
    · rw [if_neg h2]
      by_cases h3 : C < theta
      · rw [if_pos h3]
        exact ⟨fun e => absurd e (by decide), fun ⟨_, _, _⟩ => by omega⟩
      · rw [if_neg h3]
        by_cases h4 : (theta == C && n != 0 && decide (n ≤ cap)) = true
        · rw [if_pos h4]
          exact ⟨fun e => absurd e (by decide), fun ⟨_, _, c⟩ => absurd (key.1 h4) c⟩
        · rw [if_neg h4]
          exact ⟨fun _ => ⟨by omega, by omega, fun c => h4 (key.2 c)⟩, fun _ => rfl⟩

/-- Where `OnBytes.Model.policyEmpty` returns 0 and n > 0: clauses (a) and (b) hold of n costs of
2^8, the least ones, and there is a list of n costs of at least 2^8 of which they do not both hold.
The costs of that list need not be reached by any weights. -/
theorem clauses_of_policyEmpty_zero {n : ℕ} {policy : Inst.Model.AcceptancePolicy} (counted : 0 < n)
    (zero : OnBytes.Model.policyEmpty n policy.C policy.theta policy.cap 8 = 0) :
    (∑ _j ∈ Finset.range n, min ((2 : ℤ) ^ 8) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
      ((Finset.range n).filter fun _j => (policy.C : ℤ) < (2 : ℤ) ^ 8).card ≤ policy.cap) ∧
    ∃ cost : ℕ → ℤ, (∀ j < n, (2 : ℤ) ^ 8 ≤ cost j) ∧
      ¬ (∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
        ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap) := by
  obtain ⟨mean, clip, notIdle⟩ := (policyEmpty_eq_zero_iff n _ _ _).1 zero
  constructor
  · exact (clauses_least_iff (cost := fun _ => (2 : ℤ) ^ 8) (fun _ _ => rfl)).2
      (Or.inr ⟨by omega, fun small => by omega⟩)
  · by_contra none
    have all : ∀ cost : ℕ → ℤ, (∀ j < n, (2 : ℤ) ^ 8 ≤ cost j) →
        ∑ j ∈ Finset.range n, min (cost j) (policy.C : ℤ) ≤ (policy.theta : ℤ) * (n : ℤ) ∧
          ((Finset.range n).filter fun j => (policy.C : ℤ) < cost j).card ≤ policy.cap :=
      fun cost low => by
        by_contra refused
        exact none ⟨cost, low, refused⟩
    rcases (clauses_forall_iff n policy).1 all with h0 | ⟨le, limit⟩
    · omega
    · exact notIdle ⟨le_antisymm clip le, counted, limit⟩

section Claim
variable {settings : IntegerTransformer.Settings}

/-- Where `OnBytes.Model.policyEmpty` returns 4 at the number of counted tokens: the claim is that
the output has scores and meets clause (c). Clauses (a) and (b) hold whatever the costs are. -/
theorem meetsPolicy_iff_of_policyEmpty_four {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (four : OnBytes.Model.policyEmpty (countedTokens settings prompt output) policy.C policy.theta
      policy.cap 8 = 4) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      ∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position] := by
  obtain ⟨-, same, -, limit⟩ := (policyEmpty_eq_four_iff _ _ _ _).1 four
  exact meetsPolicy_iff_of_clip_le_mean (le_of_eq same.symm) limit

/-- Where `OnBytes.Model.policyEmpty` returns 2 and a token is counted, the output does not meet the
policy, at any weights. -/
theorem not_meetsPolicy_of_policyEmpty_two {policy : Inst.Model.AcceptancePolicy}
    {weights : ModelWeights settings} {prompt output : List Token}
    (two : OnBytes.Model.policyEmpty (countedTokens settings prompt output) policy.C policy.theta
      policy.cap 8 = 2)
    (counted : 0 < countedTokens settings prompt output) :
    ¬ MeetsPolicy settings policy weights prompt output := by
  obtain ⟨clip, mean⟩ := (policyEmpty_eq_two_iff _ _ _ _).1 two
  exact not_meetsPolicy_of_mean_lt mean clip counted

end Claim

end Policy

#print axioms Policy.card_above_le_aboveClip
#print axioms Policy.aboveClip_qExample
#print axioms Policy.policyEmpty_qExample
#print axioms Policy.policyEmpty_eq
#print axioms Policy.policyEmpty_cases
#print axioms Policy.policyEmpty_eq_one_iff
#print axioms Policy.policyEmpty_eq_two_iff
#print axioms Policy.policyEmpty_eq_three_iff
#print axioms Policy.policyEmpty_eq_four_iff
#print axioms Policy.policyEmpty_three_example
#print axioms Policy.policyEmpty_eq_zero_iff
#print axioms Policy.clauses_of_policyEmpty_zero
#print axioms Policy.meetsPolicy_iff_of_policyEmpty_four
#print axioms Policy.not_meetsPolicy_of_policyEmpty_two
