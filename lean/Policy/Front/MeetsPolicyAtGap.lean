-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/MeetsPolicyAtGap.lean

The claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean) at the clipped-gap policy
(C, theta, cap) = (25856, 512, 1). It is `AtChosen.qExample` (Policy/Rel/AtChosen.lean;
`qExample_eq`), and the policy that Ladder.lean names for its second set of public files. By a
reading, the file config/policy.txt of examples/full-size-clipped-gap/ has these three numbers; no
theorem of this file ties them to a parameter file. That the library's reader of the public files
returns them at the second named set (`zGap`, Ladder/Stored.lean): `pol_gap`,
Johnson/Goal/Files/FilesReadAtRef.lean. The theorems of this file at these numbers, at what the
reader returns there: Johnson/Goal/Files/MeetsPolicyAtFiles.lean. In gaps: the clip is 25,600, the
bound on the mean clipped gap is 256, and one token may lie above the clip. The general theorems are
in Policy/Front/MeetsPolicyBounds.lean. No goal of the library is stated here. Below, n
is the number of counted tokens of the one output in question.

Part 1: every policy with cap = 1, then these numbers.
* `meetsPolicy_iff_of_cap_one`, `meetsPolicy_qExample_iff`: the claim written out. Besides scores
  and clause (c): either every counted token has a gap of at most 25,600 and the gaps sum to at most
  256 n; or this holds with one counted token left out, of whose gap nothing is asked and which is
  charged 25,600.
* `gaps_of_meetsPolicy_qExample_short`: if an output with at most 99 counted tokens meets the
  policy, every gap is below 25,600 and the mean gap, unclipped, is at most 256.
  `counted_ge_of_meetsPolicy_qExample`: a counted token at or above the clip needs at least 100
  counted tokens. `meetsPolicy_qExample_of_one_free`: from 100 on, in an output with scores and
  clause (c), one counted token may be any token of the vocabulary, if all the others are the
  model's next tokens. From 100 counted tokens on the policy's numbers give no bound on the
  unclipped mean: one token may have any gap that the weights offer (`Teeth.qExample_far_iff` with
  `Teeth.outputGap_xMiss`, at m = 1: a mean of about 16,390, against 256).
* `card_gap_ge_mul_le_qExample`: of n counted tokens at most 256 n / g have a gap of g or more, for
  0 < g ≤ 25,600. cap counts only the tokens strictly above 25,600: at n = 1,023 ten tokens of gap
  25,600 are within the budget, with cap unused (by reckoning: 256,000 ≤ 261,888).
* `meetsPolicy_qExample_of_gaps_le`: an output with scores and clause (c) all of whose counted gaps
  are at most 256 meets the policy. So no counted token need be the model's choice, where the
  weights offer other tokens within 256.
Part 2: outputs at made-up weights.
* `Teeth.meetsPolicy_xMiss_base`, `Teeth.countedTokens_xMiss`, `Teeth.outputGap_xMiss`: at the
  settings of the reference scales and the made-up weights with the votes a and b (`Votes`, and
  1 ≤ a), for m ≤ 1,023: after the prompt of one token 1, the output of m tokens 0 and then
  1,023 - m tokens 1 has scores and 1,023 counted tokens; its first m tokens have
  the gap 2,047 (a + b) and the others the gap 0. It meets clause (c), which asks nothing of it:
  prompt and output have 1,024 tokens together, so no token follows a full window.
* `Teeth.meetsPolicy_iff_xMiss`, `Teeth.qExample_mixed_iff`: an output that mixes the model's
  choices with other tokens. Of 1,023 output tokens let the first m have the gap 2,047 and the
  others be the model's choices. The output meets (25856, 512, 1) exactly if m ≤ 127. Here
  2,047 · 127 = 259,969 ≤ 256 · 1,023 = 261,888 < 2,047 · 128: the budget is used up to within one
  token's gap (the mean gap is about 254.1, against 256).
* `Teeth.qExample_far_iff`: the same with the gap 16,766,977, which is above the clip: exactly if
  m ≤ 1.
For which policies every output of at most cap counted tokens meets the policy, at the reference
scales and all weights: `TeethAll.every_short_output_meets_iff`
(Policy/Front/TeethAllChannels.lean). What two functions of the library's port of the programs'
verifier, `aboveClip` and `policyEmpty` (OnBytes/Model/Config.lean), return at these and at other
numbers, and what the claim is there: Johnson/IMR/MeetsPolicyAtPort.lean.

Limits.
* The claim does not bound how many counted tokens differ from the model's choice: given scores and
  clause (c), all may, if their gaps are at most 25,600 each and sum to at most 256 n (the first
  case of `meetsPolicy_qExample_iff`; `meetsPolicy_qExample_of_gaps_le` is the case of gaps of at
  most 256 each). cap limits only the tokens whose gap is above 25,600.
* The three numbers were fitted to no model and no reply (the example's README.md says how they were
  picked). Nothing here says that they are a sensible policy.
* A gap's unit is that of the integer model's logits under the given weights. No definition here
  reads a scale for it. What 256 or 25,600 of these units are worth depends on the weights. A gap is
  the difference of two logits, and 1 more where the first choice is the smaller token.
* All limits of Policy/Front/MeetsPolicyBounds.lean hold here: one output, which the prover picks
  and may cut (after a prompt of at most 24 tokens, a reply of 1,000 tokens that is cut into ten
  outputs of 100 has room for ten tokens of any gap, one in each, if all its other tokens are the
  model's next tokens; by reckoning, no theorem); each token scored after the output's own earlier
  tokens; nothing on whether the weights are a sensible model (`meetsPolicy_of_close_logits`: where
  no logit lies more than 255 above the output token's, an output with scores and clause (c) meets
  this policy).
* Part 2: the weights are those of Policy/Rel/Teeth.lean, made up, with the same logits after every
  context, at the reference scales (`Cm.sRef`) alone. That these are the scales which the library's
  reader returns at the two named sets of public files: Johnson/Goal/Files/FilesReadAtRef.lean.
  `Teeth.qExample_mixed_iff` and `Teeth.qExample_far_iff` at what the reader returns at the second
  named set: Johnson/Goal/Files/MeetsPolicyAtFiles.lean. The m other tokens stand first in the
  output: nothing is shown on where in an output a costly token may stand. No example here meets the
  budget with equality. Nothing is shown at a trained model.
* No theorem here says what a verifier accepts. Nothing here speaks of a protocol, a commitment or a
  prover.

-/
import Policy.Front.MeetsPolicyBounds
import Policy.Front.Teeth
import Policy.Rel.AtChosen

set_option autoImplicit false

/- No default table of scales is in sight in this file: the low-priority instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever takes an `Scl` has to say which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy

open VerifiableInference

/-! ## 1. Policies with cap = 1, and the numbers (25856, 512, 1) -/

section Claim
variable {settings : IntegerTransformer.Settings}

/-- The claim at a policy with cap = 1, written out. The output has scores and meets clause (c), and
one of two: every counted token has a gap of at most C - 2^8, and the gaps sum to at most
n (theta - 2^8); or there is one counted position `free` such that every other counted token has a
gap of at most C - 2^8, and the others' gaps with C - 2^8 sum to at most n (theta - 2^8). -/
theorem meetsPolicy_iff_of_cap_one {policy : Inst.Model.AcceptancePolicy} (limit : policy.cap = 1)
    (weights : ModelWeights settings) (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      (((∀ position < countedTokens settings prompt output,
            outputGap settings weights prompt output position ≤ (policy.C : ℤ) - 2 ^ 8) ∧
          ∑ position ∈ Finset.range (countedTokens settings prompt output),
              outputGap settings weights prompt output position ≤
            (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8)) ∨
        ∃ free < countedTokens settings prompt output,
          (∀ position < countedTokens settings prompt output, position ≠ free →
            outputGap settings weights prompt output position ≤ (policy.C : ℤ) - 2 ^ 8) ∧
          ∑ position ∈ (Finset.range (countedTokens settings prompt output)).erase free,
              outputGap settings weights prompt output position + ((policy.C : ℤ) - 2 ^ 8) ≤
            (countedTokens settings prompt output : ℤ) * ((policy.theta : ℤ) - 2 ^ 8)) := by
  rw [meetsPolicy_iff_budget]
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨free, sub, few, inside, budget⟩
    rw [limit] at few
    have cases : free.card = 0 ∨ free.card = 1 := by omega
    rcases cases with h0 | h1
    · left
      rw [Finset.card_eq_zero] at h0
      subst h0
      rw [Finset.sdiff_empty] at inside budget
      simp only [Finset.card_empty, Nat.cast_zero, zero_mul, add_zero] at budget
      exact ⟨fun j hj => inside j (Finset.mem_range.2 hj), budget⟩
    · right
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
      rw [Finset.sdiff_singleton_eq_erase] at inside budget
      simp only [Finset.card_singleton, Nat.cast_one, one_mul] at budget
      exact ⟨a, Finset.mem_range.1 (Finset.singleton_subset_iff.1 sub),
        fun j hj ne => inside j (Finset.mem_erase.2 ⟨ne, Finset.mem_range.2 hj⟩), budget⟩
  · rintro (⟨inside, budget⟩ | ⟨a, ha, inside, budget⟩)
    · refine ⟨∅, Finset.empty_subset _, Nat.zero_le _, ?_, ?_⟩
      · intro j hj
        rw [Finset.sdiff_empty] at hj
        exact inside j (Finset.mem_range.1 hj)
      · rw [Finset.sdiff_empty]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul, add_zero]
        exact budget
    · refine ⟨{a}, Finset.singleton_subset_iff.2 (Finset.mem_range.2 ha),
        le_of_eq (by rw [limit, Finset.card_singleton]), ?_, ?_⟩
      · intro j hj
        rw [Finset.sdiff_singleton_eq_erase] at hj
        exact inside j (Finset.mem_range.1 (Finset.mem_of_mem_erase hj))
          (Finset.ne_of_mem_erase hj)
      · rw [Finset.sdiff_singleton_eq_erase]
        simp only [Finset.card_singleton, Nat.cast_one, one_mul]
        exact budget

/-- The policy of this file is `AtChosen.qExample`. -/
theorem qExample_eq : AtChosen.qExample = ⟨25856, 512, 1⟩ :=
  rfl

/-- The clip of (25856, 512, 1) in gaps. -/
theorem qExample_clip : (((⟨25856, 512, 1⟩ : Inst.Model.AcceptancePolicy).C : ℤ) - 2 ^ 8) = 25600 := by
  show ((25856 : ℕ) : ℤ) - 2 ^ 8 = 25600
  norm_num

/-- The bound of (25856, 512, 1) on the mean, in gaps. -/
theorem qExample_mean : (((⟨25856, 512, 1⟩ : Inst.Model.AcceptancePolicy).theta : ℤ) - 2 ^ 8) = 256 := by
  show ((512 : ℕ) : ℤ) - 2 ^ 8 = 256
  norm_num

/-- **The claim at (25856, 512, 1), written out.** The output has scores and meets clause (c), and
one of two: every counted token has a gap of at most 25,600, and the gaps sum to at most 256 n; or
there is one counted position `free` such that every other counted token has a gap of at most
25,600, and the others' gaps with 25,600 sum to at most 256 n. Of the gap of the token at `free`
nothing is asked. `HasScores` still asks that it is a token of the vocabulary and that the model has
a value on its context, and it is part of the later tokens' contexts. The second case needs n ≥ 100,
since no gap is below 0. The claim does not bound how many counted tokens differ from the model's
choice: all may, if their gaps are at most 25,600 each and sum to at most 256 n (the first case
above; `meetsPolicy_qExample_of_gaps_le` is the case of gaps of at most 256 each). The limit of one
is on tokens whose gap is above 25,600; how many can have a gap of g or more, for g ≤ 25,600:
`card_gap_ge_mul_le_qExample`. The unit of a gap is that of the given weights' integer logits. n
counts the tokens of this one output, which in a soundness statement the prover picks and may cut as
it likes. -/
theorem meetsPolicy_qExample_iff (weights : ModelWeights settings) (prompt output : List Token) :
    MeetsPolicy settings ⟨25856, 512, 1⟩ weights prompt output ↔
      HasScores settings weights prompt output ∧
      (∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position]) ∧
      (((∀ position < countedTokens settings prompt output,
            outputGap settings weights prompt output position ≤ 25600) ∧
          ∑ position ∈ Finset.range (countedTokens settings prompt output),
              outputGap settings weights prompt output position ≤
            (countedTokens settings prompt output : ℤ) * 256) ∨
        ∃ free < countedTokens settings prompt output,
          (∀ position < countedTokens settings prompt output, position ≠ free →
            outputGap settings weights prompt output position ≤ 25600) ∧
          ∑ position ∈ (Finset.range (countedTokens settings prompt output)).erase free,
              outputGap settings weights prompt output position + 25600 ≤
            (countedTokens settings prompt output : ℤ) * 256) := by
  have general := meetsPolicy_iff_of_cap_one (policy := ⟨25856, 512, 1⟩) rfl weights prompt output
  rw [qExample_clip, qExample_mean] at general
  exact general

/-- **Outputs of at most 99 counted tokens that meet (25856, 512, 1).** If an output with at most 99
counted tokens meets the policy, every counted token's gap is below 25,600, and the gaps, unclipped,
sum to at most 256 n: the mean gap is at most 256, and no token is free. The unit of a gap is that
of the given weights' integer logits. The counted tokens are those of this one output, which in a
soundness statement the prover picks and may cut as it likes. -/
theorem gaps_of_meetsPolicy_qExample_short {weights : ModelWeights settings}
    {prompt output : List Token}
    (h : MeetsPolicy settings ⟨25856, 512, 1⟩ weights prompt output)
    (short : countedTokens settings prompt output ≤ 99) :
    (∀ position < countedTokens settings prompt output,
        outputGap settings weights prompt output position < 25600) ∧
      ∑ position ∈ Finset.range (countedTokens settings prompt output),
          outputGap settings weights prompt output position
        ≤ 256 * (countedTokens settings prompt output : ℤ) := by
  have hn : (countedTokens settings prompt output : ℤ) ≤ 99 := by exact_mod_cast short
  have general := h.sum_gap_le_of_short (by decide) (by
    rw [qExample_clip, qExample_mean]
    linarith)
  rw [qExample_clip, qExample_mean] at general
  exact general

/-- **At (25856, 512, 1) a counted token at or above the clip needs 100 counted tokens.** If an
output meets (25856, 512, 1) and one of its counted tokens has a gap of 25,600 or more, it has at
least 100 counted tokens. At 100 counted tokens one token of any gap does pass, if the output has
scores and meets clause (c) and the other 99 are the model's next tokens
(`meetsPolicy_of_few_costly`, Policy/Front/MeetsPolicyGuards.lean: 1 · 25,600 ≤ 100 · 256). -/
theorem counted_ge_of_meetsPolicy_qExample {weights : ModelWeights settings}
    {prompt output : List Token}
    (h : MeetsPolicy settings ⟨25856, 512, 1⟩ weights prompt output) {position : ℕ}
    (counted : position < countedTokens settings prompt output)
    (large : 25600 ≤ outputGap settings weights prompt output position) :
    100 ≤ countedTokens settings prompt output := by
  by_contra few
  have below := (gaps_of_meetsPolicy_qExample_short h (by omega)).1 position counted
  omega

/-- **A count of the large gaps of an output that meets (25856, 512, 1).** If the output meets the
policy, then for every number g ≤ 25,600 the number of counted tokens with a gap of g or more, times
g, is at most 256 n. So of n counted tokens at most 256 n / g have a gap of g or more, for
0 < g ≤ 25,600: at most n / 100 at or above the clip. For g ≤ 256 it says nothing. The count grows
with n, the number of counted tokens of this one output, which in a soundness statement the prover
picks and may cut as it likes. -/
theorem card_gap_ge_mul_le_qExample {weights : ModelWeights settings} {prompt output : List Token}
    (h : MeetsPolicy settings ⟨25856, 512, 1⟩ weights prompt output) {g : ℤ} (clip : g ≤ 25600) :
    (((Finset.range (countedTokens settings prompt output)).filter fun position =>
        g ≤ outputGap settings weights prompt output position).card : ℤ) * g ≤
      (countedTokens settings prompt output : ℤ) * 256 := by
  have general := h.card_gap_ge_mul_le (g := g) (by
    rw [qExample_clip]
    exact clip)
  rw [qExample_mean] at general
  exact general

/-- **For an output with scores and clause (c), counted gaps of at most 256 are enough to meet
(25856, 512, 1).** An output that has scores and meets clause (c), and all of whose counted tokens
have a gap of at most 256, meets (25856, 512, 1). So no counted token need be the model's choice
where the weights offer other tokens within 256: under the all-zero weights every token is within 1
(`meetsPolicy_zeroWeights`, Policy/Front/TrueUnder.lean). -/
theorem meetsPolicy_qExample_of_gaps_le {weights : ModelWeights settings}
    {prompt output : List Token} (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position])
    (le : ∀ position < countedTokens settings prompt output,
      outputGap settings weights prompt output position ≤ 256) :
    MeetsPolicy settings ⟨25856, 512, 1⟩ weights prompt output :=
  meetsPolicy_of_costs_le scores after (k := 512)
    (by
      show (512 : ℤ) ≤ ((25856 : ℕ) : ℤ)
      norm_num)
    (by
      show (512 : ℤ) ≤ ((512 : ℕ) : ℤ)
      norm_num)
    (fun j hj => by
      rw [outputCost_eq_outputGap_add]
      have := le j hj
      linarith)

/-- **From 100 counted tokens on, one counted token may be any token of the vocabulary, if all the
other counted tokens are the model's next tokens.** Let the output have scores and meet clause (c),
and let it have at least 100 counted tokens. If every counted token but the one at `free` is the
model's next token, the output meets (25856, 512, 1), whatever the gap of the token at `free`. More
room than that: by `meetsPolicy_qExample_iff` it is enough that the others' gaps are at most 25,600
each and sum to at most 256 n - 25,600. -/
theorem meetsPolicy_qExample_of_one_free {weights : ModelWeights settings}
    {prompt output : List Token} (scores : HasScores settings weights prompt output)
    (after : ∀ position (h : position < output.length),
        settings.positions ≤ prompt.length + position →
          modelNextToken settings weights (prompt ++ output.take position) =
            some output[position])
    (long : 100 ≤ countedTokens settings prompt output) (free : ℕ)
    (others : ∀ position (h : position < output.length),
      position < countedTokens settings prompt output → position ≠ free →
        modelNextToken settings weights (prompt ++ output.take position) =
          some output[position]) :
    MeetsPolicy settings ⟨25856, 512, 1⟩ weights prompt output := by
  refine meetsPolicy_of_few_costly (by decide) scores after {free}
    (le_of_eq (Finset.card_singleton free)) ?_
    (fun position h counted out => others position h counted
      fun e => out (Finset.mem_singleton.2 e))
  have hn : (100 : ℤ) ≤ (countedTokens settings prompt output : ℤ) := by exact_mod_cast long
  rw [Finset.card_singleton, qExample_clip, qExample_mean, Nat.cast_one, one_mul]
  linarith

end Claim

end Policy

/-! ## 2. Outputs at made-up weights -/

namespace Policy.Teeth

open VerifiableInference
open Inst.Model Inst.Model.RequestGuards2

/-- A list of one a, then m times z, then k times a, read at a position inside it. -/
theorem getD_mixed {α : Type} (a z d : α) (m k j : ℕ) (hj : j < 1 + m + k) :
    ([a] ++ (List.replicate m z ++ List.replicate k a) ++ []).getD j d =
      if 1 ≤ j ∧ j ≤ m then z else a := by
  rw [List.append_nil, List.getD_eq_getElem?_getD]
  rcases Nat.eq_zero_or_pos j with rfl | hpos
  · rw [if_neg (show ¬ (1 ≤ 0 ∧ 0 ≤ m) by omega)]
    rfl
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [List.singleton_append, List.getElem?_cons_succ]
    by_cases hi : i < m
    · rw [List.getElem?_append_left (by rw [List.length_replicate]; exact hi),
        List.getElem?_replicate, if_pos hi,
        if_pos (show 1 ≤ i + 1 ∧ i + 1 ≤ m from ⟨by omega, by omega⟩)]
      rfl
    · rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
        List.length_replicate, List.getElem?_replicate, if_pos (show i - m < k by omega),
        if_neg (show ¬ (1 ≤ i + 1 ∧ i + 1 ≤ m) by omega)]
      rfl

/-- For m ≤ 1,023: the request built from the prompt of one token 1, the output of m tokens 0 and
then 1,023 - m tokens 1, and no padding is `xMiss m` (Policy/Rel/TeethCount.lean). Prompt and output
fill the window. -/
theorem built_xMiss {m : ℕ} (hm : m ≤ 1023) :
    requestOfTokens ([1], List.replicate m 0 ++ List.replicate (1023 - m) 1) [] =
      some (xMiss m) := by
  have z1 : vocabularyTokens [1] = some [Policy.tokenOne] :=
    vocabularyTokens_map_val [Policy.tokenOne]
  have z2 : vocabularyTokens (List.replicate m 0 ++ List.replicate (1023 - m) 1) =
      some (List.replicate m IntegerModel.tokenZero ++
        List.replicate (1023 - m) Policy.tokenOne) := by
    have := vocabularyTokens_map_val (List.replicate m IntegerModel.tokenZero ++
      List.replicate (1023 - m) Policy.tokenOne)
    rwa [List.map_append, List.map_replicate, List.map_replicate] at this
  rw [requestOfTokens_eq z1 z2 rfl]
  unfold IntegerModel.requestOf
  rw [dif_pos ⟨by decide, by
    rw [List.length_append, List.length_replicate, List.length_replicate]
    omega, by
    rw [List.length_append, List.length_replicate, List.length_replicate]
    show 1 + (m + (1023 - m)) ≤ 1024 + 1
    omega⟩]
  refine congrArg some ?_
  unfold xMiss
  congr 1
  · funext t
    have ht : t.val < 1024 := t.isLt
    rw [getD_mixed Policy.tokenOne IntegerModel.tokenZero IntegerModel.tokenZero m (1023 - m) t.val
      (by omega)]
    rfl
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
      rw [List.length_append, List.length_append, List.length_replicate, List.length_replicate]
      show 1 + (m + (1023 - m)) ≤ 1024
      omega)]
    rfl
  · apply Fin.ext
    show 1 - 1 + (List.replicate m IntegerModel.tokenZero ++
      List.replicate (1023 - m) Policy.tokenOne).length = 1023
    rw [List.length_append, List.length_replicate, List.length_replicate]
    omega

/-- For a, b with `Votes`, every policy and m ≤ 1,023, at the settings of the reference scales and
the weights that `idxAB h` holds: after the prompt of one token 1, the output of m tokens 0 and then
1,023 - m tokens 1 meets the policy if and only if the request `xMiss m` is true under it. With
`xMiss_iff` (Policy/Rel/TeethCount.lean) this says for which policies. -/
theorem meetsPolicy_iff_xMiss {a b : ℤ} (h : Votes a b) (pol : AcceptancePolicy) {m : ℕ} (hm : m ≤ 1023) :
    MeetsPolicy (settingsOf Cm.sRef) pol
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h)) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) ↔
      IsTrueUnder Cm.sRef pol (idxAB h) (xMiss m) := by
  rw [isTrueUnder_iff_meetsPolicy Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl
    pol (idxAB h) (built_xMiss hm)]
  exact ⟨fun x => ⟨runsK_idxAB h _, x⟩, fun x => x.2⟩

/-- For a, b with `Votes` and 1 ≤ a, and m ≤ 1,023, at the settings of the reference scales and the
made-up weights that `idxAB h` holds: after the prompt of one token 1, the output of m tokens 0 and
then 1,023 - m tokens 1 meets the policy (256, 256, 1023). At this policy clauses (a) and (b) ask
nothing of this output: C = theta, and cap is its number of counted tokens
(`meetsPolicy_iff_of_clip_le_mean`, Policy/Front/MeetsPolicyGuards.lean). Clause (c) asks nothing of
it either: prompt and output have 1,024 tokens together, so no token follows a full window. So what
the theorem gives is `HasScores`. Scores and clause (c) are parts of the claim that do not read the
policy. `exists_outputs_at_budget_gap` and `exists_outputs_above_clip_gap`
(Johnson/Goal/Files/MeetsPolicyAtFiles.lean) take both from here. -/
theorem meetsPolicy_xMiss_base {a b : ℤ} (h : Votes a b) (ha : 1 ≤ a) {m : ℕ} (hm : m ≤ 1023) :
    MeetsPolicy (settingsOf Cm.sRef) ⟨256, 256, 1023⟩
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h)) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) := by
  rw [meetsPolicy_iff_xMiss h _ hm, xMiss_iff h ha _ (by decide) hm]
  have a0 := h.a0
  have b0 := h.b0
  have e : min ((2 : ℤ) ^ 8 + 2047 * (a + b)) (((⟨256, 256, 1023⟩ : AcceptancePolicy).C : ℕ) : ℤ) = 2 ^ 8 := by
    show min ((2 : ℤ) ^ 8 + 2047 * (a + b)) ((256 : ℕ) : ℤ) = 2 ^ 8
    rw [min_eq_right (by omega)]
    norm_num
  rw [e]
  refine ⟨?_, fun _ => hm⟩
  show (m : ℤ) * 2 ^ 8 + (1023 - (m : ℤ)) * 2 ^ 8 ≤ ((256 : ℕ) : ℤ) * 1023
  omega

/-- For m ≤ 1,023, at the settings of the reference scales: after the prompt of one token 1, all
1,023 tokens of the output of m tokens 0 and then 1,023 - m tokens 1 are counted. -/
theorem countedTokens_xMiss {m : ℕ} (hm : m ≤ 1023) :
    countedTokens (settingsOf Cm.sRef) [1] (List.replicate m 0 ++ List.replicate (1023 - m) 1) =
      1023 := by
  unfold countedTokens
  rw [(Back.valid_numbers (settingsAreValid_settingsOf Cm.lawful_sRef)).1, List.length_append,
    List.length_replicate, List.length_replicate, List.length_singleton]
  omega

/-- **The gaps of that output, token by token.** For a, b with `Votes` and 1 ≤ a, and m ≤ 1,023, at
the settings of the reference scales and the made-up weights that `idxAB h` holds: after the prompt
of one token 1, in the output of m tokens 0 and then 1,023 - m tokens 1, each of the first m tokens
has the gap 2,047 (a + b), and each of the others has the gap 0. It is `cost_xMiss`
(Policy/Rel/TeethCount.lean), a theorem on the cost of the library's relation on a request, brought
to `outputGap` by `outputCost_eq_costOf` (Policy/Front/TrueUnder.lean). The output has scores
(`meetsPolicy_xMiss_base`), so by `outputGap_eq_zero_iff` (Policy/Front/MeetsPolicyBounds.lean) its
tokens of gap 0 are the model's next tokens. -/
theorem outputGap_xMiss {a b : ℤ} (h : Votes a b) (ha : 1 ≤ a) {m : ℕ} (hm : m ≤ 1023) {j : ℕ}
    (hj : j < 1023) :
    outputGap (settingsOf Cm.sRef)
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h)) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) j =
      if j < m then 2047 * (a + b) else 0 := by
  obtain ⟨p, o, pad, hp, ho, -, hx⟩ := requestOfTokens_some (built_xMiss hm)
  have ep : p.map Fin.val = [1] := map_val_of_vocabularyTokens _ p hp
  have eo : o.map Fin.val = List.replicate m 0 ++ List.replicate (1023 - m) 1 :=
    map_val_of_vocabularyTokens _ o ho
  have lp : p.length = 1 := by
    have l := congrArg List.length ep
    rw [List.length_map, List.length_singleton] at l
    exact l
  have lo : o.length = 1023 := by
    have l := congrArg List.length eo
    rw [List.length_map, List.length_append, List.length_replicate, List.length_replicate] at l
    omega
  have cost := outputCost_eq_costOf (IntegerModel.committedOf Cm.sRef Cm.lawful_sRef (idxAB h))
    (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h))
    (feeds_of_tie Cm.lawful_sRef (settingsAreValid_settingsOf Cm.lawful_sRef) rfl (idxAB h)) hx
    (j := j) (by rw [lo]; exact hj) (by
      rw [lp]
      show 1 + j ≤ 1024
      omega)
  rw [ep, eo] at cost
  have cost' : outputCost (settingsOf Cm.sRef)
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB h)) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) j =
      costOf (lgK ppref Cm.sRef.kap Cm.sRef.nf (fun _ => tbRef) (idxAB h).index.val
        (xMiss m).prompt) (xMiss m) ((xMiss m).r + j) := cost
  have logits : lgK ppref Cm.sRef.kap Cm.sRef.nf (fun _ => tbRef) (idxAB h).index.val
      (xMiss m).prompt = lg ppref tbRef (wtsAB a b) (xMiss m).prompt := by
    unfold idxAB
    rw [Cm.index_ofIndex]
    show lgK ppref ppRef.kap ppref.nf (fun _ => tbRef) (wtsAB a b) (xMiss m).prompt = _
    rw [kap_ref, Cm.lgK_ref]
  have r0 : (xMiss m).r + j = j := by
    show 0 + j = j
    omega
  rw [logits, r0, cost_xMiss h ha hj, outputCost_eq_outputGap_add] at cost'
  by_cases c : j < m
  · rw [if_pos c] at cost' ⊢
    linarith
  · rw [if_neg c] at cost' ⊢
    linarith

/-- **An example at made-up weights in which the budget of (25856, 512, 1) is used up to within one
token's gap.** At the settings of the reference scales and the made-up weights of
Policy/Rel/Teeth.lean with the votes a = 1, b = 0 (that file's two numbers), in the outputs below
each token 1 has the gap 0 and each token 0 the gap 2,047, which is below the clip
(`outputGap_xMiss` at a = 1, b = 0; the statement below tells no gap). The logits are the same at
every position of every request (for the library's relation on a request: `lg_wtsAB`,
Policy/Rel/Teeth.lean). After the prompt of one token 1, for m ≤ 1,023, the output of m tokens 0 and
then 1,023 - m tokens 1 meets (25856, 512, 1) if and only if m ≤ 127. All 1,023 output tokens are
counted, so the budget is 256 · 1,023 = 261,888, and
2,047 · 127 = 259,969 ≤ 261,888 < 262,016 = 2,047 · 128. It is clause (a) that rejects from m = 128
on: no token is above the clip. -/
theorem qExample_mixed_iff {m : ℕ} (hm : m ≤ 1023) :
    MeetsPolicy (settingsOf Cm.sRef) ⟨25856, 512, 1⟩
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) (idxAB AtChosen.votes_one)) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) ↔ m ≤ 127 := by
  rw [meetsPolicy_iff_xMiss AtChosen.votes_one _ hm,
    xMiss_iff AtChosen.votes_one (le_refl 1) _ (by decide) hm]
  have e : min ((2 : ℤ) ^ 8 + 2047 * (1 + 0)) (((⟨25856, 512, 1⟩ : AcceptancePolicy).C : ℕ) : ℤ) = 2303 := by
    show min ((2 : ℤ) ^ 8 + 2047 * (1 + 0)) ((25856 : ℕ) : ℤ) = 2303
    rw [min_eq_left (by norm_num)]
    norm_num
  rw [e]
  constructor
  · rintro ⟨h1, -⟩
    have h1' : (m : ℤ) * 2303 + (1023 - (m : ℤ)) * 2 ^ 8 ≤ ((512 : ℕ) : ℤ) * 1023 := h1
    omega
  · intro le
    refine ⟨?_, fun above => ?_⟩
    · show (m : ℤ) * 2303 + (1023 - (m : ℤ)) * 2 ^ 8 ≤ ((512 : ℕ) : ℤ) * 1023
      omega
    · have above' : ((25856 : ℕ) : ℤ) < 2 ^ 8 + 2047 * (1 + 0) := above
      norm_num at above'

/-- **An example at made-up weights in which one token above the clip passes (25856, 512, 1), and
two do not.** At the settings of the reference scales and the made-up weights that `iTeeth` holds,
in the outputs below each token 1 has the gap 0 and each token 0 the gap 16,766,977, far above the
clip (`outputGap_xMiss` at a = 4,095, b = 4,096: 2,047 · 8,191; the statement below tells no gap).
The logits are the same at every position of every request (for the library's relation on a request:
`lg_wtsAB`, Policy/Rel/Teeth.lean). After the prompt of one token 1, for m ≤ 1,023, the output of m
tokens 0 and then 1,023 - m tokens 1 meets (25856, 512, 1) if and only if m ≤ 1. At m = 2 clause (a)
holds (2 · 25,856 + 1,021 · 256 ≤ 512 · 1,023), so it is clause (b) that rejects. -/
theorem qExample_far_iff {m : ℕ} (hm : m ≤ 1023) :
    MeetsPolicy (settingsOf Cm.sRef) ⟨25856, 512, 1⟩
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeeth) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) ↔ m ≤ 1 := by
  have tie : MeetsPolicy (settingsOf Cm.sRef) ⟨25856, 512, 1⟩
        (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) iTeeth) [1]
        (List.replicate m 0 ++ List.replicate (1023 - m) 1) ↔
      IsTrueUnder Cm.sRef ⟨25856, 512, 1⟩ iTeeth (xMiss m) :=
    meetsPolicy_iff_xMiss _ ⟨25856, 512, 1⟩ hm
  refine Iff.trans tie ?_
  refine Iff.trans (xMiss_iTeeth_iff ⟨25856, 512, 1⟩ (by decide) (by decide) hm) ?_
  constructor
  · rintro ⟨-, h2⟩
    exact h2
  · intro le
    refine ⟨?_, le⟩
    show m * 25856 + (1023 - m) * 2 ^ 8 ≤ 512 * 1023
    omega

end Policy.Teeth

#print axioms Policy.meetsPolicy_iff_of_cap_one
#print axioms Policy.qExample_eq
#print axioms Policy.qExample_clip
#print axioms Policy.qExample_mean
#print axioms Policy.meetsPolicy_qExample_iff
#print axioms Policy.gaps_of_meetsPolicy_qExample_short
#print axioms Policy.counted_ge_of_meetsPolicy_qExample
#print axioms Policy.card_gap_ge_mul_le_qExample
#print axioms Policy.meetsPolicy_qExample_of_gaps_le
#print axioms Policy.meetsPolicy_qExample_of_one_free
#print axioms Policy.Teeth.getD_mixed
#print axioms Policy.Teeth.built_xMiss
#print axioms Policy.Teeth.meetsPolicy_iff_xMiss
#print axioms Policy.Teeth.meetsPolicy_xMiss_base
#print axioms Policy.Teeth.countedTokens_xMiss
#print axioms Policy.Teeth.outputGap_xMiss
#print axioms Policy.Teeth.qExample_mixed_iff
#print axioms Policy.Teeth.qExample_far_iff
