-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Files/MeetsPolicyAtFiles.lean

The claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean) at what the library's reader of the public
files (`readFiles`, Ladder.lean) returns at the two named sets of files (`storedPublicFiles`, `zGap`,
Ladder/Stored.lean; `NamedFiles`, Ladder.lean). At `storedPublicFiles` the reader returns the policy of exact
match, (C, theta, cap) = (256, 256, 0), and at `zGap` the clipped-gap policy (25856, 512, 1)
(`pol_full`, `pol_gap`, Johnson/Goal/Files/FilesReadAtRef.lean). Theorems with proofs; no
definition; no goal of the library is changed here.

This file states no goal.

Most theorems below are calls of theorems of Policy/Front/ that stand there at the settings of the
reference scales (`settingsOf Cm.sRef`), or at all settings and one fixed policy. Here each is said
of `settingsOfRead pp` and, where it speaks of the files' own policy, of `pp.pol`, for every `pp`
that the reader returns at a named set. The tie is Johnson/Goal/Files/FilesReadAtRef.lean: what the
reader returns at a named set has the settings of the reference scales and the set's policy. Four
theorems are a little more than a call: `exists_output_not_meeting` joins two theorems of
Policy/Front/TeethAllChannels.lean, `exists_outputs_at_budget_gap` and
`exists_outputs_above_clip_gap` join four of Policy/Front/MeetsPolicyAtGap.lean each, and
`clippedGaps_of_meetsPolicy_gap` writes clause (b) in gaps. No new fact on the integer model's
arithmetic is shown. The reader does return a table at each of the two sets (`read_full_ref`,
`read_gap_ref`, FilesReadAtRef.lean), so the premise `read` can be met in each theorem below. That
the other premises can be met together: under the all-zero weights by `meetsPolicy_gap_zeroWeights`
(there every gap is 0 or 1, by reckoning: that theorem tells no gap); for a counted gap of 25,600 or
more (`counted_ge_of_meetsPolicy_gap`, `meetsPolicy_gap_of_one_free`) by
`exists_outputs_above_clip_gap` at m = 1. In this file the premise of `meetsPolicy_gap_of_gaps_le`
is borne by a statement only where all gaps are 0 (`exists_outputs_at_budget_gap` at m = 0): no
statement here tells a gap from 1 to 256. One gap of 1 is told elsewhere, at all valid settings,
under the all-zero weights: `outputCost_zeroWeights_one` (Policy/Front/TrueUnder.lean: token 1 after
the prompt of one token 0 costs 257). None of the theorems below has `InScope` (Ladder.lean) among
its premises. Whoever joins one to a statement on files in scope needs `InScope storedPublicFiles = true` or
`InScope zGap = true`: the fields of `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean)
give both.

Words. An output "has scores": `HasScores`. Clause (c) of `MeetsPolicy`: a token after a full window
is the model's next token. Neither of the two reads the policy. The counted tokens of an output are
those inside the window of 1,024 tokens (`countedTokens`); n is their number. A token's gap is
`outputGap` (Policy/Front/MeetsPolicyBounds.lean).

Why the file lies in this folder: it imports FilesReadAtRef.lean and, through it, Ladder.lean.


Part 1: any policy within stated bounds, not the files' own, at both named sets.
* `settingsOfRead_named`, `valid_named`: what the reader returns at a named set has the settings of
  the reference scales, and these are valid.
* `every_output_at_meets_iff`: at the settings that the reader returns at a named set, for
  1 ≤ n ≤ 1,023, a policy with C < 2^32 and theta ≤ C is met, under all weights, by every output of
  n counted tokens that has scores and meets clause (c), if and only if theta = C and n ≤ cap.
* `every_output_meets_iff`: at the settings that the reader returns at a named set, a policy with
  C < 2^32 and theta ≤ C is met, under all weights, by every output that has scores and meets clause
  (c), if and only if theta = C and 1,023 ≤ cap.
* `every_short_output_meets_iff`: at the settings that the reader returns at a named set, a policy
  with 1 ≤ cap and theta < 9,603,783,936 is met, under all weights, by every output of at most cap
  counted tokens that has scores and meets clause (c), if and only if C ≤ theta.
Part 2: examples under made-up weights, most of them at the files' own policies.
* `exists_output_not_meeting`: at the settings that the reader returns at a named set, for
  1 ≤ n ≤ 1,023 and any policy with theta < C and theta < 9,603,783,936, or with C < 9,603,783,936
  and cap < n, there are weights, a prompt and an output of n counted tokens that has scores and
  meets clause (c) and does not meet the policy. The weights in the proof are made up.
* `exists_output_not_meeting_gap`: at the settings and the policy that the reader returns at `zGap`,
  for every n from 1 to 1,023 there are weights, a prompt and an output of n counted tokens that has
  scores and meets clause (c) and does not meet the policy. The weights in the proof are made up.
* `meetsPolicy_gap_zeroWeights_of_scores`: at the settings and the policy that the reader returns at
  `zGap`, under the all-zero weights, every output that has scores and meets clause (c) meets the
  policy.
* `meetsPolicy_gap_zeroWeights`: at the settings and the policy that the reader returns at `zGap`,
  under the all-zero weights, an output meets the policy if prompt and output are not empty, have at
  most 1,025 tokens together, all in the vocabulary, and a token after a full window is token 0. So
  there are outputs that have scores and meet clause (c) under these weights.
* `exists_outputs_at_budget_gap`: at the settings and the policy that the reader returns at `zGap`,
  there are weights under which, for every m ≤ 1,023, after the prompt of one token 1, the output of
  m tokens 0 and then 1,023 - m tokens 1 has scores, meets clause (c) and has 1,023 counted tokens,
  the first m with the gap 2,047 and the others with the gap 0, and meets the policy if and only if
  m ≤ 127. Clause (c) asks nothing of these outputs: prompt and output have 1,024 tokens together,
  so no token follows a full window. The weights in the proof are made up.
* `exists_outputs_above_clip_gap`: at the settings and the policy that the reader returns at `zGap`,
  there are weights under which, for every m ≤ 1,023, after the prompt of one token 1, the output of
  m tokens 0 and then 1,023 - m tokens 1 has scores, meets clause (c) and has 1,023 counted tokens,
  the first m with the gap 16,766,977 and the others with the gap 0, and meets the policy if and
  only if m ≤ 1. Clause (c) asks nothing of these outputs, as in the theorem before. The weights in
  the proof are made up, and are not those of the theorem before.
* `exists_output_not_meeting_full`: at the settings and the policy that the reader returns at
  `storedPublicFiles`, for every n from 1 to 1,023 there are weights, a prompt and an output of n counted tokens
  that has scores and meets clause (c) and does not meet the policy. The weights in the proof are
  made up.
Part 3: what it is to meet the files' own policy, under any weights.
* `meetsPolicy_gap_iff`: at the settings and the policy that the reader returns at `zGap`, the claim
  written out in gaps.
* `clippedGaps_of_meetsPolicy_gap`: at the settings and the policy that the reader returns at
  `zGap`, if an output meets the policy, its counted tokens' gaps, each clipped at 25,600, sum to at
  most 256 n, and at most one counted token has a gap above 25,600.
* `gaps_of_meetsPolicy_gap_short`: at the settings and the policy that the reader returns at `zGap`,
  if an output of at most 99 counted tokens meets the policy, every counted token's gap is below
  25,600 and these gaps sum to at most 256 n.
* `counted_ge_of_meetsPolicy_gap`: at the settings and the policy that the reader returns at `zGap`,
  if an output meets the policy and one of its counted tokens has a gap of 25,600 or more, it has at
  least 100 counted tokens.
* `card_gap_ge_mul_le_gap`: at the settings and the policy that the reader returns at `zGap`, if an
  output meets the policy, then for g ≤ 25,600 the number of its counted tokens with a gap of g or
  more, times g, is at most 256 n.
* `meetsPolicy_gap_of_gaps_le`: at the settings and the policy that the reader returns at `zGap`, an
  output that has scores and meets clause (c), and all of whose counted tokens have a gap of at most
  256, meets the policy.
* `meetsPolicy_gap_of_one_free`: at the settings and the policy that the reader returns at `zGap`,
  an output that has scores, meets clause (c) and has at least 100 counted tokens meets the policy
  if all its counted tokens but one are the model's next tokens, whatever the one is.
* `meetsPolicy_full_iff`: at the settings and the policy that the reader returns at `storedPublicFiles`, an
  output meets the policy exactly if it is not empty and each of its tokens is the model's next
  token (`ModelOutput`, Ladder.lean, which holds of the empty output too).
Not stated here at what the reader returns, among others: `meetsPolicy_iff_of_cap_one`
(Policy/Front/MeetsPolicyAtGap.lean) and the theorems of Policy/Front/MeetsPolicyBounds.lean,
Policy/Front/MeetsPolicyGuards.lean and Johnson/IMR/MeetsPolicyAtPort.lean, which hold at all
settings and so there too; the ceiling of Policy/Front/MeetsPolicyIdleAtScales.lean, which holds at
all valid settings (at MF = 44 and KF = 30, by reckoning, in an output that has scores no counted
token's gap is above 19,345,962,497); `Teeth.meetsPolicy_iff_xMiss`
(Policy/Front/MeetsPolicyAtGap.lean); `TeethAll.meetsPolicy_replicate_iff` and
`TeethAll.teeth_in_range_meetsPolicy` (Policy/Front/TeethAllChannels.lean).

Limits.
* In the three theorems of part 1 on policies, "under all weights" is part of the left side. They
  name the policies that every output with scores and clause (c) meets whatever the model is. A
  policy that fails the left side rejects some such output under some made-up weights. Under the
  weights at hand it may still be met by every such output.
* The three theorems of part 1 on policies hold at the two named sets. They are not true of all
  files in the goals' scope, if an evaluation is trusted, and by a reading of `settingsOf`. At valid
  settings with MF ≤ KF + 11 there is a policy with 2^8 ≤ theta < C < 2^32 and cap = 0, namely
  (2^32 - 1, 2,436,593,409, 0), that is met, under all weights, by every output that has scores and
  meets clause (c) (`exists_policy_of_close_scales`, Policy/Front/MeetsPolicyIdleAtScales.lean); so
  is every policy with theta and C from 2,436,593,409 on, whatever cap is
  (`meetsPolicy_of_close_scales` there). About smaller theta or C nothing is shown there. Three sets
  of files with MF ≤ KF + 11 evaluate as in scope (Johnson/Goal/Files/ScopeAtNarrowNorm.lean:
  evaluated, not proved). Two of them state exact match; the third states that very policy. The
  reading: that the settings of what the reader returns have the MF and KF that it returns. (That
  they are valid is a theorem: `valid_of_read`, Ladder/Ties.lean.) At the named sets MF = 44 and
  KF = 30, a difference of 14 (`storedLines`, Ladder/Stored.lean; that the reader returns the
  reference's final norm there: `read_full_ref`, `read_gap_ref`). The ceiling on a gap of
  Policy/Front/MeetsPolicyIdleAtScales.lean is below 2^32 only up to a difference of 11, so at the
  named sets that file says nothing about a policy with C < 2^32. For the differences 12 and 13, and
  for 14 at other scales, neither that file nor this one says anything about such a policy.
* Part 2 shows that each of the policies of the two named sets, at the settings that the reader
  returns with it, rejects some output that has scores and meets clause (c), under some weights. It
  does not show that they reject anything at a trained model, at the stored examples' weights, or
  at the weights under any commitment, or how often. All weights of part 2 are made up, with the
  same logits after every context.
* In `exists_output_not_meeting` and its two cases the weights are those of `iTeethAll`
  (Policy/Front/TeethAllChannels.lean), the prompt is the one token 0, and the output is n tokens 0.
  All its counted tokens have one cost, 9,603,783,936, by `TeethAll.cost_xz` (a theorem on the cost
  of the library's relation on a request, not on `outputCost`) and the arithmetic of
  `TeethAll.cost_number`: far above the clips of the two named sets.
* Outputs of which only some tokens are costly: `exists_outputs_at_budget_gap` and
  `exists_outputs_above_clip_gap`, each under made-up weights of its own. Both are for the prompt of
  one token and 1,023 counted tokens alone. 127 is that length's number. 1 is cap: with all other
  gaps 0 it is the number from 100 counted tokens on (`meetsPolicy_gap_of_one_free` and clause (b)),
  and up to 99 the number is 0 (`gaps_of_meetsPolicy_gap_short`). The costly tokens stand first in
  the output. No example meets the budget with equality.
* Under other made-up weights, the all-zero ones, every output that has scores and meets clause (c)
  meets the policy of `zGap`. No theorem here says which weights are at hand: that an output meets
  the policy, said of weights of which one knows only that they exist, says little.
* The unit of a gap is that of the given weights' own integer logits. No definition here reads a
  scale for it: what 256 or 25,600 of these units are worth depends on the weights.
* n counts the tokens of one output, which in a soundness statement the prover picks and may cut. At
  theta = C a reply that is cut into outputs of at most cap counted tokens meets the policy in each,
  whatever its tokens, given scores and clause (c).
* The claim at (25856, 512, 1) does not bound how many counted tokens differ from the model's next
  token: given scores and clause (c), all may, if their gaps are at most 25,600 each and sum to at
  most 256 n. All limits of Policy/Front/MeetsPolicyAtGap.lean hold here.
* The named sets are the bytes written in Ladder/Stored.lean. That they are the bytes of the
  repository's folder examples/ is not said here.
* Nothing here speaks of a protocol, a commitment, a prover, a verifier, soundness or the programs.
  Nothing here compares the claim with the test of the paper that Policy/Front/MeetsPolicy.lean
  names as its source.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Goal.Files.FilesReadAtRef
import Policy.Front.TeethAllChannels
import Policy.Front.MeetsPolicyAtGap

set_option autoImplicit false

/- No default table of scales is available in this file: the instance `Scl.ref`
(Inst/Model/Scl.lean) is switched off, so whatever reads a table says which. -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifierAndGoals.AtFiles

open VerifiableInference Policy Inst.Model

/- The named files stay folded: left to unfold them, Lean compares whole files byte by byte (the
note in Johnson/Goal/Files/FilesReadProof.lean). -/
attribute [local irreducible] storedPublicFiles zGap

/-! ## 1. Any policy within stated bounds, at both named sets -/

/-- Whatever the reader returns at a named set of files has the settings of the reference scales. It
is `settingsOfRead_full` and `settingsOfRead_gap` (Johnson/Goal/Files/FilesReadAtRef.lean) in one.
-/
theorem settingsOfRead_named {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (named : NamedFiles Z)
    (read : readFiles Z = .ok pp) : settingsOfRead pp = settingsOf Cm.sRef := by
  rcases named with rfl | rfl
  · exact settingsOfRead_full read
  · exact settingsOfRead_gap read

/-- The settings that the reader returns at a named set of files are valid. -/
theorem valid_named {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (named : NamedFiles Z)
    (read : readFiles Z = .ok pp) : settingsAreValid (settingsOfRead pp) = true := by
  rw [settingsOfRead_named named read]
  exact settingsAreValid_settingsOf Cm.lawful_sRef

/-- **At the settings that the reader returns at a named set of files, for 1 ≤ n ≤ 1,023, a policy
with C < 2^32 and theta ≤ C is met under all weights by every output of n counted tokens that has
scores and meets clause (c), if and only if theta = C and n ≤ cap.** It is
`TeethAll.every_output_at_meets_iff` (Policy/Front/TeethAllChannels.lean) at these settings. The
policy is any policy, not the files' own. By the docstring of `readFiles` (Ladder.lean), C < 2^32
and theta ≤ C are among what the reader asks of a policy. The left side ranges over all weights. A
policy that fails it rejects some such output under some made-up weights. Under the weights at hand
it may still be met by every such output. Limits: "only if" is shown by one output under made-up
weights. At other files "only if" can fail: at valid settings with MF ≤ KF + 11
(`exists_policy_of_close_scales`, `meetsPolicy_of_close_scales`,
Policy/Front/MeetsPolicyIdleAtScales.lean). That such files are in the goals' scope is evaluated at
three sets of files, not proved: see the limits in this file's head. n counts one output, which in a
soundness statement the prover picks and may cut. -/
theorem every_output_at_meets_iff {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (named : NamedFiles Z)
    (read : readFiles Z = .ok pp) (pol : AcceptancePolicy) (clip : pol.C < 2 ^ 32) (mean : pol.theta ≤ pol.C)
    {n : ℕ} (h0 : 0 < n) (hn : n ≤ 1023) :
    (∀ (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      HasScores (settingsOfRead pp) weights prompt output →
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) →
      countedTokens (settingsOfRead pp) prompt output = n →
      MeetsPolicy (settingsOfRead pp) pol weights prompt output) ↔
      pol.theta = pol.C ∧ n ≤ pol.cap := by
  rw [settingsOfRead_named named read]
  exact Policy.TeethAll.every_output_at_meets_iff pol clip mean h0 hn

/-- **At the settings that the reader returns at a named set of files, a policy with C < 2^32 and
theta ≤ C is met under all weights by every output that has scores and meets clause (c), if and only
if theta = C and 1,023 ≤ cap.** It is `TeethAll.every_output_meets_iff`
(Policy/Front/TeethAllChannels.lean) at these settings. The policy is any policy, not the files'
own; neither of the policies of the two named sets meets the right side. 1,023 is the largest number
of counted tokens of an output that has scores: a prompt has at least one token, and the window has
1,024. The left side ranges over all weights. A policy that fails it rejects some such output under
some made-up weights. Under the weights at hand it may still be met by every such output: the policy
of `zGap` is, under the all-zero weights (`meetsPolicy_gap_zeroWeights_of_scores`). A policy with
theta = C and 1 ≤ cap < 1,023 fails the left side, yet every output of at most cap counted tokens
that has scores and meets clause (c) meets it (`every_short_output_meets_iff`), and in a soundness
statement the prover picks the cut. Limits: "only if" is shown by one output of 1,023 tokens under
made-up weights; it says nothing of a trained model. At other files "only if" can fail: at valid
settings with MF ≤ KF + 11 (`exists_policy_of_close_scales`, `meetsPolicy_of_close_scales`,
Policy/Front/MeetsPolicyIdleAtScales.lean). That such files are in the goals' scope is evaluated at
three sets of files, not proved: see the limits in this file's head. -/
theorem every_output_meets_iff {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (named : NamedFiles Z)
    (read : readFiles Z = .ok pp) (pol : AcceptancePolicy) (clip : pol.C < 2 ^ 32) (mean : pol.theta ≤ pol.C) :
    (∀ (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      HasScores (settingsOfRead pp) weights prompt output →
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) →
      MeetsPolicy (settingsOfRead pp) pol weights prompt output) ↔
      pol.theta = pol.C ∧ 1023 ≤ pol.cap := by
  rw [settingsOfRead_named named read]
  exact Policy.TeethAll.every_output_meets_iff pol clip mean

/-- **At the settings that the reader returns at a named set of files, a policy with 1 ≤ cap and
theta < 9,603,783,936 is met under all weights by every output of at most cap counted tokens that
has scores and meets clause (c), if and only if C ≤ theta.** It is
`TeethAll.every_short_output_meets_iff` (Policy/Front/TeethAllChannels.lean) at these settings. The
policy is any policy, not the files' own. Every policy with theta ≤ C < 2^32 has
theta < 9,603,783,936; for such a policy the right side is theta = C. The left side ranges over all
weights. Under given weights more policies may be met by every such output: under the all-zero
weights the policy of `zGap` is, where C is above theta (`meetsPolicy_gap_zeroWeights_of_scores`).
Limits: "only if" is shown by one output of one token under made-up weights. At other files "only
if" can fail: at valid settings with MF ≤ KF + 11, for example at the policy
(2^32 - 1, 2,436,593,409, 1) (`meetsPolicy_of_close_scales`,
Policy/Front/MeetsPolicyIdleAtScales.lean). That such files are in the goals' scope is evaluated at
three sets of files, not proved: see the limits in this file's head. The number of counted tokens is
that of one output, which in a soundness statement the prover picks and may cut. -/
theorem every_short_output_meets_iff {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (named : NamedFiles Z)
    (read : readFiles Z = .ok pp) (pol : AcceptancePolicy) (limit : 1 ≤ pol.cap)
    (mean : pol.theta < 9603783936) :
    (∀ (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      HasScores (settingsOfRead pp) weights prompt output →
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) →
      countedTokens (settingsOfRead pp) prompt output ≤ pol.cap →
      MeetsPolicy (settingsOfRead pp) pol weights prompt output) ↔
      pol.C ≤ pol.theta := by
  rw [settingsOfRead_named named read]
  exact Policy.TeethAll.every_short_output_meets_iff pol limit mean

/-! ## 2. Examples under made-up weights -/

/-- **At the settings that the reader returns at a named set of files, for 1 ≤ n ≤ 1,023, a policy
with theta < C and theta < 9,603,783,936, or with C < 9,603,783,936 and cap < n, is not met by some
output of n counted tokens that has scores and meets clause (c), under some weights.** The policy is
any such policy, not the files' own. The weights in the proof are made up: those that `iTeethAll`
holds (Policy/Front/TeethAllChannels.lean). The prompt is the one token 0, and the output is n
tokens 0 (`TeethAll.meetsPolicy_replicate_iff`). The statement does not name them. Nothing follows
for other weights: under the weights at hand the policy may be met by every output that has scores
and meets clause (c). -/
theorem exists_output_not_meeting {Z : VerifierAndGoals.PublicFiles} {pp : ScalesAndPolicy} (named : NamedFiles Z)
    (read : readFiles Z = .ok pp) (pol : AcceptancePolicy) {n : ℕ} (h0 : 0 < n) (hn : n ≤ 1023)
    (numbers : (pol.theta < pol.C ∧ pol.theta < 9603783936) ∨
      (pol.C < 9603783936 ∧ pol.cap < n)) :
    ∃ (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      HasScores (settingsOfRead pp) weights prompt output ∧
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) ∧
      countedTokens (settingsOfRead pp) prompt output = n ∧
      ¬ MeetsPolicy (settingsOfRead pp) pol weights prompt output := by
  rw [settingsOfRead_named named read]
  obtain ⟨base, counted⟩ := Policy.TeethAll.replicate_facts h0 hn
  refine ⟨_, _, _, base.toHasScores, base.afterFullWindow, counted, fun meets => ?_⟩
  obtain ⟨a, b⟩ := (Policy.TeethAll.meetsPolicy_replicate_iff pol h0 hn).1 meets
  rcases numbers with ⟨n1, n2⟩ | ⟨n1, n2⟩
  · rcases min_le_iff.1 a with a | a
    · have : 9603783936 ≤ pol.theta := by exact_mod_cast a
      omega
    · have : pol.C ≤ pol.theta := by exact_mod_cast a
      omega
  · have small : (pol.C : ℤ) < 9603783936 := by exact_mod_cast n1
    have := b small
    omega

/-- **At the settings and the policy that the reader returns at `zGap`, for every n from 1 to 1,023,
under some weights some output of n counted tokens that has scores and meets clause (c) does not
meet the policy.** The policy is (25856, 512, 1). So it fails the left side of
`every_output_meets_iff`. The weights in the proof are made up, and all counted tokens of the output
have one cost, far above the clip (`exists_output_not_meeting`; the limits in this file's head).
Outputs of which only some tokens are costly: `exists_outputs_at_budget_gap`,
`exists_outputs_above_clip_gap`. Nothing follows for a trained model, for the stored examples'
weights or for the weights under any commitment, and under the all-zero weights every output that
has scores and meets clause (c) meets this policy (`meetsPolicy_gap_zeroWeights_of_scores`). -/
theorem exists_output_not_meeting_gap {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp) {n : ℕ}
    (h0 : 0 < n) (hn : n ≤ 1023) :
    ∃ (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      HasScores (settingsOfRead pp) weights prompt output ∧
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) ∧
      countedTokens (settingsOfRead pp) prompt output = n ∧
      ¬ MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output := by
  rw [pol_gap read]
  exact exists_output_not_meeting (Or.inr rfl) read ⟨25856, 512, 1⟩ h0 hn
    (Or.inl ⟨by norm_num, by norm_num⟩)

/-- **At the settings and the policy that the reader returns at `zGap`, under the all-zero weights,
every output that has scores and meets clause (c) meets the policy.** The policy is (25856, 512, 1).
It is `meetsPolicy_zeroWeights_of_scores` (Policy/Front/TeethAllChannels.lean) at 257 ≤ 512 and
257 ≤ 25,856. That there are such outputs: `meetsPolicy_gap_zeroWeights`. So that an output meets
the files' policy, said of weights of which one knows only that they exist, says little. -/
theorem meetsPolicy_gap_zeroWeights_of_scores {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {prompt output : List Token}
    (scores : HasScores (settingsOfRead pp) (zeroWeights (valid_named (Or.inr rfl) read)) prompt
      output)
    (after : ∀ position (h : position < output.length),
      (settingsOfRead pp).positions ≤ prompt.length + position →
        modelNextToken (settingsOfRead pp) (zeroWeights (valid_named (Or.inr rfl) read))
          (prompt ++ output.take position) = some output[position]) :
    MeetsPolicy (settingsOfRead pp) pp.pol (zeroWeights (valid_named (Or.inr rfl) read)) prompt
      output := by
  rw [pol_gap read]
  exact meetsPolicy_zeroWeights_of_scores _ (by norm_num) (by norm_num) scores after

/-- **At the settings and the policy that the reader returns at `zGap`, under the all-zero weights,
an output meets the policy if prompt and output are not empty, have at most 1,025 tokens together,
all in the vocabulary, and a token that follows a full window is token 0.** None of these conditions
reads a score. It is `meetsPolicy_zeroWeights` (Policy/Front/TrueUnder.lean) at 257 ≤ 512 and
257 ≤ 25,856. -/
theorem meetsPolicy_gap_zeroWeights {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {prompt output : List Token} (promptNonempty : prompt ≠ []) (outputNonempty : output ≠ [])
    (length_le : prompt.length + output.length ≤ (settingsOfRead pp).positions + 1)
    (inVocabulary : ∀ token ∈ prompt ++ output, token < (settingsOfRead pp).vocabulary)
    (last : ∀ position (h : position < output.length),
      (settingsOfRead pp).positions ≤ prompt.length + position → output[position] = 0) :
    MeetsPolicy (settingsOfRead pp) pp.pol (zeroWeights (valid_named (Or.inr rfl) read)) prompt
      output := by
  rw [pol_gap read]
  exact meetsPolicy_zeroWeights _ (by norm_num) (by norm_num) promptNonempty outputNonempty
    length_le inVocabulary last

/-- **At the settings and the policy that the reader returns at `zGap`, there are weights under
which, for every m ≤ 1,023, after the prompt of one token 1, the output of m tokens 0 and then
1,023 - m tokens 1 has scores, meets clause (c) and has 1,023 counted tokens, of which the first m
have the gap 2,047 and the others the gap 0; and it meets the policy if and only if m ≤ 127.**
Clause (c) asks nothing of these outputs: prompt and output have 1,024 tokens together, so no token
follows a full window. The outputs with m ≥ 128 are rejected by clause (a) or (b), not for want of
scores. No gap is above the clip of 25,600, so it is clause (a):
2,047 · 127 = 259,969 ≤ 256 · 1,023 = 261,888 < 262,016 = 2,047 · 128 (the gaps' sum at m = 127, the
budget, the sum at m = 128). The budget is used up to within one token's gap, and not with equality.
127 is the number for 1,023 counted tokens alone. The weights in the proof are made up
(`idxAB AtChosen.votes_one`: `idxAB`, Policy/Rel/Teeth.lean; `votes_one`, Policy/Rel/AtChosen.lean;
other weights than in `exists_outputs_above_clip_gap`), with the same logits after every context.
The costly tokens stand first in the output. It joins `Teeth.qExample_mixed_iff`,
`Teeth.meetsPolicy_xMiss_base`, `Teeth.countedTokens_xMiss` and `Teeth.outputGap_xMiss`
(Policy/Front/MeetsPolicyAtGap.lean). Nothing follows for other weights. -/
theorem exists_outputs_at_budget_gap {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp) :
    ∃ weights : ModelWeights (settingsOfRead pp), ∀ m ≤ 1023, ∀ prompt output : List Token,
      prompt = [1] → output = List.replicate m 0 ++ List.replicate (1023 - m) 1 →
      HasScores (settingsOfRead pp) weights prompt output ∧
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) ∧
      countedTokens (settingsOfRead pp) prompt output = 1023 ∧
      (∀ position < 1023, outputGap (settingsOfRead pp) weights prompt output position =
        if position < m then 2047 else 0) ∧
      (MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output ↔ m ≤ 127) := by
  rw [settingsOfRead_gap read, pol_gap read]
  refine ⟨weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef)
    (Policy.Teeth.idxAB AtChosen.votes_one), ?_⟩
  rintro m hm prompt output rfl rfl
  have base : MeetsPolicy (settingsOf Cm.sRef) ⟨256, 256, 1023⟩
      (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef)
        (Policy.Teeth.idxAB AtChosen.votes_one)) [1]
      (List.replicate m 0 ++ List.replicate (1023 - m) 1) :=
    Policy.Teeth.meetsPolicy_xMiss_base AtChosen.votes_one (by norm_num) hm
  refine ⟨base.toHasScores, base.afterFullWindow, Policy.Teeth.countedTokens_xMiss hm,
    fun position lt => ?_, Policy.Teeth.qExample_mixed_iff hm⟩
  have gap : outputGap (settingsOf Cm.sRef)
      (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef)
        (Policy.Teeth.idxAB AtChosen.votes_one)) [1]
      (List.replicate m 0 ++ List.replicate (1023 - m) 1) position =
      if position < m then 2047 * (1 + 0) else 0 :=
    Policy.Teeth.outputGap_xMiss AtChosen.votes_one (by norm_num) hm lt
  rw [gap]
  norm_num

/-- **At the settings and the policy that the reader returns at `zGap`, there are weights under
which, for every m ≤ 1,023, after the prompt of one token 1, the output of m tokens 0 and then
1,023 - m tokens 1 has scores, meets clause (c) and has 1,023 counted tokens, of which the first m
have the gap 16,766,977 and the others the gap 0; and it meets the policy if and only if m ≤ 1.**
Clause (c) asks nothing of these outputs: prompt and output have 1,024 tokens together, so no token
follows a full window. The outputs with m ≥ 2 are rejected by clause (a) or (b), not for want of
scores. At m = 2 the clipped gaps sum to 51,200 ≤ 261,888, so it is clause (b): one token above the
clip of 25,600 passes, and two do not. From m = 11 on clause (a) fails too
(11 · 25,600 = 281,600 > 261,888). At m = 1 the output meets the policy with a counted gap far above
the clip, and all its other counted tokens have the gap 0: so the premises of
`counted_ge_of_meetsPolicy_gap` can be met together, and, with `outputGap_eq_zero_iff`
(Policy/Front/MeetsPolicyBounds.lean), those of `meetsPolicy_gap_of_one_free` with a token above the
clip. The weights in the proof are made up (`iTeeth`, Policy/Rel/Teeth.lean; other weights than in
`exists_outputs_at_budget_gap`), with the same logits after every context. The costly tokens stand
first in the output. It joins `Teeth.qExample_far_iff`, `Teeth.meetsPolicy_xMiss_base`,
`Teeth.countedTokens_xMiss` and `Teeth.outputGap_xMiss` (Policy/Front/MeetsPolicyAtGap.lean).
Nothing follows for other weights. -/
theorem exists_outputs_above_clip_gap {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp) :
    ∃ weights : ModelWeights (settingsOfRead pp), ∀ m ≤ 1023, ∀ prompt output : List Token,
      prompt = [1] → output = List.replicate m 0 ++ List.replicate (1023 - m) 1 →
      HasScores (settingsOfRead pp) weights prompt output ∧
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) ∧
      countedTokens (settingsOfRead pp) prompt output = 1023 ∧
      (∀ position < 1023, outputGap (settingsOfRead pp) weights prompt output position =
        if position < m then 16766977 else 0) ∧
      (MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output ↔ m ≤ 1) := by
  rw [settingsOfRead_gap read, pol_gap read]
  refine ⟨weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) Policy.Teeth.iTeeth, ?_⟩
  rintro m hm prompt output rfl rfl
  have base : MeetsPolicy (settingsOf Cm.sRef) ⟨256, 256, 1023⟩
      (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) Policy.Teeth.iTeeth) [1]
      (List.replicate m 0 ++ List.replicate (1023 - m) 1) :=
    Policy.Teeth.meetsPolicy_xMiss_base (a := 4095) (b := 4096) _ (by norm_num) hm
  refine ⟨base.toHasScores, base.afterFullWindow, Policy.Teeth.countedTokens_xMiss hm,
    fun position lt => ?_, Policy.Teeth.qExample_far_iff hm⟩
  have gap : outputGap (settingsOf Cm.sRef)
      (weightsOfIndex (settingsAreValid_settingsOf Cm.lawful_sRef) Policy.Teeth.iTeeth) [1]
      (List.replicate m 0 ++ List.replicate (1023 - m) 1) position =
      if position < m then 2047 * (4095 + 4096) else 0 :=
    Policy.Teeth.outputGap_xMiss (a := 4095) (b := 4096) _ (by norm_num) hm lt
  rw [gap]
  norm_num

/-- **At the settings and the policy that the reader returns at `storedPublicFiles`, for every n from 1 to
1,023, under some weights some output of n counted tokens that has scores and meets clause (c) does
not meet the policy.** The policy is exact match, (256, 256, 0). Here theta = C, and the proof uses
cap < n. The weights in the proof are made up (`exists_output_not_meeting`). It says little: by
`meetsPolicy_full_iff`, under any weights an output with a token that is not the model's next token
does not meet exact match. -/
theorem exists_output_not_meeting_full {pp : ScalesAndPolicy} (read : readFiles storedPublicFiles = .ok pp) {n : ℕ}
    (h0 : 0 < n) (hn : n ≤ 1023) :
    ∃ (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token),
      HasScores (settingsOfRead pp) weights prompt output ∧
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) ∧
      countedTokens (settingsOfRead pp) prompt output = n ∧
      ¬ MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output := by
  rw [pol_full read]
  refine exists_output_not_meeting (Or.inl rfl) read AcceptancePolicy.exact h0 hn (Or.inr ⟨?_, h0⟩)
  show (2 : ℕ) ^ 8 < 9603783936
  norm_num

/-! ## 3. What it is to meet the files' own policy, under any weights -/

/-- **To meet the policy that the reader returns at `zGap`, written out.** At the settings and the
policy that the reader returns at `zGap`, under any weights, an output meets the policy exactly if
it has scores and meets clause (c), and one of two: every counted token has a gap of at most 25,600,
and the gaps sum to at most 256 n; or there is one counted position `free` such that every other
counted token has a gap of at most 25,600, and the others' gaps with 25,600 sum to at most 256 n. Of
the gap of the token at `free` nothing is asked. It is `meetsPolicy_qExample_iff`
(Policy/Front/MeetsPolicyAtGap.lean), whose limits hold here. The claim does not bound how many
counted tokens differ from the model's next token. The unit of a gap is that of the given weights'
integer logits. n counts the tokens of this one output, which in a soundness statement the prover
picks and may cut. -/
theorem meetsPolicy_gap_iff {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token) :
    MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output ↔
      HasScores (settingsOfRead pp) weights prompt output ∧
      (∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position]) ∧
      (((∀ position < countedTokens (settingsOfRead pp) prompt output,
            outputGap (settingsOfRead pp) weights prompt output position ≤ 25600) ∧
          ∑ position ∈ Finset.range (countedTokens (settingsOfRead pp) prompt output),
              outputGap (settingsOfRead pp) weights prompt output position ≤
            (countedTokens (settingsOfRead pp) prompt output : ℤ) * 256) ∨
        ∃ free < countedTokens (settingsOfRead pp) prompt output,
          (∀ position < countedTokens (settingsOfRead pp) prompt output, position ≠ free →
            outputGap (settingsOfRead pp) weights prompt output position ≤ 25600) ∧
          ∑ position ∈
                (Finset.range (countedTokens (settingsOfRead pp) prompt output)).erase free,
              outputGap (settingsOfRead pp) weights prompt output position + 25600 ≤
            (countedTokens (settingsOfRead pp) prompt output : ℤ) * 256) := by
  rw [pol_gap read]
  exact meetsPolicy_qExample_iff weights prompt output

/-- **At the settings and the policy that the reader returns at `zGap`, under any weights: if an
output meets the policy, the gaps of its counted tokens, each clipped at 25,600, sum to at most 256
n, and at most one counted token has a gap above 25,600.** These are clauses (a) and (b) of
`MeetsPolicy` in gaps (`MeetsPolicy.sum_clippedGap_le`, Policy/Front/MeetsPolicyBounds.lean, and the
clause `aboveClip`). With scores and clause (c) they are the whole claim (by reckoning;
`meanClause_iff_gap`, Policy/Front/MeetsPolicyBounds.lean, is the step for (a)); only this direction
is stated here. A token above the clip enters the sum as 25,600, whatever its gap. The unit of a gap
is that of the given weights' integer logits. n counts the tokens of this one output, which in a
soundness statement the prover picks and may cut. -/
theorem clippedGaps_of_meetsPolicy_gap {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {weights : ModelWeights (settingsOfRead pp)} {prompt output : List Token}
    (h : MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output) :
    ∑ position ∈ Finset.range (countedTokens (settingsOfRead pp) prompt output),
        min (outputGap (settingsOfRead pp) weights prompt output position) 25600
      ≤ 256 * (countedTokens (settingsOfRead pp) prompt output : ℤ) ∧
    ((Finset.range (countedTokens (settingsOfRead pp) prompt output)).filter fun position =>
        25600 < outputGap (settingsOfRead pp) weights prompt output position).card ≤ 1 := by
  rw [pol_gap read] at h
  have same : ((Finset.range (countedTokens (settingsOfRead pp) prompt output)).filter
        fun position => ((⟨25856, 512, 1⟩ : AcceptancePolicy).C : ℤ) <
          outputCost (settingsOfRead pp) weights prompt output position) =
      (Finset.range (countedTokens (settingsOfRead pp) prompt output)).filter
        fun position => ((⟨25856, 512, 1⟩ : AcceptancePolicy).C : ℤ) - 2 ^ 8 <
          outputGap (settingsOfRead pp) weights prompt output position :=
    Finset.filter_congr fun j _ => by
      rw [outputCost_eq_outputGap_add]
      constructor <;> intro lt <;> linarith
  have a := h.sum_clippedGap_le
  have b : ((Finset.range (countedTokens (settingsOfRead pp) prompt output)).filter
        fun position => ((⟨25856, 512, 1⟩ : AcceptancePolicy).C : ℤ) - 2 ^ 8 <
          outputGap (settingsOfRead pp) weights prompt output position).card ≤
      (⟨25856, 512, 1⟩ : AcceptancePolicy).cap := by
    rw [← same]
    exact h.aboveClip
  rw [qExample_clip, qExample_mean] at a
  rw [qExample_clip] at b
  exact ⟨a, b⟩

/-- **At the settings and the policy that the reader returns at `zGap`, under any weights: if an
output with at most 99 counted tokens meets the policy, every counted token's gap is below 25,600,
and these gaps, unclipped, sum to at most 256 n.** It is `gaps_of_meetsPolicy_qExample_short`
(Policy/Front/MeetsPolicyAtGap.lean). The unit of a gap is that of the given weights' integer
logits. The counted tokens are those of this one output, which in a soundness statement the prover
picks and may cut. -/
theorem gaps_of_meetsPolicy_gap_short {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {weights : ModelWeights (settingsOfRead pp)} {prompt output : List Token}
    (h : MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output)
    (short : countedTokens (settingsOfRead pp) prompt output ≤ 99) :
    (∀ position < countedTokens (settingsOfRead pp) prompt output,
        outputGap (settingsOfRead pp) weights prompt output position < 25600) ∧
      ∑ position ∈ Finset.range (countedTokens (settingsOfRead pp) prompt output),
          outputGap (settingsOfRead pp) weights prompt output position
        ≤ 256 * (countedTokens (settingsOfRead pp) prompt output : ℤ) := by
  rw [pol_gap read] at h
  exact gaps_of_meetsPolicy_qExample_short h short

/-- **At the settings and the policy that the reader returns at `zGap`, under any weights: if an
output meets the policy and one of its counted tokens has a gap of 25,600 or more, it has at least
100 counted tokens.** It is `counted_ge_of_meetsPolicy_qExample`
(Policy/Front/MeetsPolicyAtGap.lean). That its premises can be met together:
`exists_outputs_above_clip_gap` at m = 1. The unit of a gap is that of the given weights' integer
logits. The counted tokens are those of this one output, which in a soundness statement the prover
picks and may cut. -/
theorem counted_ge_of_meetsPolicy_gap {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {weights : ModelWeights (settingsOfRead pp)} {prompt output : List Token}
    (h : MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output) {position : ℕ}
    (counted : position < countedTokens (settingsOfRead pp) prompt output)
    (large : 25600 ≤ outputGap (settingsOfRead pp) weights prompt output position) :
    100 ≤ countedTokens (settingsOfRead pp) prompt output := by
  rw [pol_gap read] at h
  exact counted_ge_of_meetsPolicy_qExample h counted large

/-- **At the settings and the policy that the reader returns at `zGap`, under any weights: if an
output meets the policy, then for every number g ≤ 25,600 the number of its counted tokens with a
gap of g or more, times g, is at most 256 n.** So of n counted tokens at most 256 n / g have a gap
of g or more, for 0 < g ≤ 25,600. For g ≤ 256 it says nothing. It is `card_gap_ge_mul_le_qExample`
(Policy/Front/MeetsPolicyAtGap.lean). The unit of a gap is that of the given weights' integer
logits. The count grows with n, the number of counted tokens of this one output, which in a
soundness statement the prover picks and may cut. -/
theorem card_gap_ge_mul_le_gap {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {weights : ModelWeights (settingsOfRead pp)} {prompt output : List Token}
    (h : MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output) {g : ℤ}
    (clip : g ≤ 25600) :
    (((Finset.range (countedTokens (settingsOfRead pp) prompt output)).filter fun position =>
        g ≤ outputGap (settingsOfRead pp) weights prompt output position).card : ℤ) * g ≤
      (countedTokens (settingsOfRead pp) prompt output : ℤ) * 256 := by
  rw [pol_gap read] at h
  exact card_gap_ge_mul_le_qExample h clip

/-- **At the settings and the policy that the reader returns at `zGap`, under any weights: an output
that has scores and meets clause (c), and all of whose counted tokens have a gap of at most 256,
meets the policy.** So no counted token need be the model's next token, where the weights offer
other tokens within 256. It is `meetsPolicy_qExample_of_gaps_le`
(Policy/Front/MeetsPolicyAtGap.lean). The unit of a gap is that of the given weights' integer
logits. The counted tokens are those of this one output, which in a soundness statement the prover
picks and may cut. -/
theorem meetsPolicy_gap_of_gaps_le {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {weights : ModelWeights (settingsOfRead pp)} {prompt output : List Token}
    (scores : HasScores (settingsOfRead pp) weights prompt output)
    (after : ∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position])
    (le : ∀ position < countedTokens (settingsOfRead pp) prompt output,
      outputGap (settingsOfRead pp) weights prompt output position ≤ 256) :
    MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output := by
  rw [pol_gap read]
  exact meetsPolicy_qExample_of_gaps_le scores after le

/-- **At the settings and the policy that the reader returns at `zGap`, under any weights: an output
that has scores, meets clause (c) and has at least 100 counted tokens meets the policy if every
counted token but one is the model's next token, whatever the gap of that one.** The one stands at
the position `free`. `HasScores` still asks that it is a token of the vocabulary and that the model
has a value on its context, and it is part of the later tokens' contexts. It is
`meetsPolicy_qExample_of_one_free` (Policy/Front/MeetsPolicyAtGap.lean). That the one can lie above
the clip: `exists_outputs_above_clip_gap` at m = 1, under made-up weights. -/
theorem meetsPolicy_gap_of_one_free {pp : ScalesAndPolicy} (read : readFiles zGap = .ok pp)
    {weights : ModelWeights (settingsOfRead pp)} {prompt output : List Token}
    (scores : HasScores (settingsOfRead pp) weights prompt output)
    (after : ∀ position (h : position < output.length),
        (settingsOfRead pp).positions ≤ prompt.length + position →
          modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
            some output[position])
    (long : 100 ≤ countedTokens (settingsOfRead pp) prompt output) (free : ℕ)
    (others : ∀ position (h : position < output.length),
      position < countedTokens (settingsOfRead pp) prompt output → position ≠ free →
        modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
          some output[position]) :
    MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output := by
  rw [pol_gap read]
  exact meetsPolicy_qExample_of_one_free scores after long free others

/-- **At the settings and the policy that the reader returns at `storedPublicFiles`, under any weights: an
output meets the policy exactly if it is not empty and each of its tokens is the model's next token
after the prompt and the output tokens before it.** The policy is exact match, (256, 256, 0). The
second half is written by the goals' own name for it, `ModelOutput` (Ladder.lean), which holds of
the empty output too; the claim does not. It is `meetsPolicy_exact_iff`
(Policy/Front/MeetsPolicyGuards.lean). -/
theorem meetsPolicy_full_iff {pp : ScalesAndPolicy} (read : readFiles storedPublicFiles = .ok pp)
    (weights : ModelWeights (settingsOfRead pp)) (prompt output : List Token) :
    MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output ↔
      output ≠ [] ∧ VerifierAndGoals.ModelOutput (settingsOfRead pp) weights prompt output := by
  rw [pol_full read]
  exact meetsPolicy_exact_iff weights prompt output

end VerifierAndGoals.AtFiles

#print axioms VerifierAndGoals.AtFiles.settingsOfRead_named
#print axioms VerifierAndGoals.AtFiles.valid_named
#print axioms VerifierAndGoals.AtFiles.every_output_at_meets_iff
#print axioms VerifierAndGoals.AtFiles.every_output_meets_iff
#print axioms VerifierAndGoals.AtFiles.every_short_output_meets_iff
#print axioms VerifierAndGoals.AtFiles.exists_output_not_meeting
#print axioms VerifierAndGoals.AtFiles.exists_output_not_meeting_gap
#print axioms VerifierAndGoals.AtFiles.meetsPolicy_gap_zeroWeights_of_scores
#print axioms VerifierAndGoals.AtFiles.meetsPolicy_gap_zeroWeights
#print axioms VerifierAndGoals.AtFiles.exists_outputs_at_budget_gap
#print axioms VerifierAndGoals.AtFiles.exists_outputs_above_clip_gap
#print axioms VerifierAndGoals.AtFiles.exists_output_not_meeting_full
#print axioms VerifierAndGoals.AtFiles.meetsPolicy_gap_iff
#print axioms VerifierAndGoals.AtFiles.clippedGaps_of_meetsPolicy_gap
#print axioms VerifierAndGoals.AtFiles.gaps_of_meetsPolicy_gap_short
#print axioms VerifierAndGoals.AtFiles.counted_ge_of_meetsPolicy_gap
#print axioms VerifierAndGoals.AtFiles.card_gap_ge_mul_le_gap
#print axioms VerifierAndGoals.AtFiles.meetsPolicy_gap_of_gaps_le
#print axioms VerifierAndGoals.AtFiles.meetsPolicy_gap_of_one_free
#print axioms VerifierAndGoals.AtFiles.meetsPolicy_full_iff
