-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Front/MeetsPolicy.lean

`MeetsPolicy`: what it means that output tokens meet an acceptance policy under the scores (the
integer logits) of given weights. Definitions only, over the model function of
IntegerModel/Model.lean. It is a claim for a soundness statement (`SoundForWith`,
VerifiableInference/MoreStatements.lean), where `sound_of_verify_at`
(Johnson/Goal/Skeleton/SoundOfVerifyAt.lean) has "every output token is the
model's next token".
Source: the clipped margin of Token-DiFR at temperature 0: A. Karvonen, D. Reuter, R. Rinberg,
L. Marks, A. Garriga-Alonso, K. Warr, "DiFR: Inference Verification Despite Nondeterminism",
arXiv 2511.20621, sections 4.2 and 7.2, appendix D.
Theorems that are named without a file: Policy/Front/MeetsPolicyGuards.lean. The tie to the
library's relation on a request: Policy/Front/TrueUnder.lean, Policy/Front/TrueUnderConverse.lean.

Limits: The claim says how one output scores under the given weights. It does not say that these are
a sensible model, that the policy has content, or that the output passes the paper's test: see the
docstrings of `logitGap` (whose unit a gap has), `tokenCost` (the constant 2^8) and `MeetsPolicy`.
Nothing in this file ties the policy to a commitment, or says which system is sound for the claim.
The soundness theorem for it is `soundUnderPolicy_of_verify_at`
(Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean), at each set of public files in scope, with that
file's limits. Beside them: a token's cost is its logit gap + 2^8: the exponent 8 is fixed, and 7,
which this library's port of the programs' verifier admits (`policy`,
OnBytes/Model/HeadLayout.lean), is not covered (`tokenCost`); the extractor sees the public files,
the settings, the commitment and the committer's logged queries, and nothing else (`extractor`,
Ladder.lean); `PolCond` (Policy/Rel/True.lean), wider than the programs' `PolTests`, is no
hypothesis of it: it speaks at the policy of each set of files in scope (`InScope`, Ladder.lean).
-/
import VerifiableInference.ModelWeights
import VerifiableInference.Statements
import Inst.Model.ProgramR
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

namespace Policy

open VerifiableInference

/-! ## 1. Logits, gap, cost -/

/-- The model's logits after `tokens`: the row of `IntegerTransformer.trace`'s field `logits` at the
last position, one whole number for each token of the vocabulary; no sampling noise is added. Where
`modelNextToken` has a value, it is the first arg-max of this row (`modelNextToken_eq_firstArgmax`).
Like `trace` this function tests nothing. -/
def modelLogits (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (tokens : List Token) : IntegerTransformer.IntegerVector :=
  (IntegerTransformer.trace settings lookupTables weights.val tokens.toArray).logits.entry
    (tokens.length - 1)

/-- The gap of `token` under `logits`: the largest, over all tokens `other` of the vocabulary, of
logits[other] − logits[token], plus 1 where `other` is the smaller token (`maxUpTo` includes its
last index, vocabulary − 1). For a token of the vocabulary it is at least 0, and 0 exactly at the
first choice, the least token of largest logit (`logitGap_nonneg`, `logitGap_eq_zero_iff`); at every
other token it is how far the token's logit lies below the first choice's, and 1 more if the first
choice is the smaller token (`logitGap_eq_choice`). Outside the vocabulary a read gives the logit 0.
Limit: a gap has the unit of the logits. In `MeetsPolicy` these are the given weights' own, and
whoever makes the weights sets their scale: under weights whose logits barely differ every gap is
small, so the same policy is strict for one model and loose for another. -/
def logitGap (vocabulary : Nat) (logits : IntegerTransformer.IntegerVector) (token : Token) : Int :=
  IntegerTransformer.maxUpTo
    (fun other => logits.entry other - logits.entry token + if other < token then 1 else 0)
    (vocabulary - 1)

/-- The cost of `token` after `context`: its gap under the model's logits after `context`, plus 2^8.
The constant is that of `Inst.Model.costOf`; why a cost has an offset: the head of
Inst/Model/ProgramR.lean. This library's port of the programs' verifier admits the exponents 7 and 8
(`policy`, OnBytes/Model/HeadLayout.lean); this definition has the exponent 8 alone. -/
def tokenCost (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (context : List Token) (token : Token) : Int :=
  logitGap settings.vocabulary (modelLogits settings weights context) token + 2 ^ 8

/-- The cost of the output token at `position` (counted from 0), after the prompt and the output
tokens before it, whatever the model would have chosen there. For a token of the vocabulary it is at
least 2^8 (`outputCost_ge`). Beyond the output's end it reads token 0; `MeetsPolicy` reads it only
below `countedTokens`, which is at most the output's length. -/
def outputCost (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Token) (position : Nat) : Int :=
  tokenCost settings weights (prompt ++ output.take position) (output.getD position 0)

/-! ## 2. Which output tokens are counted -/

/-- The number of counted output tokens: those inside the window of `settings.positions` tokens
(1,024 at valid settings: `settingsAreValid`, VerifiableInference/ModelWeights.lean). They are the
output tokens at the positions 0 .. `countedTokens` − 1. With at most 1,024 tokens in prompt and
output together all output tokens are counted; with 1,025 all but the last; after a prompt of 1,024
tokens none. -/
def countedTokens (settings : IntegerTransformer.Settings) (prompt output : List Token) : Nat :=
  min output.length (settings.positions - prompt.length)

/-! ## 3. The claim -/

/-- The model has scores for the output: neither the prompt nor the output is empty
(`promptNonempty`, `outputNonempty`); they have at most 1,025 tokens together (`length_le`); every
token is in the vocabulary (`inVocabulary`); and the model has a value on the context of every
output token, that is, on the prompt followed by the output tokens before it: no range condition of
the integer program fails on it (`defined`). Nothing is asked beyond the last output token's
context. `outputNonempty`, `defined` and `inVocabulary` for the output give the other clauses
(`hasScores_iff`); these are written out for the reader. -/
structure HasScores (settings : IntegerTransformer.Settings) (weights : ModelWeights settings)
    (prompt output : List Token) : Prop where
  promptNonempty : prompt ≠ []
  outputNonempty : output ≠ []
  length_le : prompt.length + output.length ≤ settings.positions + 1
  inVocabulary : ∀ token ∈ prompt ++ output, token < settings.vocabulary
  defined : ∀ position < output.length,
    (modelNextToken settings weights (prompt ++ output.take position)).isSome = true

/-- **The output meets the policy under the weights' scores.** The policy is three numbers: the clip
C, the bound theta on the mean cost, the limit cap. The model has scores for the output
(`HasScores`), and:
(a) `meanCost`: the costs of the counted output tokens, each clipped at C, sum to at most theta
    times their number;
(b) `aboveClip`: at most cap of the counted output tokens cost more than C;
(c) `afterFullWindow`: an output token that follows a full window (the 1,025th token of prompt and
    output together) is the model's next token, whatever the policy. The library's relation on a
    request has no cost for it.
Every output token is either counted or under (c): the two conditions on its position are each
other's negation. After a prompt of 1,024 tokens none is counted, and only (c) binds
(`meetsPolicy_iff_of_fullPrompt`).
What the claim gives. A counted token above the clip enters (a) as C and (b) as one, whatever its
cost: up to cap counted tokens may be any tokens of the vocabulary, where the others' costs leave
room in (a). Up to the clip: for 2^8 < c ≤ C, of n counted tokens at most
n (theta − 2^8) / (c − 2^8) cost c or more (`few_costly_of_meetsPolicy`); so the gap of a counted
token that is not above the clip is at most n (theta − 2^8), and at most C − 2^8. With cap = 0 no
counted token is above the clip (`outputCost_le_clip_of_cap_zero`).
What meets it: the model's own output, if it is not empty and 2^8 ≤ theta, 2^8 ≤ C
(`meetsPolicy_of_isModelOutput`); and, given scores and (c), outputs in which cheap tokens leave
room for costly ones (`meetsPolicy_of_few_costly`): at C = 2^8 + 1000, theta = 2^8 + 10, cap = 10,
one counted token in a hundred, and at most ten, may be any token of the vocabulary if the others
are first choices.
At the policy of exact match (`Inst.Model.AcceptancePolicy.exact`: C = theta = 2^8, cap = 0) the claim is: the
output is not empty, and every output token is the model's next token (`meetsPolicy_exact_iff`).
Limits. The claim bounds a mean and a count over one output, which in a soundness statement the
prover picks. Unless cap = 0 it is in general no bound on each token. The prompt's tokens are not
scored: a reply that is cut into several outputs has a mean and a count in each, and what is scored
in one is unscored prompt in the next. No condition on the three numbers is part of the claim. With
C ≤ theta clause (a) says nothing, since a clipped cost is at most C: at every policy with
C = theta, exact match among them, only (b) and (c) bind; if cap is also at least the number of
counted tokens, (b) says nothing either (`meetsPolicy_iff_of_clip_le_mean`). The weights need not
be a sensible model: at valid settings, under the all-zero weights, every output meets every policy
with 257 ≤ theta and 257 ≤ C, whatever cap is, if prompt and output are not empty and have at most
1,025 tokens together, all in the vocabulary, and a token after a full window is token 0
(`meetsPolicy_zeroWeights`, Policy/Front/TrueUnder.lean); the same goes for any weights under which
the model has values and the logits of each row are equal (an argument; no theorem). Clause (a) has
the form of Token-DiFR's test (the source named in this file's head), and (b) and (c) have no
counterpart there; to meet (a) is not to pass that test: there the checker runs a model it knows,
pools many outputs' tokens and fits the clip (in the paper's section 4.1 the bound too) to honest
runs. -/
structure MeetsPolicy (settings : IntegerTransformer.Settings) (policy : Inst.Model.AcceptancePolicy)
    (weights : ModelWeights settings) (prompt output : List Token) : Prop
    extends HasScores settings weights prompt output where
  meanCost :
    ∑ position ∈ Finset.range (countedTokens settings prompt output),
        min (outputCost settings weights prompt output position) (policy.C : Int)
      ≤ (policy.theta : Int) * (countedTokens settings prompt output : Int)
  aboveClip :
    ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : Int) < outputCost settings weights prompt output position).card ≤ policy.cap
  afterFullWindow : ∀ position (h : position < output.length),
    settings.positions ≤ prompt.length + position →
      modelNextToken settings weights (prompt ++ output.take position) = some output[position]

end Policy
