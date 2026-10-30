-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Goal/Skeleton/SoundOfVerifyGaps.lean

Index binding for a second relation, said in logit gaps, for the Lean verifier `verify`. The
relation is that the output meets the files' policy, three numbers (C, theta, cap). Terms:
lean/TERMS.md, table 2 and its note 2. The statements are `SoundForWith`
(VerifiableInference/MoreStatements.lean), the text of `Sound` with another claim and the extractor
named. That has the shape of index binding for this relation. This file does not lead from it to the
general form in which the library states index binding with a named extractor,
`ZKCP.HasIndexBindingWith` (ZKCP/Defs.lean). For `MeetsPolicy` and the IOP's own parser that form is
proved: `indexBindingUnderPolicy_of_verify_at` (Johnson/Goal/Skeleton/SoundOfVerifyForms.lean). The
step, for every system and claim: `VerifiableInference.indexBindingWith_of_soundForWith`, there.

But for the error, where `verify` accepts an output: the index extractor of the interactive oracle
proof (IOP) as written in Lean gives weights, from the public files, the commitment and the
committer's hash queries alone, so before any proof; the integer model at these weights has scores
for the output (`HasScores`); the gaps of the output's counted tokens, each clipped at C - 2^8, sum
to at most theta - 2^8 times their number (where a token is counted, that is a mean clipped gap of
at most theta - 2^8); at most cap of them have a gap above C - 2^8; and a token that follows a full
window is that model's next token. The error is `VerifierAndGoals.soundnessErrorInQueries t n` (Ladder/Bits.lean): with
T = t + n + 2^23 it is 16·T/2^128 + (T + 2)^2/2^256, where t bounds the committer's and the prover's
hash queries together, and n the proof parser's. That is 124 bits for each hash query, not 128, and
never below about 2^-101. The statements are for every proof parser. The IOP's own parser has n = 1
(`theDescription_within`, Johnson/Goal/Description/Description.lean); that case (`systemOfRecord`,
Ladder.lean) is not written out here.

This file states no goal.

Its five statements are theorems, with their proofs here. `GapsWithinPolicy` is a definition of this
file, made to say the goals' own claim `MeetsPolicy` (Policy/Front/MeetsPolicy.lean) in a user's
terms, and it is proved to be that claim, with no premise. The goals' files do not name it. Nor do
they name the shorthand in which it and two statements below are written: `Policy.outputGap`
(Policy/Front/MeetsPolicyBounds.lean), a token's cost less 2^8. The same can be had without
`GapsWithinPolicy`: `soundUnderPolicy_of_verify_at` with `Policy.meetsPolicy_iff_clauses`, which is
written in costs, and `Policy.MeetsPolicy.sum_clippedGap_le`, which is written in that shorthand
(both: Policy/Front/MeetsPolicyBounds.lean).

Words. A token's gap: how far its integer logit lies below the largest logit after the same context,
and 1 more if the first choice is the smaller token. The first choice: the least token of largest
logit. For a token of the vocabulary, where the model has a value, the gap is 0 exactly at the
model's next token (`Policy.outputGap_eq_zero_iff`, Policy/Front/MeetsPolicyBounds.lean). Counted:
the output tokens inside the window of 1,024 tokens of prompt and output together
(`Policy.countedTokens`); a token that follows a full window is the 1,025th. The last clause: a
token that follows a full window is the model's next token (clause (c) of `MeetsPolicy`). The model
has scores for an output if prompt and output are not empty, have at most 1,025 tokens together, all
in the vocabulary, and the model has a value on every output token's context. The reader is the
library's reader of the public files (`readFiles`, Ladder.lean), and pp is what it returns. In the
Lean names a `Description` is the IOP as written in Lean, and `atSecondHashFunction` takes it at the format's
second hash function. Paths count from lean/, but for lean/TERMS.md itself.

* `Policy.GapsWithinPolicy`: the claim. `Policy.meetsPolicy_iff_gapsWithinPolicy`: it is
  `MeetsPolicy`, written in gaps. Nothing is dropped or added.
* `soundFor_of_soundUnderPolicyAtZ`: `SoundForWith` for the policy of pp, at one set of public
  files, gives the same, with the same system, extractor and error, for every claim that follows
  from `MeetsPolicy`.
* `soundForGaps_of_verify_at`: that step at `soundUnderPolicy_of_verify_at`
  (Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean) and `GapsWithinPolicy`. It is that theorem said
  again, not a second result beside it.
* `soundForGaps_of_verify_at_gap`: the same where the files state (C, theta, cap) = (25856, 512, 1),
  with the numbers written out: clip 25,600, mean 256, one token. `soundForGaps_of_verify_at_zGap`:
  at the second named set of public files (`zGap`, Ladder/Stored.lean), which is in scope and states
  that policy by `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean).

What it gives.
* What the bounds give, at (25856, 512, 1). In an output of at most 99 counted tokens every counted
  token's gap is below 25,600, and the unclipped gaps sum to at most 256 times their number
  (`Policy.gaps_of_meetsPolicy_qExample_short`). At every length, of n counted tokens at most 256
  n / g have a gap of g or more, for 0 < g ≤ 25,600 (`Policy.card_gap_ge_mul_le_qExample`). Both:
  Policy/Front/MeetsPolicyAtGap.lean. And the claim can fail. At what the reader returns at `zGap`,
  for every n from 1 to 1,023, there are weights and an output of n counted tokens that has scores,
  meets the last clause and does not meet the policy
  (`VerifierAndGoals.AtFiles.exists_output_not_meeting_gap`); and there are weights under which an output of
  1,023 tokens whose first m have the gap 2,047, and the others the gap 0, meets it exactly if
  m ≤ 127 (`VerifierAndGoals.AtFiles.exists_outputs_at_budget_gap`). Both:
  Johnson/Goal/Files/MeetsPolicyAtFiles.lean. These weights are made up: nothing follows for a
  trained model.
* What is proved of its partner, correctness of extraction at the same extractor (the fifth limit
  below says why it is the partner). `theCpp (theTwin g) prove` (Johnson/Bind/Cpp/Defs.lean) is a
  variant of the Lean verifier's system: it keeps `verify` and its extractor
  (`Bind.Cpp.cpp_is_of_verify`, Johnson/Bind/Cpp/OfTie.lean) and has a stand-in committer written in
  Lean. Of it, at every g and prove, these are proved at `zGap` with no premise, each at an error of
  its own: correctness of extraction, the binding of the commitment in the opening form, and
  soundness after an honest commitment for `MeetsPolicy`
  (`AtFullSide.Tie.extractsCommitted_called_zGap`, `AtFullSide.Tie.bindsAt_called_zGap`,
  `AtFullSide.Tie.soundAtCommitted_live_zGap`, AtFullSide/Bind/LiveAtNamed.lean, in a side library,
  with the limits in that file's head). By that head: the error of the third is never below about
  2^-88; at this size that committer can never be run; nothing says that `verify` accepts any proof
  under that committer's commitments, and if it accepted none, the third would hold for that reason;
  nothing there is about the release's committing program. Of two more variants the binding of the
  commitment in the opening form is proved, and a form of correctness of extraction at each fixed
  choice of the committer's coins (lean/TERMS.md, notes 5 and 4, with the limits that they tell).

Limits.
* `verify` is the goals' Lean verifier (`VerifierAndGoals.verify`, Ladder.lean) at `theDescription`: a Lean
  function, which no program that lean/ builds runs. As typed it cannot be executed. A second term
  can, and whatever verdict that one gives is `verify`'s (`PV.Ride.verdictThe_is_theDescription`,
  Johnson/PVR/RideThe.lean). Nothing here is about the C++ programs or about a compiled run. Nothing
  here is about a real model's weights: the weights are whatever the extractor gives.
* `soundForGaps_of_verify_at` is the second half of `soundUnderPolicy_of_verify_at` with its claim
  rewritten. (The first half, that the IOP's own parser stays within `honestBudget`, is not carried
  over.) It says nothing that that theorem does not say, and the limits in the head of
  Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean hold here. That `protocolDataWellFormed` says yes is a theorem of
  a side library at the two named sets as Ladder/Stored.lean writes them (the fourth limit), and at
  the release's files as bytes evaluated, not proved. Among these limits: the public files are
  fixed before the hash function is sampled; the second hash function is a fixed function; the
  error grows with n; at the full size alone; beneath some of the called theorems stand files on
  coding theory adapted from third-party Lean (lean/LIMITS.md, L15). By the scope (`InScope`,
  Ladder.lean): one proof format and one model size.
* The extracted weights hang on the public files too, not on the commitment and the committer's hash
  queries alone: no theorem bars one commitment from being accepted at two sets of public files,
  with two sets of weights and two policies (the head of Ladder.lean, 13). The policy of the
  statement is the one that the reader returns at the given files. So a user has to hold the right
  public files, as it holds the right commitment, and to read the three numbers in the parameter
  file.
* Where the tests on the public files inside `verify` (`protocolDataWellFormed`,
  Johnson/Goal/Description/Live.lean) say no, `verify` rejects everything
  (`FlashProve.theDescription_dead_all`, Johnson/Goal/Description/DeadParser.lean), and the
  statement holds for that reason. At the two named sets, and at the first set's files under every
  policy in scope, they say yes: `AtFullSide.Top.theLive_zFull` (AtFullSide/Top/LiveAtFull.lean),
  `AtFullSide.Top.theLive_zGap`, `AtFullSide.Top.theLive_zAt` (AtFullSide/Top/LiveAtPolicies.lean),
  with the limits in these files' heads. The last two stand on the first. They lie in a side
  library, which this file and the main library do not import: only a build of that library shows a
  break in them. Of other public files in scope (another scale file, or another value of one of the
  five free numbers that the parameter file has beside the policy's three) none of the Lean files
  named here says so. No files in scope are known at which they say no (the head of
  Johnson/Goal/Description/LiveSaysNo.lean). A yes of these tests is no sign that `verify` accepts
  any proof. That an honest proof is accepted at the two named sets as bytes is evaluated, not
  proved; at the second set's written copy no theorem says it either (lean/TERMS.md: "the two stored
  sets of public files").
* Taken by itself, `soundForGaps_of_verify_at` bars nothing by its bounds on gaps against a
  committer who commits to weights under which every output that has scores and meets the last
  clause meets the policy. So it means something only together with correctness of extraction at the
  same extractor (that the extracted weights are the ones an honest committer put in:
  `ExtractsCommittedWeights`, VerifiableInference/MoreStatements.lean) and with knowing who made the
  commitment, which no theorem says.
* What is not proved of that partner. Of the Lean verifier's own system correctness of extraction
  cannot be stated with any content: the honest committer and prover of `theDescription` are
  empty placeholders (a committer that returns one constant, a prover that hands over empty files).
  The goals' file says the like of its own goals: `G8`, the goal under a policy, means something
  only together with `G9` (the binding of the commitment in the opening form: `BindsAt`) and
  `G3'pol` (outputs within a policy's tolerance are accepted), all in Ladder.lean. Of
  `theDescription` neither is proved: either would speak of the placeholders alone, and of such a
  committer `G9` is false (by hand: lean/TERMS.md, note 5).
* Weights under which every output that has scores and meets the last clause meets the policy exist
  at all policies with theta and C of at least 257: the all-zero ones
  (`Policy.meetsPolicy_zeroWeights_of_scores`, Policy/Front/TeethAllChannels.lean, at valid
  settings; the settings read off public files are valid: `VerifierAndGoals.valid_of_read`, Ladder/Ties.lean).
  There are outputs that have scores and meet the last clause under them: every well-formed output
  of at most one window meets every such policy (`Policy.meetsPolicy_zeroWeights`,
  Policy/Front/TrueUnder.lean). More generally: where, after each counted token's context, no logit
  lies more than s above that token's, an output that has scores and meets the last clause is within
  every policy with 2^8 + s + 1 ≤ theta and 2^8 + s + 1 ≤ C, whatever cap is
  (`Policy.meetsPolicy_of_close_logits`, Policy/Front/MeetsPolicyBounds.lean). At (25856, 512, 1)
  that is s up to 255. At exact match that theorem gives nothing where a token is counted.
* What the bounds do not give, at (25856, 512, 1). They do not bound how many counted tokens differ
  from the model's choice: all may, where the weights offer other tokens within 256
  (`Policy.meetsPolicy_qExample_of_gaps_le`). From 100 counted tokens on they bound no single token:
  one token may be any token of the vocabulary, if the others are the model's next tokens. So the
  three numbers do not bound the unclipped mean (`Policy.meetsPolicy_qExample_of_one_free`). The
  three numbers were fitted to no model. All of this: Policy/Front/MeetsPolicyAtGap.lean.
* At some policies the claim says little. With theta = C the clause on the mean holds of any gaps;
  if cap is also at least the number of counted tokens, so does the clause on the count
  (`Policy.meetsPolicy_iff_of_clip_le_mean_anyCap`, `Policy.clauses_forall_iff`,
  Policy/Front/MeetsPolicyBounds.lean). Such policies are in scope: (256, 256, 1) and
  (256, 256, 1024) at the first named set's files (`LPFPol.inScope_at_stored`,
  Johnson/LPFPol/LiveCorollaries.lean; that the reader returns the three numbers as written:
  `LPFPol.read_withPol`, Johnson/LPFPol/ScopeAtPolicy.lean). At the first of these the count is free
  only for an output with one counted token. More policies that exclude no output by its scores, at
  some settings: Policy/Front/MeetsPolicyIdleAtScales.lean.
* The unit of a gap is that of the integer model's logits under the extracted weights. No definition
  here reads a scale for it.
* The bounds are on one output, which the prover picks and may cut as it likes. Each token is scored
  after the output's own earlier tokens. The prompt is not scored. After a prompt of 1,024 tokens no
  token is counted, and of the three clauses only the last asks anything. The error is for one
  proof. For N proofs under one commitment, handed in as one list, N times the error follows by
  `VerifiableInference.SoundForWith.manyProofsUnion`
  (Johnson/Goal/Skeleton/SoundOfVerifyForms.lean), which is not called here.
* To be within the policy is not to pass the test of Token-DiFR (arXiv 2511.20621): see the
  docstring of `MeetsPolicy`.
* `zGap` is the bytes written in Ladder/Stored.lean. That they are the bytes of a folder of examples
  is not said here.
* Nothing on completeness or hiding, on correctness of extraction or the binding of the commitment
  in the opening form, or on anything else that names an honest committer or prover: the theorems of
  this file say nothing on these; what other files prove stands above.

-/
import Johnson.Goal.Skeleton.SoundOfVerifyPolicy
import Policy.Front.MeetsPolicyAtGap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- Remove the default instance `Inst.Model.Scl.ref`: no statement below may pick it up silently. -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace Policy

open VerifiableInference

/-- **The output's gaps are within the policy under the weights' scores.** The model has scores for
the output (`HasScores`); the gaps of the counted output tokens, each clipped at C - 2^8, sum to at
most theta - 2^8 times their number; at most cap of them have a gap above C - 2^8; and an output
token that follows a full window is the model's next token. It is `MeetsPolicy`, written in gaps
(`meetsPolicy_iff_gapsWithinPolicy`). It is not one of the library's goals. No condition on the
three numbers is part of it: the two differences are whole numbers and may be negative (with C < 2^8
every counted token of an output that has scores is above the clip). The unit of a gap is that of
the given weights' integer logits. The counted tokens are those of this one output. -/
structure GapsWithinPolicy (settings : IntegerTransformer.Settings) (policy : Inst.Model.AcceptancePolicy)
    (weights : ModelWeights settings) (prompt output : List Token) : Prop where
  scores : HasScores settings weights prompt output
  meanClippedGap :
    ∑ position ∈ Finset.range (countedTokens settings prompt output),
        min (outputGap settings weights prompt output position) ((policy.C : ℤ) - 2 ^ 8)
      ≤ ((policy.theta : ℤ) - 2 ^ 8) * (countedTokens settings prompt output : ℤ)
  aboveClip :
    ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) - 2 ^ 8 < outputGap settings weights prompt output position).card ≤
      policy.cap
  afterFullWindow : ∀ position (h : position < output.length),
    settings.positions ≤ prompt.length + position →
      modelNextToken settings weights (prompt ++ output.take position) = some output[position]

/-- `MeetsPolicy` is `GapsWithinPolicy`: the same four parts, with clauses (a) and (b) written in
gaps. -/
theorem meetsPolicy_iff_gapsWithinPolicy {settings : IntegerTransformer.Settings}
    (policy : Inst.Model.AcceptancePolicy) (weights : ModelWeights settings) (prompt output : List Token) :
    MeetsPolicy settings policy weights prompt output ↔
      GapsWithinPolicy settings policy weights prompt output := by
  have same : ((Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) < outputCost settings weights prompt output position) =
      (Finset.range (countedTokens settings prompt output)).filter fun position =>
        (policy.C : ℤ) - 2 ^ 8 < outputGap settings weights prompt output position :=
    Finset.filter_congr fun j _ => by
      rw [outputCost_eq_outputGap_add]
      constructor <;> intro h <;> linarith
  constructor
  · intro h
    exact ⟨h.toHasScores, h.sum_clippedGap_le, by rw [← same]; exact h.aboveClip,
      h.afterFullWindow⟩
  · intro g
    exact
      { toHasScores := g.scores
        meanCost := (meanClause_iff_gap (cost := outputCost settings weights prompt output)).2 (by
          simp only [outputCost_sub]
          exact g.meanClippedGap)
        aboveClip := by rw [same]; exact g.aboveClip
        afterFullWindow := g.afterFullWindow }

end Policy

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles
open P5J

/-- `SoundForWith` for the policy of pp, at one set of public files, gives the same for every claim
that follows from `MeetsPolicy` at pp's settings and policy: the same system, the same extractor,
the same error. For every `Description`. Nothing here ties pp to Z but the premise `sound`: pp is
the files' own only where it is what the reader returns at Z. The conclusion says as much as the
claim says: of a claim that always holds it says nothing. -/
theorem soundFor_of_soundUnderPolicyAtZ (D : Description) (eps : ℕ → ℕ → ℝ≥0∞) (Z : VerifierAndGoals.PublicFiles)
    (pp : Inst.Model.ScalesAndPolicy) (sound : SoundUnderPolicyAtZ D eps Z pp)
    (claim : ModelWeights (settingsOfRead pp) → List Token → List Token → Prop)
    (follows : ∀ weights prompt output,
      Policy.MeetsPolicy (settingsOfRead pp) pp.pol weights prompt output →
        claim weights prompt output)
    (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → D.Rand → List Token → List Token →
      RandomizedAlgorithm Form)
    (parse : Parser D Z Form) (n : ℕ) (within : parse.Within n) :
    SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
      (D.extractor Z (settingsOfRead pp)) claim fun t => eps t n := by
  have h1 := sound.2 Form prove parse n within
  have h2 := SoundForWith.mapWeights _ _ _ _ h1 (ModelWeights (settingsOfRead pp)) D.Shown
    (D.shown (settingsOfRead pp)) (modelNextToken (settingsOfRead pp))
    (D.commit Z (settingsOfRead pp)) prove id claim follows
  have h3 : SoundForWith (system D Z (settingsOfRead pp) Form prove parse)
      (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) claim (fun t => eps t n) := h2
  have same : (fun c q => (D.extractor Z (settingsOfRead pp) c q).map id) =
      D.extractor Z (settingsOfRead pp) := by
    funext c q
    cases D.extractor Z (settingsOfRead pp) c q <;> rfl
  exact Eq.mp (congrArg (fun extractor =>
    SoundForWith (system D Z (settingsOfRead pp) Form prove parse) extractor claim
      fun t => eps t n) same) h3

/-- **For the Lean verifier `verify`: index binding for a second relation, that the output's gaps
are within the files' policy, at one set of public files in scope, read as pp.** (The term:
lean/TERMS.md, note 2. It is stated as `SoundForWith`, the shape of index binding.) For every form
of proof and every proof parser within n hash queries, and for every committer and every prover with
at most t hash queries together: the probability that `verify` accepts while the IOP's own extractor
gives no weights, or gives weights at which the output's gaps are not within the files' policy
(`Policy.GapsWithinPolicy`, which is the goals' own claim `MeetsPolicy`:
`Policy.meetsPolicy_iff_gapsWithinPolicy`), is at most `VerifierAndGoals.soundnessErrorInQueries t n`. (The argument `prove` is
the system's honest prover, which this property does not read.) It is the second half of
`soundUnderPolicy_of_verify_at` with its claim rewritten. Three of its limits (the others: this
file's head). The public files are fixed before the hash function is sampled. The unit of a gap is
that of the extracted weights' integer logits. Taken by itself, it bars nothing by its bounds on
gaps against a committer who commits to weights under which every output that has scores and meets
the last clause meets the policy: it means something only together with correctness of extraction at
the same extractor and with knowing who made the commitment. What is proved of that partner: this
file's head. -/
theorem soundForGaps_of_verify_at (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp) (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → (atSecondHashFunction theDescription).Rand → List Token →
      List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (n : ℕ) (within : parse.Within n) :
    SoundForWith (system (atSecondHashFunction theDescription) Z (settingsOfRead pp) Form prove parse)
      ((atSecondHashFunction theDescription).extractor Z (settingsOfRead pp))
      (Policy.GapsWithinPolicy (settingsOfRead pp) pp.pol) fun t => VerifierAndGoals.soundnessErrorInQueries t n :=
  soundFor_of_soundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp
    (soundUnderPolicy_of_verify_at Z pp scope read) _
    (fun weights prompt output meets =>
      (Policy.meetsPolicy_iff_gapsWithinPolicy pp.pol weights prompt output).1 meets)
    Form prove parse n within

/-- **For the Lean verifier `verify`: index binding for a second relation, at public files in scope
that state (C, theta, cap) = (25856, 512, 1), with the relation written out in numbers.** (The term:
lean/TERMS.md, note 2. It is stated as `SoundForWith`, the shape of index binding.) The relation is
the goals' own claim `MeetsPolicy` at these three numbers, written in gaps:
`Policy.meetsPolicy_iff_gapsWithinPolicy`, with 25856 - 2^8 = 25,600 and 512 - 2^8 = 256 put in
(`Policy.qExample_clip`, `Policy.qExample_mean`). That the text below says neither more nor less
than that claim follows from these three by hand; no theorem of this file states it, and the proof
uses one direction. The claim: the model has scores for the output; the gaps of its counted tokens,
each clipped at 25,600, sum to at most 256 times their number; at most one of them has a gap above
25,600; a token that follows a full window is the model's next token. In an output of at most 99
counted tokens that bounds every gap below 25,600 and the unclipped gaps' sum by 256 times their
number (`Policy.gaps_of_meetsPolicy_qExample_short`). It does not bound how many counted tokens
differ from the model's choice, and from 100 counted tokens on one token may be any token of the
vocabulary if the others are the model's next tokens (this file's head;
Policy/Front/MeetsPolicyAtGap.lean). The limits of `soundForGaps_of_verify_at` hold: the public
files are fixed before the hash function is sampled; the unit of a gap is that of the extracted
weights' integer logits; taken by itself, it bars nothing by its bounds on gaps against a committer
who commits to weights under which every output that has scores and meets the last clause meets the
policy: it means something only together with correctness of extraction at the same extractor and
with knowing who made the commitment. -/
theorem soundForGaps_of_verify_at_gap (Z : VerifierAndGoals.PublicFiles) (pp : Inst.Model.ScalesAndPolicy)
    (scope : InScope Z = true) (read : readFiles Z = .ok pp) (gap : pp.pol = ⟨25856, 512, 1⟩)
    (Form : Type)
    (prove : ModelWeights (settingsOfRead pp) → (atSecondHashFunction theDescription).Rand → List Token →
      List Token → RandomizedAlgorithm Form)
    (parse : Parser (atSecondHashFunction theDescription) Z Form) (n : ℕ) (within : parse.Within n) :
    SoundForWith (system (atSecondHashFunction theDescription) Z (settingsOfRead pp) Form prove parse)
      ((atSecondHashFunction theDescription).extractor Z (settingsOfRead pp))
      (fun weights prompt output =>
        Policy.HasScores (settingsOfRead pp) weights prompt output ∧
        ∑ position ∈ Finset.range (Policy.countedTokens (settingsOfRead pp) prompt output),
            min (Policy.outputGap (settingsOfRead pp) weights prompt output position) 25600
          ≤ 256 * (Policy.countedTokens (settingsOfRead pp) prompt output : ℤ) ∧
        ((Finset.range (Policy.countedTokens (settingsOfRead pp) prompt output)).filter
          fun position =>
            25600 < Policy.outputGap (settingsOfRead pp) weights prompt output position).card ≤ 1 ∧
        ∀ position (h : position < output.length),
          (settingsOfRead pp).positions ≤ prompt.length + position →
            modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
              some output[position])
      fun t => VerifierAndGoals.soundnessErrorInQueries t n :=
  soundFor_of_soundUnderPolicyAtZ (atSecondHashFunction theDescription) VerifierAndGoals.soundnessErrorInQueries Z pp
    (soundUnderPolicy_of_verify_at Z pp scope read) _
    (fun weights prompt output meets => by
      rw [gap] at meets
      have g := (Policy.meetsPolicy_iff_gapsWithinPolicy _ weights prompt output).1 meets
      have a := g.meanClippedGap
      have b := g.aboveClip
      rw [Policy.qExample_clip, Policy.qExample_mean] at a
      rw [Policy.qExample_clip] at b
      exact ⟨g.scores, a, b, g.afterFullWindow⟩)
    Form prove parse n within

/-- **For the Lean verifier `verify`: index binding for a second relation, at the second named set
of public files, with the relation written out in numbers.** (The term: lean/TERMS.md, note 2. It is
stated as `SoundForWith`, the shape of index binding.) The relation is that of
`soundForGaps_of_verify_at_gap`: the goals' own claim `MeetsPolicy` at these three numbers, written
in gaps (`Policy.meetsPolicy_iff_gapsWithinPolicy`). `zGap` (Ladder/Stored.lean) is in scope, is
read, and states the policy (25856, 512, 1): `VerifierAndGoals.filesRead`. (That it is in scope is used in the
proof and is not part of the statement.) So no premise on the files is left. That alone is no
content: a verifier that rejects everything meets it too, and where the tests on the public files
inside `verify` (`protocolDataWellFormed`) say no, `verify` is such a verifier. At `zGap` they say yes:
`AtFullSide.Top.theLive_zGap` (AtFullSide/Top/LiveAtPolicies.lean, in a side library that this file
does not import). A yes of these tests is no sign that `verify` accepts any proof: that it accepts
an honest proof under this policy is not proved. By lean/TERMS.md it was evaluated (there: "the two
stored sets of public files"). The limits of `soundForGaps_of_verify_at_gap` hold. -/
theorem soundForGaps_of_verify_at_zGap :
    ∃ pp : Inst.Model.ScalesAndPolicy, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      ∀ (Form : Type)
        (prove : ModelWeights (settingsOfRead pp) → (atSecondHashFunction theDescription).Rand → List Token →
          List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction theDescription) zGap Form) (n : ℕ), parse.Within n →
        SoundForWith (system (atSecondHashFunction theDescription) zGap (settingsOfRead pp) Form prove parse)
          ((atSecondHashFunction theDescription).extractor zGap (settingsOfRead pp))
          (fun weights prompt output =>
            Policy.HasScores (settingsOfRead pp) weights prompt output ∧
            ∑ position ∈ Finset.range (Policy.countedTokens (settingsOfRead pp) prompt output),
                min (Policy.outputGap (settingsOfRead pp) weights prompt output position) 25600
              ≤ 256 * (Policy.countedTokens (settingsOfRead pp) prompt output : ℤ) ∧
            ((Finset.range (Policy.countedTokens (settingsOfRead pp) prompt output)).filter
              fun position =>
                25600 <
                  Policy.outputGap (settingsOfRead pp) weights prompt output position).card ≤ 1 ∧
            ∀ position (h : position < output.length),
              (settingsOfRead pp).positions ≤ prompt.length + position →
                modelNextToken (settingsOfRead pp) weights (prompt ++ output.take position) =
                  some output[position])
          fun t => VerifierAndGoals.soundnessErrorInQueries t n := by
  obtain ⟨scope, pp, read, gap⟩ := VerifierAndGoals.filesRead.other
  exact ⟨pp, read, gap, fun Form prove parse n within =>
    soundForGaps_of_verify_at_gap zGap pp scope read gap Form prove parse n within⟩

end VerifierAndGoals.AtTheName

#print axioms Policy.meetsPolicy_iff_gapsWithinPolicy
#print axioms VerifierAndGoals.AtTheName.soundFor_of_soundUnderPolicyAtZ
#print axioms VerifierAndGoals.AtTheName.soundForGaps_of_verify_at
#print axioms VerifierAndGoals.AtTheName.soundForGaps_of_verify_at_gap
#print axioms VerifierAndGoals.AtTheName.soundForGaps_of_verify_at_zGap
