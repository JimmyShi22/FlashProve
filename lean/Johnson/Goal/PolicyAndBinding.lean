-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/PolicyAndBinding.lean: soundness under the public files' own policy TOGETHER WITH
binding, at one extractor, with no hypothesis left: the goals `G8bits` and `G9bits`
(Ladder/Bits.lean) of the stand-in description `theWideDigits`
(Johnson/Goal/Conditions/WideDigits.lean), which keeps the verifier and the extractor of
`theDescription` and adds a committer. THAT COMMITTER IS WRITTEN IN LEAN BESIDE THE PROTOCOL: A
PLACEHOLDER THAT CORRESPONDS TO NO PROGRAM OF THE RELEASE; WRITTEN, NOT RUN: its randomness is a
number with more digits than a machine holds (WideDigits.lean's head). NO THEOREM SAYS THAT `verify`
ACCEPTS A PROOF UNDER ITS COMMITMENTS (the goal `G3'pol`, Ladder.lean, is not had). Calls alone. No
new goal is stated: these are theorems about the goals' own definitions.
"Binding" in this file is the opening form, `BindsWith` (VerifiableInference/MoreStatements.lean):
nobody opens a commitment, by naming weights and randomness from which the committer gives it, to
weights that the extractor does not give; at fixed randomness it yields that the extractor gives the
committed weights back (`BindsWith.atRandomness`). It is not the index binding of ZKCP/Defs.lean's
`HasIndexBinding`: the half on soundness has that form, for the claim "meets the policy" (the tie is
typed at exact match: `sound_iff`, VerifiableInference/Agreement.lean), and speaks of every
commitment, whoever made it.
Why. At a policy in scope with 257 ≤ theta (so 257 ≤ C; `zGap`'s is one) soundness under the policy
bars nothing by itself against a committer who commits to weights under which every well-formed
output meets the policy. The all-zero weights are such, under the side conditions of
`meetsPolicy_zeroWeights` (Policy/Front/TrueUnder.lean: prompt and output not empty, at most 1,025
tokens together, all in the vocabulary, a token after a full window is token 0). `G8` means
something only together with `G9` at the same extractor and `G3'pol` (Ladder.lean's head, 6), and
with whose commitment it is and who chose the public files (so the policy), which no Lean text says.
THIS FILE HAS THE FIRST TWO, OF A STAND-IN; `G3'pol` IS NOT HAD. AT THIS TERM IT IS OUT OF REACH:
the stand-in's honest prover hands over empty bytes and its sampler gives 0
(`placeHolderNumberCoins`, Johnson/Goal/Conditions/WideOnto.lean). (By reading: no theorem says that
`verify` rejects the empty form.) Both halves hold at every K and W (`G8bits_theWide`,
`G9bits_theWide`); no K with a true prover is written. EVEN WITH ALL THREE THE FENCE STANDS: a
committer may itself commit to such weights, and against that committer the pair says nothing at
these policies.
  `g8bits_digits_of_verify`: `G8bits theWideDigits`, from the three rows that are theorems:
    `keySound_holds` (Johnson/Goal/Conditions/KeyOpenHolds.lean), `FlashProve.entrySound`
    (Johnson/Goal/Conditions/EntrySits.lean), `proofSound_of_verify`
    (Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean). `ProofSound` is a theorem in this library:
    `proofSound_of_verify` (Johnson/Goal/Skeleton/SoundOfVerifyGoals.lean); it asks something only
    where `protocolDataWellFormed` says yes (Johnson/Goal/Conditions/RowsAtTheRecord.lean).
  **`policy_and_binding_digits`**: the pair; its second half is `G9bits_digits` (WideDigits.lean).
  `digits_is_of_verify`: why it is "of `verify`, at one extractor": `atSecondHashFunction theDescription` is
    `flashProveDescription`; the stand-in description's `verify` is `flashProveDescription`'s at every parser; its extractor is
    `atSecondHashFunction theDescription`'s. In both goals the extractor is the one term
    `D.extractor Z (settingsOfRead pp)` (Ladder.lean: `SoundUnderPolicyAt`, `BindsAt`).
  **`policy_and_binding_at_zGap`**: both halves spelled out at the goals' second named set of
    public files, whose policy is (C, theta, cap) = (25856, 512, 1).
Limits. CALLS ALONE: NO NEW ARGUMENT IS MADE HERE. Stated of a stand-in description, not of
`theDescription`, whose own committer is hollow. THE PAIR IS A CONJUNCTION: that an accepted output
meets the policy at the OPENED weights (the join, at the two errors' sum) is not stated in this file
(`NearestSoundAndBinding` and `NearestSoundOpened`, Ladder/Package.lean, are at exact match). The
half on binding does not read `verify` (the verifier is idle in `G9bits`: the head of
Johnson/Goal/Conditions/WideAtThe.lean): the two halves meet in the extractor alone. The errors are
the goals' own (Ladder/Bits.lean): `soundnessErrorInQueries t n` is 16 / 2^128, or 124 bits, for each query and about
2^-101 at t = n = 0, where t bounds the adversary's queries and n the parser's; `bindingErrorInQueries t` is
likewise 16 / 2^128 for each query and about 2^-101 at t = 0, where t bounds the committer's and the
opener's queries together. The half on binding speaks only of commitments that the stand-in's
committer makes: to open is to name weights and a number from which that committer, run again, gives
the commitment. Of any other commitment it says nothing: there the extractor may give any weights,
the all-zero weights too. No theorem ties the committer to the release's program that commits. It
makes every commitment that the committer written out at given coins, `(T₀ Z).commitAtCoins`, makes
at coins whose salts have the salts' length, by two theorems (`coins_enumerated_digits_closed`,
WideDigits.lean; `fixedCommit_theWide`, Johnson/Goal/Conditions/BindsPlain.lean): one inclusion. The
way back, under a premise on the number, is a third theorem's (`commit_withTerms_reach`,
Johnson/Goal/Conditions/CoinsEnumerated.lean), stated for any description and any honest side and
not called here. Values, not algorithms. Of these coins only those at the format's own start, the
public files' digest, are ones that a program could write; an opening at another start is of strings
outside the format (said here without a theorem): that part of the half on binding is mathematics
beyond any program's commitment, not a promise about it. A verifier that enforces exact match at
every policy meets both halves (Ladder.lean's head, 6), and so does one that rejects everything (the
same head, 2): nothing proved here shows that `verify` accepts an output other than the model's own.
In scope are also policies that leave every counted token free at all weights: theta = C with cap at
least the number of counted tokens (the docstring of `InScope`, Ladder.lean;
`meetsPolicy_iff_of_clip_le_mean`, Policy/Front/MeetsPolicyGuards.lean): there the half on soundness
bars nothing of a counted token, whoever committed. Shown to be in scope are `storedPublicFiles`, `zGap`
(`VerifierAndGoals.filesRead`) and `zAt C theta cap`, which is `storedPublicFiles` under another policy, within four
bounds (`inScope_zAt`, Johnson/Goal/Files/ScopeAtPolicies.lean). `theWideDigits` does not read its
argument, and `flashProveDescription` names the second hash function (the head of
Johnson/Goal/Conditions/MoreAtDigits.lean): no row on `G7'` or `G7'bits` may be counted at it. Where
`protocolDataWellFormed` says no, `verify` rejects everything and the half on soundness holds for that reason; the
plan without depth and empty data are laid there (of the empty data and the rejecting the head of
MoreAtDigits.lean says it of `theWide K W` itself), and binding holds of the committer over that
dead frame, not over the release's (the head of Johnson/Goal/Conditions/BindsAtSecondHashFunction.lean, 5). AT
`storedPublicFiles` AND `zGap`, FILES WRITTEN IN Ladder/Stored.lean THAT NO LEAN TIES TO THE RELEASE's, AND AT
`zAt` WITHIN ITS BOUNDS, `protocolDataWellFormed` (AT `OnBytes.secondHashFunction`) SAYS YES: THEOREMS OF A SIDE LIBRARY, NOT
CALLED HERE (`theLive_zFull`, AtFullSide/Top/LiveAtFull.lean; `theLive_zGap`, `theLive_zAt`,
AtFullSide/Top/LiveAtPolicies.lean); OF OTHER FILES THIS HEAD NAMES NO SUCH THEOREM.
At the policy of `zGap` one run (its prints lie outside this library) of the step-by-step form of
Johnson/PVR/RideThe.lean, whose verdict is `verify`'s by `verdictThe_is_theDescription` (at the
description's own parser, where a verdict is given), accepted one honest full-size proof and
rejected five altered inputs (synthetic weights; the parsed form of the files; natively compiled in
part; evaluated once, not proved): in that run the gate said yes (`live_of_accept`,
Johnson/Goal/Description/AcceptGivesLive.lean). The proof was the stored example's
(examples/full-size-clipped-gap/); which build made it the run's report does not say. A second run
at that policy (the same form; synthetic weights; evaluated once), on a proof that a build of the
release's programs made at a commitment of its own, accepted the honest proof and one of five
altered inputs: one bit of the parsed proof file, in a Merkle-path entry that the verifier does not
read (by reading; no theorem); no false claim. In neither run did a refusal reach the policy's own
test. By the stored example's README alone (a run of the integer model: no proof, no print of these
runs and no Lean text shows it) the output of the first run's honest proof leaves the model's first
choice at one token. The second run's proof is of the same request and reply (byte for byte, by that
run's report), under another commitment; that this commitment is to the same weights, so that the
README's word holds there too, no print of these runs says. In neither run was that request tried at
the public files of exact match: no pair of runs shows that the tolerance made the difference. Each
run stood under the commitment that lay with its proof's files, which came from no run of this
committer; whether this committer gives it at any weights and number, no theorem and no run says. No
test of binding has been run. By the runs' own reports their three public files are `zGap`'s bytes.
These are two runs of more: what has been run, under a tolerant policy too, is told by kinds and
counts, not run by run, on lean/THEOREM.md ("What has been run").
What "meets the policy" says is the definition's (Policy/Front/MeetsPolicy.lean): a gap has the unit
of the weights' own scores, and to meet the policy is not to pass Token-DiFR's test (the end of that
definition's docstring). The public files are fixed before the hash function is sampled. At the full
size alone; the verifier with fourteen entry tests. Beneath the half on soundness stand files on
coding theory adapted from third-party Lean (lean/LIMITS.md, L15): beneath five of the rows that
Johnson/Goal/Skeleton/SoundOfVerifyAt.lean calls, by a program that follows Lean's own account of
what each proof uses, in one run. The
limits of Johnson/Goal/Skeleton/SoundOfVerifyPolicy.lean, of WideDigits.lean and of the files that
are called travel whole; so do those of Johnson/Goal/TopOfThreeBinding.lean, but for two: its three
hypotheses are theorems (named above), and that the stand-in's extractor is `theDescription`'s is
`same_extractor_wide` (Johnson/Goal/SameExtractorWide.lean). Nothing on completeness or hiding.
-/
import Johnson.Goal.Skeleton.SoundOfVerifyGoals
import Johnson.Goal.SameExtractorWide
import Johnson.Goal.Files.FilesReadProof

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section
open scoped ENNReal

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals VerifierAndGoals.Fit FlashProve FlashProve
open VerifiableInference

/-- **`G8bits` of the stand-in description: soundness under the files' policy, at every policy
in scope.** -/
theorem g8bits_digits_of_verify : G8bits theWideDigits :=
  G8bits_theWide digitCoins digitWide keySound_holds FlashProve.entrySound proofSound_of_verify

/-- **THE PAIR, AT ONE EXTRACTOR, AT EVERY POLICY IN SCOPE: NO HYPOTHESIS LEFT.** The committer is
written in Lean and corresponds to no program of the release. A verifier that rejects everything, or
one that enforces exact match at every policy, meets the pair too: see the head. -/
theorem policy_and_binding_digits : G8bits theWideDigits ∧ G9bits theWideDigits :=
  ⟨g8bits_digits_of_verify, G9bits_digits⟩

section
/- Lean compares these names and does not unfold them (as in
Johnson/Goal/Conditions/AllAtDigits.lean). -/
attribute [local irreducible] theCoding theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF descriptionOfDataOnBytes
  FlashProve.thePlan FlashProve.theItem digitCoins digitWide

/-- **Why the pair is "of `verify`, at one extractor".** -/
theorem digits_is_of_verify (o : SecondHashFunctionType) :
    atSecondHashFunction theDescription = flashProveDescription ∧
      (∀ (Z : VerifierAndGoals.PublicFiles) (Form : Type) (parse : Parser flashProveDescription Z Form),
        verify (theWideDigits o) Z parse = verify flashProveDescription Z parse) ∧
      (theWideDigits o).extractor = (atSecondHashFunction theDescription).extractor :=
  ⟨the_description_is, fun Z _ parse => verify_digits o Z parse,
    same_extractor_wide digitCoins digitWide o⟩

end

/-- **BOTH HALVES AT `zGap`, SPELLED OUT, OF THE STAND-IN**, whose committer is written in Lean
and corresponds to no program of the release. In scope; read; the policy (25856, 512, 1); but with
probability at most `soundnessErrorInQueries t n` nobody has an output accepted for which the extractor gives no
weights, or which does not meet that policy at the weights that it gives; and but with probability
at most `bindingErrorInQueries t` nobody opens a commitment of that committer's make to weights that the same
extractor does not give. `protocolDataWellFormed` says yes at `zGap` (`AtFullSide.Top.theLive_zGap`, in a side
library; not called here). The goals' clauses on the budgets (the verifier's, the parser's and the
committer's queries) are not repeated here: they stand in `G8bits` and `G9bits` above. The all-zero
weights meet this policy at every well-formed output: see the head. -/
theorem policy_and_binding_at_zGap :
    InScope zGap = true ∧ ∃ pp, readFiles zGap = .ok pp ∧ pp.pol = ⟨25856, 512, 1⟩ ∧
      (∀ (Form : Type)
        (prove : ModelWeights (settingsOfRead pp) → (atSecondHashFunction theWideDigits).Rand → List Token →
          List Token → RandomizedAlgorithm Form)
        (parse : Parser (atSecondHashFunction theWideDigits) zGap Form) (n : ℕ), parse.Within n →
        SoundForWith (system (atSecondHashFunction theWideDigits) zGap (settingsOfRead pp) Form prove parse)
          ((atSecondHashFunction theWideDigits).extractor zGap (settingsOfRead pp))
          (Policy.MeetsPolicy (settingsOfRead pp) pp.pol) fun t => soundnessErrorInQueries t n) ∧
      BindsWith (systemOfRecord (atSecondHashFunction theWideDigits) zGap (settingsOfRead pp))
        ((atSecondHashFunction theWideDigits).extractor zGap (settingsOfRead pp)) bindingErrorInQueries :=
  let ⟨sc, pp, hr, hp⟩ := VerifierAndGoals.filesRead.other
  ⟨sc, pp, hr, hp, (g8bits_digits_of_verify.2 zGap pp sc hr).2, (G9bits_digits zGap pp sc hr).2⟩

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.g8bits_digits_of_verify
#print axioms VerifierAndGoals.AtTheName.policy_and_binding_digits
#print axioms VerifierAndGoals.AtTheName.digits_is_of_verify
#print axioms VerifierAndGoals.AtTheName.policy_and_binding_at_zGap
