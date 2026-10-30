-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Ladder/Package.lean: the six top statements of VerifiableInference/Statements.lean, applied by name
to the argument system of the goals' verifier. Definitions only: no proof is in this file. Of them
`NearestSound` is proved (Johnson/Goal/Skeleton/SoundOfVerifyAt.lean; two more, of an illustrative
system: SoundOfVerifyMore.lean); what is proved of them, and of which nothing: lean/GAPS.md, 39.
Why. VerifiableInference/Statements.lean states what an argument system for a model's output should
satisfy: `Sound`, `SoundAndBinding`, `SoundOpened`, `Complete`, `ZeroKnowledge`, and the three
together, `CompleteSoundZeroKnowledge`. The goals of Ladder.lean apply one of the six by name
(`Sound`, in `G7` and `G7'`) and state the rest through kin of theirs. Here each of the six stands
as a goal on `verify` (Ladder.lean), as that file writes it.

The system. `systemOfRecord D Z s` (Ladder.lean): its verifier is `verify D Z (D.parse Z)`; its
committer, prover, form and parser are `D`'s own. `D` is a description of the protocol, Z the three
public files, s the settings that the reader returns at Z. As in Ladder.lean a goal takes a function
from the second hash function to a description, and speaks of it at the real one
(`atSecondHashFunction D`); and it speaks of the public files in scope (`InScope`). The files Z stand in front of
each statement: they are fixed before the hash function is drawn. Files out of scope, the library's
small example among them, are refused by `verify`: of these the goals here say nothing.

The errors α, ε and ζ are arguments, as in VerifiableInference/Statements.lean. A goal of this file
at an error function that is 1 everywhere says nothing: what counts is a proof at a named small one.
A goal on soundness alone is met by a verifier that refuses everything: it weighs only together
with `G3'pol`, of the same `D`: a nearby form and `G3'pol` meet at `storedPublicFiles` alone (Ladder.lean,
head 14 (a)).
No statement of VerifiableInference/Statements.lean bounds the queries of an honest party. So
soundness with completeness is met by a `D` that knows nothing of the model and asks for a proof of
work that is harder than any adversary within the budget can do, and that its honest prover does all
the same. The goals of Ladder.lean rule that out by a budget on the honest side (`HonestWithin`; in
`G9` a budget on `commit`). The single forms here have no such budget: to say that they hold says
less than to say that the goals of Ladder.lean hold.

TWO FORMS SIDE BY SIDE. The statements of VerifiableInference/Statements.lean speak of one system
and know no public files. Here a system stands at each set of files in scope.
FOR THE THREE STATEMENTS ON SOUNDNESS THE NEARBY FORM IS THE STATEMENT ITSELF, UNCHANGED, at each
set of files whose policy is exact match: nothing of it is weakened. What cannot hold is the same
statement at files with another acceptance policy, under which outputs are accepted that are not the
model's: that is our family of files, not a fault of the statement.
For completeness and zero knowledge the statement itself is not expected to hold, at any files: it
speaks of every request, and for some no proof is to be had: the request without an output token is
one. `CanServe` (VerifiableInference/CanServe.lean) says which requests are left: those "that can be
served".
Each reason is told in the docstrings: an argument, but where a theorem is named. So each statement
on soundness stands twice:
  `Package…`: the statement, at all files in scope.
  `Nearest…`: a nearby form that can hold. Its docstring says how it differs, and which part of the
    difference is forced and which is a choice.

  at all files in scope         a nearby form that can hold     how it differs
  `PackageSound`                `NearestSound`                  the same, at exact match alone
  `PackageSoundAndBinding`      `NearestSoundAndBinding`        the same, at exact match alone
  `PackageSoundOpened`          `NearestSoundOpened`            the same, at exact match alone
  `PackageComplete`             none in this file               acceptance is asked by `G3'pol`
                                                                (Ladder.lean)
  `PackageZeroKnowledge`        none in this file
  `PackageBundle`               none in this file

What the goals of Ladder.lean ask of these is said at each. That a goal there gives a goal here is
a theorem; such theorems stand in Ladder/PackageTies.lean.

Under an acceptance policy other than exact match the verifier accepts outputs that are not the
model's: that is what a policy is for. What is claimed there is `Policy.MeetsPolicy`, and the goals
on it are `G8` and `G3'pol` (Ladder.lean). VerifiableInference/Statements.lean has no statement
with a claim other than "the output tokens are the model's".

-/
import Ladder

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals
open VerifiableInference VerifiableInference.OnPublicFiles
open scoped ENNReal

/-! ## 1. Soundness -/

/-- **`Sound`, as written**, of the system of `verify`, at all files in scope: there is an
extractor such that no committer and prover get an output accepted that is not the output of the
model with the extracted weights, but with probability at most ε of the number of their queries.
It is not expected to hold at a small ε. The files `zGap` are in scope and their policy is not exact
match (`FilesRead.other`, which `VerifierAndGoals.filesRead` proves); there is an output there
that meets the policy and is not the model's (`FixedFacts.otherClaim`), and under `G3'pol` the
honest prover has it accepted. This one output does not contradict `Sound`, whose extractor need not
return the committed weights. A prover with two such outputs for one prompt would; no fact of
Ladder.lean gives two. An argument; no theorem states it. -/
def PackageSound (D : SecondHashFunctionType → Description) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    Sound (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε

/-- **`Sound`, a nearby form that can hold**: at the files in scope whose policy is exact match.
From Ladder.lean: `G7` asks this and more: `Sound` for every form, prover and parser within n
queries, at an error that is at most one quarter up to 2^64 queries. `D`'s own parser is among
these: `SoundAt` puts it within `honestBudget`, which is at most `parserBudget`. -/
def NearestSound (D : SecondHashFunctionType → Description) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    pp.pol = Inst.Model.AcceptancePolicy.exact →
    Sound (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε

/-! ## 2. Soundness and binding, for one extractor -/

/-- **`SoundAndBinding`, as written**, at all files in scope: one extractor serves for soundness, as
in `Sound`, and for binding: nobody opens the committer's commitment to other weights than the
extracted ones, but with probability at most ε.
Together with `G3'pol` twice its error is at least 1 - completenessErrorBound at some number of queries within the
honest side's budget: at `zGap` binding makes the extractor return the committed weights, but for ε,
and the honest prover's accepted output of `FixedFacts.otherClaim` is not their model's
(`packageSoundAndBinding_bar`, Ladder/PackageTies.lean, given the files as read). -/
def PackageSoundAndBinding (D : SecondHashFunctionType → Description) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    SoundAndBinding (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε

/-- **`SoundAndBinding`, a nearby form that can hold**: at the files in scope whose policy is
exact match.
From Ladder.lean: `G8` and `G9` ask its two clauses apart, for one extractor, `D.extractor`. `G8`'s
clause is on `Policy.MeetsPolicy`, which at exact match gives the model's output; the two errors
differ; `soundAndBinding_of_le` (VerifiableInference/Binds.lean) joins such clauses. -/
def NearestSoundAndBinding (D : SecondHashFunctionType → Description) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    pp.pol = Inst.Model.AcceptancePolicy.exact →
    SoundAndBinding (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε

/-! ## 3. Soundness for an opened commitment -/

/-- **`SoundOpened`, as written**, at all files in scope: nobody names weights and randomness from
which the committer computes a commitment, and has an output accepted under that commitment that is
not the output of the model with these weights, but with probability at most ε. No extractor occurs.
Together with `G3'pol` its error is at least 1 - completenessErrorBound at some number of queries within the honest
side's budget: at `zGap` the adversary names the weights of `FixedFacts.otherClaim` with honest
randomness and has their output accepted (`packageSoundOpened_bar`, Ladder/PackageTies.lean, given
the files as read). -/
def PackageSoundOpened (D : SecondHashFunctionType → Description) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    SoundOpened (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε

/-- **`SoundOpened`, a nearby form that can hold**: at the files in scope whose policy is exact
match.
It follows from `NearestSoundAndBinding` at a related error (`soundOpened_of_soundAndBinding`,
VerifiableInference/Checks.lean). -/
def NearestSoundOpened (D : SecondHashFunctionType → Description) (ε : ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    pp.pol = Inst.Model.AcceptancePolicy.exact →
    SoundOpened (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ε

/-! ## 4. Completeness -/

/-- **`Complete`, as written**, at all files in scope: for all weights, every prompt and the model's
own output, the honest committer's and prover's proof is refused with probability at most α.
It cannot hold at an α below 1 of a verifier that refuses some request with the model's own output
whatever the proof is (`not_complete_of_rejected`, VerifiableInference/NotComplete.lean): the
protocol serves requests up to a fixed length, and weights and prompts whose values stay within its
tables' ranges. That `verify` refuses such a request is an argument; no theorem states it. -/
def PackageComplete (D : SecondHashFunctionType → Description) (α : ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    Complete (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) α

/-! ## 5. Zero knowledge

A goal on zero knowledge is about the honest committer and the honest prover (`D.sample`,
`D.commit`, `D.prove`) and about what a proof may reveal (`D.shown`), not about `verify`.
`D.shown` is a free field of `D`: no goal of this file or of Ladder.lean bounds what it returns. -/

/-- **`ZeroKnowledge`, as written**, at all files in scope: what the experiment's verifier sees can
be made without the weights, from `D.shown` of them alone, up to a statistical distance of ζ, for
every request with the model's own output. What it sees (`View`,
VerifiableInference/Statements.lean): the commitment (256 bits), as many proofs as it asks for, each
with its request, its own queries to the hash function with their answers, and its own draws. The
public files Z are fixed before the weights and are the same in both experiments: what they tell of
the weights (a fitted model's scale file is made from its weights) is not counted. What else a
committer publishes, a key file with the record, has no place in the view: it is covered only as far
as a proof's form carries it, and not at all before the first proof.
Whether a request can be served depends on the weights, so what the honest prover does at a request
that cannot be served tells something of them: the statement is not expected to hold as written.
It speaks of requests with the model's own output. Under an acceptance policy other than exact
match the honest prover also answers requests whose output is not the model's; of these it says
nothing, and there the answer itself tells how far a token lies from the model's choice.
No goal of Ladder.lean says anything on zero knowledge. -/
def PackageZeroKnowledge (D : SecondHashFunctionType → Description) (ζ : ℕ → ℕ → ℝ≥0∞) : Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    ZeroKnowledge (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) ζ

/-! ## 6. The three together -/

/-- **`CompleteSoundZeroKnowledge`, as written**, at all files in scope: `Sound`, `Complete` and
`ZeroKnowledge` of one system. It cannot hold where one of the three cannot. -/
def PackageBundle (D : SecondHashFunctionType → Description) (α : ℝ≥0∞) (ε : ℕ → ℝ≥0∞) (ζ : ℕ → ℕ → ℝ≥0∞) :
    Prop :=
  ∀ (Z : PublicFiles) (pp : Inst.Model.ScalesAndPolicy), InScope Z = true → readFiles Z = .ok pp →
    CompleteSoundZeroKnowledge (systemOfRecord (atSecondHashFunction D) Z (settingsOfRead pp)) α ε ζ

end VerifierAndGoals
