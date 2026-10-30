-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFGuard/AtDescription.lean: THE GOALS' DESCRIPTION, MADE WITH THE UNGUARDED LAYING, IS THE
GOALS' DESCRIPTION; THE SAME AT `VerifierAndGoals.verify`. One definition, and four statements as
`def … : Prop`.

Why. `Spec.strike` (Unguarded.lean) says that what is laid for the proof file, `LPFD.Full.proofDataAndDecisionOfPublicFiles`,
is the same with the guard on the reply and without it (`laidPBare`). The goals speak of
`VerifierAndGoals.theDescription` and of `VerifierAndGoals.verify` at it. DoorText.lean writes the goals' description
out as a function of what is laid for the proof file: `Text.theDescription door`, with
`VerifierAndGoals.theDescription = Text.theDescription LPFD.Full.proofDataAndDecisionOfPublicFiles` (`Text.theDescription_at`).

THE FORM OF THE ARGUMENT: ONE FUNCTION AT TWO ARGUMENTS. The goals' description is
`Text.theDescription` at `proofDataAndDecisionOfPublicFiles` (proved); the description below is the same function at
`laidPBare` (by its text). The two arguments are equal (`strike`, Strike.lean). So the statements
below are cheap: they follow by congruence. What they are worth hangs on two readings and a walk,
none of them a theorem: that the twenty short declarations of `Text.theDescription` are the
library's own but for the letter (DoorText.lean); that nothing beneath these twenty leads to the
guard (a walk over names by a program that is not in this library); and what "without the guard"
means in `laidPBare` (Unguarded.lean).
("Strike" in the names: Unguarded.lean, limit 4. Nothing is struck.)

Main names.
* `theDescriptionBare := Text.theDescription laidPBare`: THE GOALS' DESCRIPTION, MADE WITH WHAT IS
  LAID FOR THE PROOF FILE WITHOUT THE GUARD.
* `Spec.strike_description`: `theDescriptionBare = VerifierAndGoals.theDescription`.
* `Spec.strike_verdict`: AT `VerifierAndGoals.verify`: at every function o in the place of the format's
  second hash function, all public files, every commitment, prompt and output and every form B
  (`FlashProve.FormBytes`: further tokens and five byte strings, the parsed files of a proof):
  the verifier at `theDescriptionBare o` with that description's own parser, and the verifier at
  `VerifierAndGoals.theDescription o` with its own, are the same algorithm. So they give the same verdict at
  every hash function.
* `Spec.strike_system`: the argument systems of which the goals on the honest side and on binding
  speak (`VerifierAndGoals.systemOfRecord`) are equal.
* `Spec.strike_any`: every property that can be stated in Lean holds of the one description if and
  only if it holds of the other.

Limits.
1. Statements; they are proved in StrikeAt.lean.
2. WHAT "WITHOUT THE GUARD" MEANS IS Unguarded.lean's TO SAY, with its eleven limits: in `laidPBare`
   the guard is still called at two places, with a test that always says yes (then it does nothing:
   `Spec.idle_block`, `Spec.idle_chain`, `Spec.idle_first`); at the third the call is gone.
3. NOTHING OF THE LIBRARY's TEXT IS STRUCK OR TURNED. Whether the guard's calls can be struck from
   the library on these statements is not said here.
4. NO THEOREM HERE SAYS ANYTHING ON "WITHOUT THE GUARD". The four statements would hold of any
   function in `Text.theDescription`'s place that gives `VerifierAndGoals.theDescription` at `proofDataAndDecisionOfPublicFiles`, also
   of one that throws its argument away. And since the two descriptions are equal, no statement of
   Lean can tell them apart: "without the guard" is a property of a TEXT, not of the object. That
   the guard's test on the reply is reached from nowhere in `theDescriptionBare`'s term is read off
   the texts, and a program that is not in this library walks the names. Neither is a theorem.
5. WHAT `Spec.strike_verdict` GIVES ON AN HONEST PROOF, AND WHAT NOT. Under the readings of limits 2
   and 4 (that `theDescriptionBare` is the description without the guard's test) it gives: the test
   turns no verdict: a proof is accepted with it if and only if it is accepted without it. It does
   not give that the guard's refusal is never reached (only that it is never the only cause of a
   no), nor that an honest proof is accepted.
6. `Spec.strike_verdict` speaks of each description's own parser, on the parsed form; not of the
   exchange file's bytes, and not of the parser that a run hands over, which is not looked at here.
   A parser for the one description does not type at the other without a transport, so no equation
   of verdicts at "the same" other parser is stated. The goals on soundness are stated for every
   type of form, every prover and every parser (`VerifierAndGoals.system`): such a closed property passes by
   `Spec.strike_any`.
7. The statements carry a theorem on `VerifierAndGoals.theDescription` over to `theDescriptionBare`. They do
   not free that theorem's proof of the guard: the soundness theorem's proof takes a fact from
   the test.
8. The theorems speak of Lean's terms, not of compiled code. Nothing on the programs' verifier.
9. No theorem of this folder says that anything is laid at any public files; other theorems say it
   at the library's written terms meant to be the full-size files, under the stored policy and
   others, at one function o; no theorem ties these terms to the release's files (Unguarded.lean,
   limit 8). At public files that fail the goals' test `VerifierAndGoals.InScope`, or at which nothing is
   laid, `Spec.strike_verdict` is an equation of two verifiers that refuse. That something is laid
   does not say that any proof is accepted: as far as this folder's theorems go, both verifiers may
   refuse every proof everywhere.
10. No goal of the release is named or stated. `theDescriptionBare` is a second description, written
    for these theorems alone; no definition outside this folder names it.
11. Nothing on soundness, completeness or hiding.


-/
import Johnson.LPFGuard.DoorText
import Johnson.LPFGuard.Unguarded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFGuard

open VerifiableInference (Commitment Token)

/-- **The goals' description, made with what is laid for the proof file without the guard.** -/
noncomputable def theDescriptionBare : VerifierAndGoals.SecondHashFunctionType → VerifierAndGoals.Description :=
  Text.theDescription laidPBare

/-- **At the goals' description.** -/
def Spec.strike_description : Prop := theDescriptionBare = VerifierAndGoals.theDescription

/-- **At `VerifierAndGoals.verify`**, each description with its own parser: one algorithm, at all inputs. -/
def Spec.strike_verdict : Prop :=
  ∀ (o : VerifierAndGoals.SecondHashFunctionType) (Z : VerifierAndGoals.PublicFiles) (commitment : Commitment) (prompt output : List Token)
    (B : FlashProve.FormBytes),
    VerifierAndGoals.verify (theDescriptionBare o) Z ((theDescriptionBare o).parse Z) commitment prompt output
        B =
      VerifierAndGoals.verify (VerifierAndGoals.theDescription o) Z ((VerifierAndGoals.theDescription o).parse Z) commitment
        prompt output B

/-- **At the argument system of which the goals on the honest side and on binding speak.** -/
def Spec.strike_system : Prop :=
  ∀ (o : VerifierAndGoals.SecondHashFunctionType) (Z : VerifierAndGoals.PublicFiles) (s : IntegerTransformer.Settings),
    VerifierAndGoals.systemOfRecord (theDescriptionBare o) Z s =
      VerifierAndGoals.systemOfRecord (VerifierAndGoals.theDescription o) Z s

/-- Every property that can be stated in Lean holds of the one description if and only if it holds
of the other. -/
def Spec.strike_any : Prop :=
  ∀ P : (VerifierAndGoals.SecondHashFunctionType → VerifierAndGoals.Description) → Prop, P VerifierAndGoals.theDescription ↔ P theDescriptionBare

end LPFGuard
