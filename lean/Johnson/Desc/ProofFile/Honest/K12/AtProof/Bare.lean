-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/Bare.lean: the bare jobs of the two proximity tests (the
kind K12) in the proof file's shared chain, and their two halves. A job (`TestJob`, Test.lean in the
folder above) is what a caller supplies for a test. A half (`Placed`,
Johnson/Desc/ProofFile/Honest/Frame.lean; below: the frame) is the prover's side of a sub-protocol
at its place; a job's half is `proverSideOfProximityTest` (Parts.lean in the folder above). A bare job (`bareJob`,
Doors.lean in this folder) holds public numbers only: a place's numbers (`p`, of type `P12`); the
group's members (`members`: the group's oracle messages, each with its sender's address, its number
and its count of coins); and who sent the first fold's fresh table (`fresh`). In the place of all
three functions of a job it has defaults: a state that holds nothing (`rec₀`), rows of zeros
(`rows₀`), no tree (`trees₀`). Its half is called a bare half below. The bare halves are for a test
of the laying: the laying is the frame's `chainSteps`, which builds a chain's list of rounds from
the halves and the book of coins (`ProverCoinCounts`), or returns an error. Defined at every public part (`Pub`,
Johnson/Desc/ProofFile/Pub.lean); the types V, W and X are free parameters. Definitions with code;
no theorem.

  `bareU`, `bareO`: the bare jobs of the test on the folded row's group (G_u) and of the test on
    Omega's group (G_omega), at a public part. The place's numbers are those of `four` (Places.lean
    in this folder); the members are `membersU` and `membersO`, the fresh table's sender `freshU`
    and `freshO` (Members.lean in this folder). Each is `none` where `four` or `sendPub`
    (Members.lean) returns `none`, and `bareO` also where the plan has no test on Omega's group
  `bareShared`: the halves of these two jobs, each where its job is made: `sharedOf` (Doors.lean) at
    `bareU` and `bareO`. It has the form of the list that `withShared` (Doors.lean) appends to the
    field `shared` of a filling of the honest prover (`OnlineProverParts`,
    Johnson/Desc/ProofFile/Honest/AtPure.lean). `sharedOf` takes any two jobs, so a job whose
    functions are real goes in by the same definition

What it is good for. What a half states of rounds, cuts, counts and names depends only on the
place's numbers, the members and the field `fresh` (by reading Parts.lean in the folder above;
proved nowhere). Rounds and cuts are its parts' numbers of moves; counts and names are the fields
`takes`, `spends` and `carries` of a part (`Part`, the frame). So whether `chainSteps` returns at a
job's half can be asked at the bare job that has the same three fields.

Limits.
- A bare half is a stand-in of public numbers for a test of the laying. It is no honest prover's
  side, and it is not to be laid into a filling that is played or counted.
- By its type a bare half is a half like any other; only its name marks it. What it does where it is
  put into a filling all the same: (1) to (5).
- (1) The frame's lists of the sub-protocols that send and have no half (`lacking`, the frame;
  `OnlineProverWithDescription.stillIdle`, AtPure.lean) do not name the one at its place, though the kind has no half
  there that can be accepted.
- (2) The frame's play falls back on a stored run's round only where no half is defined
  (`Step.tell`, at a round to which `chainSteps` has given no move): a bare half takes that
  fall-back away at its place.
- (3) Its moves show the folds of rows of zeros, from a verifier's state that holds nothing: the
  sub-protocol is not expected to accept them.
- (4) Whether each of its messages has the shape that the sub-protocol states is not evaluated here;
  where one has not, the error is the frame's own (`Step.tell`, of the class `Why.unfit`), not the
  sub-protocol's.
- (5) Each move computes the whole test's value anew (`testAll`, Test.lean, called by `msgAt`,
  Parts.lean): how long that takes, also at a small made-up plan, is not measured here.
- Neither `bareU` nor `bareO` asks that the place's numbers have two stages or more: where `four`
  yields the empty numbers (`H2U.noP12`; see the limits of Places.lean), a bare job is made of them.
- The members' counts are those of `msgOf` (Members.lean), which reads a message's shape with a
  default. Where a sending has no message of that number, the count is computed at the default
  shape, and the bare job is made all the same.
- One message is a member of both groups: message 1 of "send o_omega" (`senderO`), the split's mask
  message o_sp, is the second member in `membersU` and in `membersO`. So, where both jobs are made,
  all four parts of the two bare halves state that message's stretch of coins under `carries`
  (`memberRuns`, Parts.lean).
- No job is defined here at the first chain's or at the last chain's test: this file calls neither
  `lotOf` nor `secondOf` (Doors.lean). At the first chain's test JobL.lean and LotL.lean in this
  folder define a job and its lot, with limits of their own.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Doors
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Members

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K12 (P12 T12)
open Johnson.Prover.Link (PS)

variable {V W X W₀ Rc Tr X₀ : Type}

/-- The bare job of the test on G_u; `none` where `four Z` or `sendPub Z` is `none`. -/
def bareU (Z : Pub) : Option (TestJob W X) :=
  (four Z).bind fun F => (sendPub Z).map fun A => bareJob F.U (membersU A) freshU

/-- The bare job of the test on G_omega; `none` where the plan has no such test, and where `four Z`
or `sendPub Z` is `none`. -/
def bareO (Z : Pub) : Option (TestJob W X) :=
  (four Z).bind fun F => F.O.bind fun p => (sendPub Z).map fun A => bareJob p (membersO A) freshO

/-- The shared chain's two bare halves; a job that is `none` gives no half. -/
def bareShared (Z : Pub) : List (Placed V W X) := sharedOf bareU bareO Z

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.bareU
#print axioms ProofFile.Honest.K12.AtProof.bareO
#print axioms ProofFile.Honest.K12.AtProof.bareShared
