-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/AtFinish.lean: the proximity test (the kind K12) at its place on the first chain:
behind the last switch, in front of the members' places: the kind's block (Frame.lean) with its
parts joined (Join.lean; JoinGuarded.lean: the last part decides by the base case written anew, and every
part that is dealt rounds stands behind the guard on a drawn position's range), as a block over the
state that the first chain carries (Johnson/Desc/First/State.lean), by `Block.inside`. Definitions
with code; no theorem.
  enterFinish   reads out of the chain's state what the test needs at its front: the running record,
                the book of trees, the count of roots; the number of the group under test and the
                number of the message that holds the first fold's mask, which the last switch's
                place has laid into the finish's own part. It refuses unless the chain stands at its
                finish, no count of claims waits (`S.noneWaits`: a count of none at all and a count
                of 0 answer alike) and no test is marked as failed.
  leaveFinish   writes back the running record, the book and the count of roots. All else of the
                test's own record is dropped, and the finish's own part stays as it was in front.
Limits: the finish's own part has seven fields more, which the verifier program's steps fill inside
the test (answers, the present stage, the stages behind it, the claim, its layout, the mask, what
the last switch inside returned): here they keep the values that they had in front of the test. By
the state's own file nothing reads them behind the test. The count of claims that waits is left as
it came: where it came as a count of 0 it goes on as a count of 0. Nothing has run on a proof.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K12.JoinGuarded
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12
open VerifiableInference.Desc.First (S)

def enterFinish (s : S) : Except String T12 :=
  match s.here with
  | .fin o => do
    need "a count of claims is owed in front of the test" s.noneWaits
    need "a test is marked as failed in front of the test" s.failed.isNone
    pure { st := s.st, book := s.book, roots := s.roots, g := o.fr.group, pass := .nothing
           mask := o.mask }
  | _ => .error "the chain does not stand at its finish"

def leaveFinish (s : S) (t : T12) : Except String S :=
  .ok { s with st := t.st, book := t.book, roots := t.roots }

/-- **The proximity test at the first chain's finish.** -/
def atFinish (p : P12) : Block S Unit := (proximityTestKind guardedProximityTestParts p).inside enterFinish leaveFinish

end VerifiableInference.Desc.K12
