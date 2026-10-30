-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K9/Fall.lean: K9's SHARE OF THE FALL, RUN FROM THE STATE IN FRONT OF THE
BATCHING: the form in which it is COUNTED over chi. Definitions with code; no theorem.

What a fall is (the frame's keeper's form): a test of the verifier's own, with code, on the verifier's
state in front of a member and that member's own challenges. It is handed no coin, no input and no
table. Where it speaks the verifier refuses. It is read by the sentence on acceptance, and by nothing
that plays. A FALL IS SEATED AT THE MEMBER THAT REFUSES: K9's share's seat is the frame's member behind
the batching: the test AT THAT SEAT is `quietFallTest` (Honest/K9/Quiet.lean). `batFallTest`, here, is
the same text run from the state in front of the member that draws (`batFall_is`, there).

Where the tests stand. A segment's flat list (`Link.blocksInOrder`, Johnson/Desc/Block.lean) has the batching
(K9: the draw and the whole adding, in one decision) and, right behind it, the frame's member
without a round "behind the batching" (`Link.runBehind`): the link's tests behind the adding, which
at the proof file's description are `k9Tests` (Johnson/Desc/ProofFile/Lot/K9.lean): "every sent
scalar stands in a claim" and the sort's counts; then the other kinds' runs behind the batching.

NO SECOND TEXT OF THE ADDING: the state behind the adding is made by the description's own member.
  `behindBat b s ds`   the state behind the member b, from s, at rounds in which nothing is sent and
                       ds is drawn, shown without the sealed digest, as `Block.step` shows them;
                       nothing where b refuses
  `slotsFree n s`      K9's own test on values, as a Bool on a state: `First.Door.freeSlotOk`, the
                       condition of `K9.freeSlot`, at the ledger and the merge's slot of s; true
                       where no segment is open (that refusal is not a test on values)
  `freeSlotShare`      K9's share of the fall's test: of the state behind the adding
  `batFallTest`        the test, as the frame's form takes it: another kind's share IN FRONT of the
                       member (of s and ds: for a test on values that refuses inside b's own
                       decision), then, of the state behind the adding, K9's share and another
                       kind's. The two others are parameters.
  `batFallAt`          at segment l of the proof file's description: the number of slots off the
                       public parameters, as `k9Tests` reads it
  `batFallShare`       A STATED NUMBER, NO BOUND: slots * top of |E|: for each slot BUT THE MERGE's at
                       most `top` values of chi, WHERE THAT SLOT's COEFFICIENT IS NOT THE ZERO
                       POLYNOMIAL IN chi. At the merge's slot the test asks the other way round: the
                       coefficient must BE 0: it is, at every chi, where no claim names that slot
  `batFallShareAt`     at segment l, off the public parameters as `k9Tests` reads it: slots: the slots that
                       the segment's messages fill (THE MERGE's SLOT IS COUNTED WITH THEM: one `top`
                       too many where there is a merge); top: the plan's number of claims, less one:
                       a claim that takes its own number c is added under chi^c, c below that
                       number. BY READING, NO THEOREM: the claims that are added under a higher
                       power (the smallness test's ties and reads) name no slot. |E|: the cube of
                       2^64 - 2^32 + 1

Limits. Where b itself refuses, K9's share says nothing: a refusal inside the adding is `front`'s.
`behindBat` does not ask the format's test on the rounds: at challenges that do not fit the round the
test may speak where `Block.step` says "the rounds". The stated share counts chi alone: at which
earlier challenges a slot's coefficient is the zero polynomial is not counted. No line of the toy
runs `batFallAt` or `batFallShareAt`: they want a public part (`Pub`). The counts of the segment's
sort are no tests on values and are not in the test. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K9.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K9
open VerifiableInference.Desc (Block noDigest)
open VerifiableInference.Desc.First (S)

variable {T Cl : Type}

/-- The state behind a member in whose rounds nothing is sent. -/
def behindBat (b : Block T Cl) (s : T) (ds : List Fmt.Drawn) : Option T :=
  (b.decide s (ds.map fun d => noDigest ⟨[], d⟩) []).toOption

/-- "Every sent scalar stands in a claim", as a Bool on a state. n: the slots that the segment's
messages fill. -/
def slotsFree (n : Nat) (s : S) : Bool :=
  match VerifiableInference.Desc.K9.tAtS.get? s with
  | some a => VerifiableInference.Desc.First.Door.freeSlotOk n a.merge a.F
  | none => true

/-- K9's share: of the state behind the adding. -/
def freeSlotShare (n : Nat) (s₁ : S) : Option String :=
  if slotsFree n s₁ then none else some "K9.free-slot"

/-- **The fall's test at the batching's round.** b: the description's own member at the batching's
place. front: another kind's share in front of b. other: another kind's share, of the state behind
the adding. -/
def batFallTest (b : Block S Cl) (n : Nat) (front : S → List Fmt.Drawn → Option String)
    (other : S → Option String) (s : S) (ds : List Fmt.Drawn) : Option String :=
  (front s ds).or ((behindBat b s ds).bind fun s₁ => (freeSlotShare n s₁).or (other s₁))

/-- At segment l of the proof file's description. Nothing is tested where the public parameters have no
plan for the segment. -/
def batFallAt (Z : Pub) (l : Nat) (b : Block S Cl) (front : S → List Fmt.Drawn → Option String)
    (other : S → Option String) (s : S) (ds : List Fmt.Drawn) : Option String :=
  (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).bind fun w =>
    batFallTest b w.2.2.filled front other s ds

/-- The stated share of K9's share. slots: the slots under test. top: the highest power of chi under
which a claim that names a slot is added. sizeE: the number of elements of the extension field. -/
def batFallShare (slots top sizeE : Nat) : Odds := ⟨slots * top, sizeE⟩

/-- The number of elements of the extension field: the cubic extension of the integers modulo
2^64 - 2^32 + 1. -/
def sizeOfE : Nat := (2 ^ 64 - 2 ^ 32 + 1) ^ 3

/-- The stated share at segment l. -/
def batFallShareAt (Z : Pub) (l : Nat) : Option Odds :=
  (VerifiableInference.Desc.K9.testsWhere Z.p.X l 0).map fun w =>
    batFallShare w.2.2.filled (w.2.1 - 1) sizeOfE

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.behindBat
#print axioms ProofFile.Honest.K9.slotsFree
#print axioms ProofFile.Honest.K9.freeSlotShare
#print axioms ProofFile.Honest.K9.batFallTest
#print axioms ProofFile.Honest.K9.batFallAt
#print axioms ProofFile.Honest.K9.batFallShare
#print axioms ProofFile.Honest.K9.sizeOfE
#print axioms ProofFile.Honest.K9.batFallShareAt
