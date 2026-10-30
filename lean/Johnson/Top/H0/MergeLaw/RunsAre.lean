-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsAre.lean: two named premises for the laws that carry the readers of nine
runs of claims across the accepting step of the merge of the claims on the committed table
(`RunsPass`, KeepAtMerge.lean). Definitions; one small theorem, a negative test.

Why. The reader of a run is the run itself, as the segment states it under its name, called at the
state (`readerOf`, Johnson/Desc/First/Batch/ReaderOf.lean). A law on a reader therefore wants to
know which run the segment states. That is a fact on the segment, not on the merge: it is named
here, a run a field, and shown here of no segment. In the first chain as it is made each run stands
behind a guard that rejects where the run has turned the reply that was heard; so a field does not
say "the stated run is the kind's own run" but the two halves that such a guarded run meets.

Main names:
  `RunIs l k name own`: the segment l states a run under that name at its place number k (from 0);
    where that run accepts, `own` accepts with the same answer; where `own` accepts and leaves the
    reply, that run accepts with the same answer. These are the premises hf, fwd and bwd of
    `reader_rides_own` (Johnson/Desc/Kinds/Law/ReaderRides.lean), sign for sign, under one "there
    is" for the stated run.
  `OwnIs l X iU3 name`: the like at one of the output head's three own runs: `own` is what the
    kind's sub-protocol states under the name (the premise hrun of `reader_rides_own`). The two
    numbers 24 and 4 in it (the segment's, the place's from 1) are idle: the kind's runs read
    neither (Johnson/Desc/Kinds/HeadKind.lean).
  `RunsAre l X iU3 lm`: THE NINE, a run a field. The number in a field's name is the place's number
    in the segment, from 0. X: the public parameters. iU3: the number of the reads' array. lm: the
    planes' matrix has 2 ^ lm rows.
  `speaksAt l k name s`: A TEST WITH CODE: the stated run's own reader answers at the state s.
  `Speaks l s`: that test at the five runs that read the reads' tables.
  `speaksAt_rejects`: a negative test: where no ledger is open `speaksAt` rejects, at every
    segment, place and name. That is not the case for which `Speaks` stands (a state of the output
    head's segment without the reads' tables): a rejection there hangs on the stated runs, and is
    for an evaluation at such a state, not for this file.

Why `Speaks`. At the output head's segment the readers have a second arm: where the stated run's
own reader is silent, the same reader is asked at the state with the reads' tables laid in thought
(`k6Silent`, Johnson/Desc/Kinds/Law/K6SilentCode.lean). A law "what the reader answers in front it
answers behind" would there need that the first arm is silent behind as well. `Speaks` shuts that
case out at the state in front.

Which runs stand on the right. "objects" and "guests": the two runs that the lookup's sub-protocol
states (`Law.blockVia`, Johnson/Desc/First/Look/Via/Via.lean), at the seat of the calls (place 2)
and of the digits (place 7). The list of guests is empty: `theOwn`
(Johnson/Desc/First/Look/K3Own.lean) hands `blockVia` the list [], and `theWhole`, `theStated` and
`K3Lot.hear` (K3Whole.lean, K3Stated.lean, Johnson/Desc/ProofFile/Lot/K3.lean) take that
sub-protocol's runs as they are. "planes": `withCaller` at the output head's readers, as
`K3Lot.readersAt` lays them at the head's segment. "join" and the three own runs: as `blockClaims`
(Johnson/Stored/HeadAddsAtS.lean) lays them. `K3Lot.ofForm` is `asClaim` in other letters.

Limits. Nothing is shown here of a segment or of a state. iU3 and lm are free letters here, and that
the right sides are the made chain's runs is, in this file, by reading of the files named above.
`RunsAre` is shown in another file of segment 24 of the first chain as it is made, in scope, at an
opening, with iU3 and lm tied to the public parameters (`runsAre_at_link24`, RunsAreAtLink.lean).
AN EVALUATION, NO THEOREM: over another state of the library, at one honest full-size run over
synthetic weights, the term of `speaksAt`, typed out, has been seen to accept at the five runs of
`Speaks` at the state in front of the merge, and to reject at all five four borders in front of it.
Nothing on soundness.

-/
import Johnson.Desc.First.Batch.ReadersOfLink
import Johnson.Top.H.Keep.K3Block
import Johnson.Stored.HeadAddsAtS
import Johnson.Desc.Kinds.Law.RowRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (statesOfLink readerOf)
open VerifiableInference.Desc.Kinds.Head (kind asClaim seatAt parOf planesAt callerReaders
  callerKeys)
open VerifiableInference.Desc.Kinds.Head.Law (workOf)
open VerifiableInference.OnPublicFiles (objectsRun guestsRun)

/-- The segment states a run under the name at place number k, and that run answers as `own` does:
wherever it accepts; and wherever `own` accepts and leaves the reply that was heard. -/
def RunIs (l : Link S Claim) (k : ℕ) (name : String)
    (own : ℕ → S → Except String (List Claim × S)) : Prop :=
  ∃ run : ℕ → S → Except String (List Claim × S),
    ((statesOfLink l k).find? fun r => r.1 == name) = some (name, run) ∧
      (∀ n t y, run n t = .ok y → own n t = .ok y) ∧
      ∀ n t y, own n t = .ok y → y.2.out.reply = t.out.reply → run n t = .ok y

/-- The like at one of the output head's own runs. -/
def OwnIs (l : Link S Claim) (X : OnBytes.Model.Verify.Public) (iU3 : ℕ) (name : String) : Prop :=
  ∃ own : ℕ → S → Except String (List Claim × S),
    (kind asClaim (seatAt X.hS iU3) 24 4 (parOf X.hS (workOf X))).claims.lookup name = some own ∧
      RunIs l 3 name own

/-- **Which runs the segment states: the nine, a run a field.** -/
structure RunsAre (l : Link S Claim) (X : OnBytes.Model.Verify.Public) (iU3 lm : ℕ) : Prop where
  objects2 : RunIs l 2 "objects" (objectsRun (K3.seatCalls asClaim))
  guests2 : RunIs l 2 "guests" (guestsRun ([] : List (Look.Guest S Claim)))
  planes2 : RunIs l 2 "planes"
    (K3.planesRun (K3.seatCalls asClaim) lm (callerReaders (planesAt iU3)))
  join3 : RunIs l 3 "join"
    (K3.joinRun (K3.seatCalls asClaim) (callerKeys (parOf X.hS (workOf X)) (seatAt X.hS iU3)))
  norm3 : OwnIs l X iU3 "norm"
  policy3 : OwnIs l X iU3 "policy"
  logits3 : OwnIs l X iU3 "logits"
  objects7 : RunIs l 7 "objects" (objectsRun (K3.seatDigits asClaim))
  guests7 : RunIs l 7 "guests" (guestsRun ([] : List (Look.Guest S Claim)))

/-- A test with code: the stated run's own reader answers at the state. -/
def speaksAt (l : Link S Claim) (k : ℕ) (name : String) (s : S) : Bool :=
  (readerOf (statesOfLink l) k name s).isSome

/-- **The stated run's own reader answers**, at the five runs that read the reads' tables. -/
structure Speaks (l : Link S Claim) (s : S) : Prop where
  planes2 : speaksAt l 2 "planes" s = true
  join3 : speaksAt l 3 "join" s = true
  norm3 : speaksAt l 3 "norm" s = true
  policy3 : speaksAt l 3 "policy" s = true
  logits3 : speaksAt l 3 "logits" s = true

/-- A negative test: where no ledger is open the test rejects. -/
theorem speaksAt_rejects (l : Link S Claim) (k : ℕ) (name : String) {s : S}
    (h : s.fork? = none) : speaksAt l k name s = false := by
  unfold speaksAt readerOf
  cases (statesOfLink l k).find? fun r => r.1 == name with
  | none => rfl
  | some r =>
    rw [h]
    simp only [Option.bind_some]
    cases r.2 0 s <;> rfl

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.speaksAt_rejects
