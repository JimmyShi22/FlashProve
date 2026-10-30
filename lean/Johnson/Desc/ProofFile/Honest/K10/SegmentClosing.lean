-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SegmentClosing.lean: the job of the closing of a segment, with the group's rows
taken whole from the shared text that makes a segment's group's rows anew (`groupRowsOf`,
Honest/K2/Closing.lean; its head: "for whoever closes that group"). This file defines
part of the honest prover. Definitions with code; no theorem.

The kind lays no coin itself: where in a carried run a tail, a pad or a mask row's entry stands is that
text's (`messageRows`, Honest/K2/Sending.lean), for every sender of the chain and for this kind alike. What
that text refuses (its head lists it) is handed on aloud (`closeAsk`, Honest/K10/Job.lean; the row's part makes nothing
of a refusal: Job.lean's Limits). Three things are refused here, in front of it and under this kind's own words:
  codes that do not fit: a message that names a code which the chain has not; a segment whose own two numbers the
       codes lack; segments that do not all have one list of codes and one pair of numbers, or a message that names
       another code than its segment's
  a carrying message without room: a switch's target whose rest does not lie in main rows, whose block has fewer
       places than what a fold leaves beside the folded main row has entries, or whose main block is too short for
       the folded main row: the verifier's own test on a target has these clauses among its own
       (`switchTargetCheck`, OnBytes/Iop/Cs.lean)
  carried runs that are not as many as that text asks for: it asks for runs by number and never counts the list, so
       a run too many would go unseen
That text refuses much of this itself, by its tests `sentShapeFits`, `groupFits` and `Sizes.roomy`. Not refused there,
and refused here alone: segments that do not all have one list of codes and one pair of numbers; a message of the last
segment that names another code than its segment's; a switch's target whose rest does not lie in main rows (there that
text lays no rest); carried runs that are not as many as that text asks for.

  `segsKnown`  all these segments have the last one's list of codes and its two numbers; the codes have
               both numbers; every message names these two for the rows that it has
  `segsRoomy`  each segment but the first has a carrying message with room: by `Sizes.serves` (which asks the main
               block's part too) and the length of `rest` (Johnson/Desc/K2/Honest/Carrying.lean), and by the verifier's
               own count of the room (`SwitchPlaces.make`); the third clause, on the main block's length, is typed here
  `noLeft`     what a fold leaves, all 0: for the length of `rest`
  `runsAsked`  how many runs `groupRowsOf` asks for: every message of the segments in front; of the last
               segment every message but its own fresh mask
  `memberOf`   one member as the closing takes it: its shape and mark "kept"; its main rows' and its mask
               rows' messages, as the program's elements
  `jobRows`    the job of a place: `rows` := `groupRowsOf` at the carried runs, run by run. Its parameters:
               table  a fresh mask's table (read at the segments in front alone)
               segs   what is public of the segments, from the first to the one that is closed
               own    the main rows of a segment's own messages outside the pads: of the input and the
                      challenges in front of "BAT": segment, the message's number in the segment, row,
                      place

One more thing that that text does not refuse is not refused here either: a challenge of a fold in front that lacks or
drew no element: there it lays 0. So `jobRows` by itself yields rows folded at a 0 wherever a fold stands in front and
not all was heard. The lot's job asks in front of it (`heardAll` in `jobAt`, Honest/K10/SeatLot.lean). `jobBare`
(SeatLot.lean) is `jobRows` without that test. The toys call `jobRows` at one segment or none, where no fold stands in
front, and `jobBare`, on purpose, at two segments with a challenge lacking (Honest/K10/ToyTwo.lean, ToyWalk.lean).

Limits. The carried runs must stand in that text's order: segment by segment, in a segment in the order of sending, the
closed segment's own fresh mask left out. Nothing here holds `pub.borne` against `segs` but the number of runs, and, run
by run, that text's own test on each run's count (a test at two segments, at the list that Honest/K10/Carried.lean
makes: Honest/K10/ToyTwo.lean). Nothing holds `segs` against a plan here. `own` is a parameter. Refused only because two
counts differ there (the run's, by `msgDue`, Honest/BookRows.lean; that text's own): a pad too long for its row; a
message with main rows and no sample. No property of the protocol is claimed: nothing is said on its soundness,
completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Job
import Johnson.Desc.ProofFile.Honest.K2.Closing

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement)
open ProofFile.Honest.K2 (FreshTable SegmentPub groupRowsOf Stretch)

variable {W : Type}

/-- **One list of codes and one pair of numbers for all these segments, both numbers there, and every message
names them.** No at no segment. A request has one pair of codes for all its groups (`ReqFrame.beginLink`,
OnBytes/Iop/Req.lean). So what `rowsFit` holds against the statement at the last segment reaches all. -/
def segsKnown (segs : List SegmentPub) : Bool :=
  match segs.getLast? with
  | none => false
  | some Z =>
    (Z.sizes.codes.base[Z.sizes.code]?).isSome && (Z.sizes.codes.mask[Z.sizes.maskCode]?).isSome &&
    segs.all fun S =>
      S.sizes.codes == Z.sizes.codes && S.sizes.code == Z.sizes.code &&
        S.sizes.maskCode == Z.sizes.maskCode &&
        S.sent.all fun a => a.all fun n =>
          (n.shape.mainRows == 0 || n.shape.code == Z.sizes.code) &&
            (n.shape.maskRows == 0 || n.shape.maskCode == Z.sizes.maskCode)

/-- What a fold leaves, all 0: for the length of `rest`, which hangs on no value of it. -/
def noLeft : VerifiableInference.Desc.K2.Honest.Left :=
  ⟨fun _ => OnBytes.Slice.toE (0, 0, 0), fun _ => OnBytes.Slice.toE (0, 0, 0),
    fun _ _ => OnBytes.Slice.toE (0, 0, 0), fun _ _ => OnBytes.Slice.toE (0, 0, 0),
    fun _ => ⟨fun _ _ => OnBytes.Slice.toE (0, 0, 0), fun _ _ => OnBytes.Slice.toE (0, 0, 0)⟩⟩

/-- **Each segment but the first has a carrying message with room** for what the fold in front leaves: the
rest lies in main rows, with a target for each kept member; it has no more entries than its block has
places; the folded main row's message is no longer than the main block. -/
def segsRoomy (segs : List SegmentPub) : Bool :=
  (segs.drop 1).all fun S =>
    S.sizes.serves &&
      decide ((VerifiableInference.Desc.K2.Honest.rest S.sizes noLeft).length ≤
        (OnBytes.SwitchPlaces.make S.sizes.codes S.sizes.target).size) &&
      decide ((S.sizes.codes.base.getD S.sizes.code default).ell ≤
        (S.sizes.codes.base.getD S.sizes.target.shape.code default).ell * 2 ^ S.sizes.target.main.bits)

/-- **How many runs `groupRowsOf` asks for.** -/
def runsAsked (segs : List SegmentPub) : Nat :=
  (segs.map (·.messages)).sum - 1

/-- **One member, as the closing takes it.** -/
def memberOf (g : VerifiableInference.Desc.K2.Honest.GroupMember) (R : Johnson.Prover.Send.Rows) :
    MemberRows :=
  { shape := g.shape, kept := g.kept
    main := fun b p =>
      if g.shape.mainDeg == 3 then E.ofTriple (OnBytes.Slice.ofE (R.mainE b p)) else eOfF (R.mainF b p)
    mask := fun b p => E.ofTriple (OnBytes.Slice.ofE (R.mask b p)) }

/-- **The job of a place, the group's rows by the shared text.** -/
def jobRows (pub : ClosePub) (table : FreshTable) (segs : List SegmentPub)
    (stAt : W → Seen → List Fmt.Drawn → Except String (Statement × Nat))
    (own : W → List Fmt.Drawn → Nat → Nat → Nat → Nat → Cb.Gl.E) : CloseJob W :=
  { pub := pub, stAt := stAt
    rows := fun w front ca =>
      match segs.getLast? with
      | none => .error "K10: no segment is named"
      | some S =>
        if !segsKnown segs then .error "K10: the segments' codes do not fit"
        else if !segsRoomy segs then .error "K10: a carrying message has no room for what a fold leaves"
        else if pub.borne.length != runsAsked segs then
          .error "K10: the carried runs are not as many as the segments' messages"
        else
          (groupRowsOf table segs (own w front) front (Stretch.carried _ ca)).map fun R =>
            ⟨S.sizes.codes, S.sizes.code, S.sizes.maskCode,
              (R.members.zip R.rows).map fun x => memberOf x.1 x.2⟩ }

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.segsKnown
#print axioms ProofFile.Honest.K10.noLeft
#print axioms ProofFile.Honest.K10.segsRoomy
#print axioms ProofFile.Honest.K10.runsAsked
#print axioms ProofFile.Honest.K10.memberOf
#print axioms ProofFile.Honest.K10.jobRows
