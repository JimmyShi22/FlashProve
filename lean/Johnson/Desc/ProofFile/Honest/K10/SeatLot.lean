-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SeatLot.lean: the lot's honest side with the closing's halves laid in, at
the first chain's types: the terms of this folder's files, and the shared texts that they call, in one
term; what is still open stands as three named parameters. This file defines part of the honest prover.
Definitions with code; no theorem; no test line.

The shared texts that are called.
  what the fold's rounds send      `foldWords` (Honest/K10/Words.lean, over Johnson/Prover/Link/FoldWordsE.lean)
  the group's rows, each member in full   `groupRowsOf` (Honest/K2/Closing.lean), through `jobRows`
                                   (Honest/K10/SegmentClosing.lean)
  what is public of the segments; a fresh mask's table   `segmentsOf`, `freshTable` (Honest/K2/AtPlan.lean)
  the address of a segment's own message   `addrOf` (Honest/K2/Seat.lean)
  the main rows of a segment's own messages outside the pads   `ownBy` (Honest/K2/AtPlan.lean): the one call
                                   `RowData.at_` (Honest/RowData.lean), read as a row of its field takes it
    a fold's challenges, or a refusal   `challengesAt` (Honest/K2/Closing.lean), through `heardAll`
  the refusals in front of these rows   `ownReady` (Honest/K2/AtPlan.lean): a message without an address; an
                                   array that the layout lays and the filling does not; data that are
                                   not ready at what was heard
  how many coins a carried message has   `msgDue` (Honest/BookRows.lean), through `borneAt`
                                   (Honest/K10/BorneAt.lean)

  `addrsAt`    `addrOf` off Z and the ground G, as the code switch's places take it
  `askPlace`   `ownReady` is typed at a place of the code switch; of that place its first loop, over the
               segments' own messages, reads the addresses alone; its second loop goes over the messages of
               a switch's own sending: here there are none. This is such a place, with nothing else in it
  `jobBare`, `heardAll`, `jobAt`   the job of a place: `jobRows` at these (`jobBare`); in front of its rows two tests,
                   both on public data and what was heard: `ownReady`; and `heardAll`, which is this file's: every
                   challenge of the folds in front has been heard: `challengesAt`, walked here over the segments but the
                   last. Why the second: `segmentLeft` (Honest/K2/Closing.lean) does not refuse there: it lays 0 for a
                   challenge that lacks or drew no element (`challengesOr0`: "For a caller that must return at every
                   list of challenges"), and its head says where that 0 can flow. `challengesAt`, "which no step calls,
                   still refuses on what was heard". `closeAsk` can refuse: so it asks, and no table is folded at a 0 in
                   silence (Limits)
  `borneSameAt`, `borneSame`   a test with code, for whoever lists the halves: the carried list of this folder
               (`borneAtOf`) is, entry for entry, sender, number and count, the code switch's list of what
               the segments have sent (`frontOf`, `frontBy`, Honest/K2/Half.lean) without the closing's own
               fresh mask; at a segment; at all segments off the public part
  `foldAt`     the fold's part at a place, with the older caller: `closeFold` at that job. Not the row's: `foldAtT`
               (Honest/K10/SimSeat.lean)
  `seatLot`    the lot's entry (`K9.closeLot`, Honest/K9/Lot.lean) with `borneAt` laid in and the fold's part
               seated: open are the small record off the input and the fold's part; not called by `seatLotT`
  `seatLotR`   the same with `foldAt` laid in: the older caller's: not to be laid: the lot with the row's part is
               `seatLotT` (Honest/K10/SeatLotT.lean). The three parameters that are left, there as here:
                 readers  the readers off the prover's input (cells, index, the index committer's coins)
                 rows     the main rows' data, as a function of the public instance (`RowDataOf`): the
                          frame's type; filled message by message, where the kinds that define the messages are written
                 stAt     the verifier's statement in front of "BAT": of the public instance, the place's numbers, and
                          what was shown and drawn (`StAtOf`, Honest/K10/Seat.lean): the seat lays it at the input's own
                          instance into the small record, and the job reads it there. A filler that is to be laid in no
                          lot yet: `stAtFirst` (see the head of Honest/K10/StAt.lean)

Limits. `addrsAt`, `foldAt`, `seatLot`, `seatLotR`, `borneSame` are run by no line: they want the public data of a real
description. Two texts for one thing, twice. The carried runs (`borneAt`) are listed by this folder's own text off the
request's shape; the order in which `groupRowsOf` asks for them comes off `segmentsOf`, which reads the verifier's own
list of what a sending holds. And the part that holds a sending is found here by the book's cut of a place's rounds
(`sendersIn`, Honest/K10/BorneAt.lean), there as part 0 of a place of the two sending kinds (`sendersOf`,
Honest/K2/Seat.lean). (`prepOf` asks that the planner's shape and codes are the ground's (G.first) and the first
state's; `borneAt` and `borneSame` read Z.first: that G.first is Z.first is asked by nobody here.) No theorem says that
the texts agree: `borneSame` is the test for it, asked by nobody here. Where it would say no, `jobRows` refuses by the
number of runs, or `groupRowsOf` by a run's count; two runs of one count in each other's place would go unseen by these
two; a sender's address that differs is seen by neither: they read no address. `askPlace` leans on the text of
`ownReady` as it lies: if its first loop came to read another field of the place, a default would go in without a word.
`ownReady` is handed the closed segment too, and its words, which are handed on unturned, speak of "a segment in front".
`heardAll` leans on the text of `groupRowsOf` as it lies: it writes that text's walk a second time (the segments but the
last; each one's `gamma`; the list in front): that these are places at which `challengesOr0` is called is read there and
shown by no theorem; that of what was heard `groupRowsOf`'s value hangs on nothing beyond these is had of the walk that
it calls, not of itself: `closingFrom_congr` (Honest/K10/Pay/XchCongr.lean), where each segment's first sending holds a
message, at two equal `own`, while `jobRows`' `own` is handed what was heard too; that, where the test passes, the two
readings of the challenges agree at each of these segments is shown by no theorem here. Its words too are handed on
unturned. `borneAt` yields a list also where `borneDue` says no: whoever lists the halves asks `borneDue`, `foldDueAll`
and `borneSame`. That the list of challenges which is handed to `RowData.at_` begins with what the message's sender had
heard is not shown (it is a first stretch of what the part has heard). `RowData`'s public fields, and `CloseIn.st`,
reach the part through its input's type: a law that needs them public goes back through `closeIn`. No property of the
protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SegmentClosing
import Johnson.Desc.ProofFile.Honest.K10.Words
import Johnson.Desc.ProofFile.Honest.K10.BorneAt
import Johnson.Desc.ProofFile.Honest.K10.Seat
import Johnson.Desc.ProofFile.Honest.K9.Lot
import Johnson.Desc.ProofFile.Honest.K2.AtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (SegmentPub SwitchPlace segmentsOf freshTable)

/-- **The address of a segment's own message**, off Z and the ground G: as `switchPlaces`
(Honest/K2/Half.lean) lays it. None where the planner's sizes are not tied to the chain's, or the table of
steps has a word that is not known. -/
def addrsAt (Z : Pub) (G : Ground) : Nat → Nat → Option MsgAddr :=
  match P1K2.prepOf Z G, spotsOf Z.cuts with
  | some P, some sps =>
    ProofFile.Honest.K2.addrOf { shape := P.z.request, groups := OnBytes.reqGroups P.z.request } sps
  | _, _ => fun _ _ => none

/-- A place of the code switch that holds the addresses and nothing else: no message of a sending of its
own. -/
def askPlace (addrs : Nat → Nat → Option MsgAddr) : SwitchPlace :=
  { place := default, link := 0, sizes := ⟨{}, 0, 0, [], default⟩, others := #[], foldVars := 0
    front := [], addrs := addrs }

/-- The job of a place without the two tests in front of its rows: `jobRows` at the shared texts. No half calls it: it
is `jobAt`'s inner term, by name, so that a line can show what the tests do. -/
def jobBare (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub)
    (stAt : CloseIn → Seen → List Fmt.Drawn → Except String (Statement × Nat)) (pub : ClosePub) :
    CloseJob CloseIn :=
  jobRows pub freshTable segs stAt fun (w : CloseIn) heard =>
    ProofFile.Honest.K2.ownBy w.data w.readers addrs
      (fun s m => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) heard

/-- **A public test: every challenge of the folds in front has been heard**: `challengesAt` (Honest/K2/Closing.lean),
which refuses where a challenge lacks or drew no element, at each segment but the last: these are the segments whose
folds `groupRowsOf` walks. -/
def heardAll (segs : List SegmentPub) (front : List Fmt.Drawn) : Except String Unit :=
  (segs.dropLast.mapM fun S => ProofFile.Honest.K2.challengesAt front S.gamma).map fun _ => ()

/-- **The job of a place.** segs: what is public of the segments 0 .. the place's. -/
def jobAt (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr)
    (segs : List SegmentPub)
    (stAt : CloseIn → Seen → List Fmt.Drawn → Except String (Statement × Nat))
    (pub : ClosePub) : CloseJob CloseIn :=
  { jobBare addrs segs stAt pub with
    rows := fun w front ca =>
      (ProofFile.Honest.K2.ownReady w.data lay (askPlace addrs) segs front).bind fun _ =>
        (heardAll segs front).bind fun _ => (jobBare addrs segs stAt pub).rows w front ca }

/-- **The carried list at segment l is the code switch's** (`frontOf`, `frontBy`, Honest/K2/Half.lean): all that the
segments 0 .. l - 1 have sent, and of segment l all but the closing's own fresh mask, which stands behind the carrying
message, the copies and the own messages of moment 0: sender, number in the sending, count. -/
def borneSameAt (s : OnBytes.Params.ReqShape) (codes : OnBytes.Codes)
    (xs : List (Spot × List Fmt.DeclaredRound × Nat)) (sps : List Spot) (l : Nat) : Bool :=
  let f₀ : OnBytes.ReqFrame := { shape := s, groups := OnBytes.reqGroups s }
  (borneAtOf s codes xs l).map (fun b => (b.sender, b.msg, b.count)) ==
    ProofFile.Honest.K2.frontOf codes f₀ sps l ++ (ProofFile.Honest.K2.frontBy codes f₀ sps l).eraseIdx
      (ProofFile.Honest.K2.headCount f₀ l + ProofFile.Honest.K2.ownFirst f₀ l)

/-- **The same at all segments, off the public part.** No where the table of steps has a word that is not known; else
yes at a shape with no segment. -/
def borneSame (Z : Pub) : Bool :=
  match spotsOf Z.cuts with
  | some sps => (List.range Z.first.shape.link.length).all
      (borneSameAt Z.first.shape Z.first.codes (k9Stretches Z) sps)
  | none => false

/-- **The fold's part at a place**, off Z and the ground G: with the older caller (`closeFold`): not the row's: the
row's is `foldAtT` (Honest/K10/SimSeat.lean). -/
def foldAt {V X : Type} (Z : Pub) (G : Ground) : ClosePub → Part V CloseIn X :=
  fun pub => closeFold (jobAt G.first.layout (addrsAt Z G) ((segmentsOf Z G).take (pub.par.link + 1))
    (fun i => i.st pub.par) pub)

/-- **The lot's honest side, seated**: the fold's part is a parameter. Not called by `seatLotT`
(Honest/K10/SeatLotT.lean), the lot to lay. -/
def seatLot {W₀ Rc Xi Tr X : Type} (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (fold : ClosePub → Part Unit CloseIn Unit) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  K9.closeLot borneAt (seatFold inOf fold)

/-- **The same with the fold's part laid in**: the older caller's. Not to be laid: lay `seatLotT`
(Honest/K10/SeatLotT.lean). Called by nothing in this folder. -/
def seatLotR {W₀ Rc Xi Tr X : Type} (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  K9.batLot fun Z g => seatClosings (closeIn readers rows stAt) borneAt (foldAt Z g) Z g

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.addrsAt
#print axioms ProofFile.Honest.K10.askPlace
#print axioms ProofFile.Honest.K10.jobBare
#print axioms ProofFile.Honest.K10.heardAll
#print axioms ProofFile.Honest.K10.jobAt
#print axioms ProofFile.Honest.K10.borneSameAt
#print axioms ProofFile.Honest.K10.borneSame
#print axioms ProofFile.Honest.K10.foldAt
#print axioms ProofFile.Honest.K10.seatLot
#print axioms ProofFile.Honest.K10.seatLotR
