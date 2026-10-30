-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/AtPlan.lean: the honest side of the kind "the code switch" (K2):
THE SEGMENTS' PUBLIC DATA OUT OF THE PLAN, AND THE KIND's ONE LOT, over the sending
(Honest/K2/Sending.lean), the closing (Honest/K2/Closing.lean) and the frame's one function for the
data of the segments' own messages (`RowData`, Honest/RowData.lean). It defines part of the honest
prover. Definitions with code; no theorem.

  `segmentsOf`    each segment's `SegmentPub`
  `freshTable`    a fold's fresh mask's table, of the hiding polynomial's coefficients: THE SHARED
                  SENDING's OWN (`K1.Ride.lay`, Honest/K1/Coins.lean), which lays it by the format's
                  model prover's packing
  `SegmentPub.ownShapes`   the shapes of a segment's own messages, by their number in the segment
  `ownBy`         the main rows of a segment's own messages: segment, the message's number among the
                  segment's own, row, place: `asRow` (Honest/K2/Half.lean) of `D.at_` at the
                  message's address
  `arraysLaid`    a public test: of EACH ARRAY that the layout lays into the message, `D` lays an
                  element somewhere (the way back off the layout: `laidBack`, Honest/LaidData.lean)
  `ownReady`      a refusal unless each own message of the segments in front has an address, each
                  of its arrays is laid, and its data is ready at the challenges heard; and the like
                  of each own message of the switch's own sending, at no challenge: FOR A CALLER
                  THAT CAN REJECT
  `ownLaid`, `ownHeard`   its two halves: the first, on public data alone, is what the lot's closing
                  asks; the second, on the challenges heard, is a test with code that no move asks
  `switchLot`     THE KIND's ONE LOT

WHAT THE LOT TAKES: `D : RowDataOf Xi` (the filling, of the public instance) and `readers`, the
frame's. No other letter.

WHERE A 0 CAN STILL STAND IN. `ownBy` is a plain function: it yields 0 where a message has no
address and where `D.lays` says no, and `D.entry`'s value means nothing where `D.ready` says no. The
lot's closing asks `ownLaid` first and refuses: no address; an own message of the switch's own
sending whose data reads a challenge; AN ARRAY THAT THE LAYOUT LAYS INTO THE MESSAGE AND OF WHICH
`D` LAYS NO ELEMENT (so at `RowData.empty` the lot refuses wherever the layout lays an array, and a
filling that lays some of a message's arrays and not the others is refused). A message into which
the layout lays no array is lawful (`reqMessageLaid`, Johnson/Desc/Own/Req.lean): nothing is asked
there, and its entries outside the pad are 0 by the format's own rule. NOT CAUGHT: a filling that
lays some elements of an array and not the others. NOT ASKED BY THE LOT's CLOSING: THAT THE DATA OF
THE MESSAGES IN FRONT IS READY AT THE CHALLENGES HEARD (`ownHeard`): a move must return wherever a
run stands, so it calls `D.at_`, as Honest/RowData.lean bids a caller that must stay total; the test
is a premise of whoever says what the rows are. What `D.entry` yields where it is not ready stands
where the data stands: at entries of main rows that are no pad's; it reaches no coin's place (the
head of Honest/K2/Closing.lean).

Which challenges a fold's are. The chain's challenges are counted with its rounds, from 0. A
segment's closing has as many rounds "FOLD round" as its group has row variables, and the segments
close in order: so segment j's are the next k_j of the chain's rounds of that name. The last
proximity test's rounds of the name come behind all of them.

Limits. That a run's list of challenges has one entry a round is the frame's. Nothing holds the
rounds' numbers against the table of steps. The kept copies' rows are taken off what the fold in
front left, not off `D`. No test in this file evaluates `segmentsOf` or `switchLot`: they want
the public files' data. The lot's name is written here a second time (the first:
Johnson/Desc/ProofFile/Lot/K2.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Desc.ProofFile.Honest.K2.Closing
import Johnson.Desc.ProofFile.Honest.K2.Rounds
import Johnson.Desc.ProofFile.Honest.LaidData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc.K2.Honest (Sizes zeroG)

variable {W₀ Rc Xi Tr X : Type}

/-- **Each segment's public data.** None where the planner's sizes are not tied to the chain's. -/
def segmentsOf (Z : Pub) (G : Ground) : List SegmentPub :=
  match P1K2.prepOf Z G with
  | none => []
  | some P =>
    let f₀ : OnBytes.ReqFrame := { shape := P.z.request, groups := OnBytes.reqGroups P.z.request }
    let ks := P.z.request.link.zipIdx.map fun L => (f₀.groups.getD L.2 {}).k
    P.z.request.link.zipIdx.map fun L =>
      let j := L.2
      let T := (f₀.groups.getD j {}).target
      let own := ({ f₀ with link := j }.atMoment 0).length
      { sizes := ⟨P.z.codes, P.z.request.code, P.z.request.maskCode, T.kept.toList.map (·.shape), T⟩
        sent := (List.range (OnBytes.reqMoments L.1)).map fun m =>
          -- what rides at the start stands behind the first segment's fresh mask: cut off
          if j == 0 && m == 0 then (P1K2.noticesAt f₀ j m).extract 0 (own + 1)
          else P1K2.noticesAt f₀ j m
        ownKept := L.1.messages.map fun m => decide (0 < m.life)
        foldVars := ks.getD j 0
        gamma := ((roundNumbers Z.D.1 "FOLD round").drop ((ks.take j).foldl (· + ·) 0)).take
          (ks.getD j 0) }

/-- **The table of a fold's fresh mask**: the shared sending's own. -/
def freshTable : FreshTable := fun k h c r j => (⟨k, h⟩ : K1.Ride).lay c r j

/-- The shapes of a segment's own messages, by their number in the segment. first: it is the first
segment: no carrying message and no copy stand in front. -/
def SegmentPub.ownShapes (S : SegmentPub) (first : Bool) : List OnBytes.OracleShape :=
  let head := if first then 0 else 1 + S.sizes.kept.length
  let one := (S.sent.headD #[]).toList
  (((one.take (one.length - 1)).drop head) ++ (S.sent.drop 1).flatMap (·.toList)).map (·.shape)

/-- **The main rows of a segment's own messages**, outside the pads: segment, the message's number
among the segment's own, row, place. shapes: the messages' shapes. 0 where the message has no
address. -/
def ownBy (D : RowData) (R : Readers) (addrs : Nat → Nat → Option MsgAddr)
    (shapes : Nat → Nat → OnBytes.OracleShape) (heard : List Fmt.Drawn) (seg m b j : Nat) :
    Cb.Gl.E :=
  match addrs seg m with
  | some a => asRow ((shapes seg m).mainDeg == 3) (D.at_ R heard a b j)
  | none => zeroG

/-- **A public test: each array that the layout lays into the message is laid by D**: at some row
and place where the layout has an element of that array, D lays an element. lay: the item "layout".
seg, m: the segment, and the message's number in its list. s: its shape. a: its address. Yes of a
message into which the layout lays no array. -/
def arraysLaid (D : RowData) (lay : OnBytes.Params.ReqLayout) (codes : OnBytes.Codes)
    (s : OnBytes.OracleShape) (seg m : Nat) (a : MsgAddr) : Bool :=
  ((lay.link.getD seg []).filter fun A => A.message == m).all fun A =>
    (List.range s.mainRows).any fun b =>
      (List.range (codes.base.getD s.code default).ell).any fun j =>
        D.lays a b j && (laidBack lay seg m b j).any fun x => x.1.name == A.name

/-- Each own message of these segments has an address, each of its arrays is laid, and its data is
ready at the challenges heard; the like of each own message of the switch's own sending, at no
challenge. -/
def ownReady (D : RowData) (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace)
    (segs : List SegmentPub) (heard : List Fmt.Drawn) : Except String Unit := do
  for x in segs.zipIdx do
    for s in (x.1.ownShapes (x.2 == 0)).zipIdx do
      match p.addrs x.2 s.2 with
      | none => throw "an own message of a segment in front has no address"
      | some a =>
        if !arraysLaid D lay x.1.sizes.codes s.1 x.2 s.2 a then
          throw "an array of a message in front is not laid"
        if !D.readyAt heard a then throw "the data of a message in front is not ready"
  for n in (p.others.toList.take (p.others.size - 1)).zipIdx do
    if !arraysLaid D lay p.sizes.codes n.1.shape p.link n.2 (p.ownAddr n.2) then
      throw "an array of a message of the switch's own sending is not laid"
    if !D.readyAt [] (p.ownAddr n.2) then
      throw "the data of a message of the switch's own sending reads a challenge"

/-- **The public half of that test**: `ownReady` without its clause on the challenges heard: of the
filling at the public instance, the layout and the place alone. -/
def ownLaid (D : RowData) (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace)
    (segs : List SegmentPub) : Except String Unit := do
  for x in segs.zipIdx do
    for s in (x.1.ownShapes (x.2 == 0)).zipIdx do
      match p.addrs x.2 s.2 with
      | none => throw "an own message of a segment in front has no address"
      | some a =>
        if !arraysLaid D lay x.1.sizes.codes s.1 x.2 s.2 a then
          throw "an array of a message in front is not laid"
  for n in (p.others.toList.take (p.others.size - 1)).zipIdx do
    if !arraysLaid D lay p.sizes.codes n.1.shape p.link n.2 (p.ownAddr n.2) then
      throw "an array of a message of the switch's own sending is not laid"
    if !D.readyAt [] (p.ownAddr n.2) then
      throw "the data of a message of the switch's own sending reads a challenge"

/-- **The other half, as a test with code**: the data of each own message of these segments is ready
at the challenges heard. NO MOVE ASKS IT: it is for whoever says what the rows are to name as a
premise. Yes of a message without an address. -/
def ownHeard (D : RowData) (p : SwitchPlace) (segs : List SegmentPub) (heard : List Fmt.Drawn) :
    Bool :=
  segs.zipIdx.all fun x =>
    (x.1.ownShapes (x.2 == 0)).zipIdx.all fun s =>
      ((p.addrs x.2 s.2).map (D.readyAt heard)).getD true

/-- **THE KIND's ONE LOT: its honest side**, under the name of the lot that seats the kind's blocks
(`P1K2.lot`, Johnson/Desc/ProofFile/Lot/K2.lean). -/
def switchLot (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  { name := "the code switch"
    halves := fun Z G =>
      let segs := segmentsOf Z G
      switchHalves (coreSender freshTable) D readers (fun p D R heard k =>
        (ownLaid D G.first.layout p (segs.take p.link)).bind fun _ =>
          closingFor freshTable (segs.take p.link) p.sizes.kept
            (ownBy D R p.addrs
              (fun s m => (((segs[s]?).map (·.ownShapes (s == 0))).getD []).getD m {}) heard)
            heard k)
        Z G }

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.segmentsOf
#print axioms ProofFile.Honest.K2.freshTable
#print axioms ProofFile.Honest.K2.SegmentPub.ownShapes
#print axioms ProofFile.Honest.K2.ownBy
#print axioms ProofFile.Honest.K2.arraysLaid
#print axioms ProofFile.Honest.K2.ownReady
#print axioms ProofFile.Honest.K2.ownLaid
#print axioms ProofFile.Honest.K2.ownHeard
#print axioms ProofFile.Honest.K2.switchLot
