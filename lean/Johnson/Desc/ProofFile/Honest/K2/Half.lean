-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Half.lean: the honest side of the kind "the code switch" (K2), in
the form of Honest/Frame.lean: THE HALF AT A PLACE, AND THE PLACES OUT OF THE PLAN's PUBLIC DATA. It
defines part of the honest prover. Definitions with code; no theorem. Its tests stand in
Honest/K2/Toy.lean and Honest/K2/ToyAddr.lean, which this library may not hold.

  `SwitchPlace`, `SwitchPlace.carries`, `SwitchPlace.ownAddr`   a place's public data; the stretches
                  that its part carries; the address of an own message of the switch's own sending
  `asRow`         an entry of the data as a row of its field takes it
  `Closing`, `switchWit`   what the part reads of the prover's input
  `switchHalf`    the kind's half: a row of one part
  `frontBy`, `frontOf`, `switchPlaces`   the places of the kind, each with its data, out of the
                  planner's sizes (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean); the addresses:
                  Honest/K2/Seat.lean
  `switchHalves`  the halves at all places of the kind

THE DATA OF THE SEGMENTS' OWN MESSAGES IS THE FRAME's ONE FUNCTION (`RowData`, Honest/RowData.lean),
called at an address: the part that holds the message's sending, and its number in that sending.
  `D`         that function, of the public instance (`RowDataOf`): a parameter; whoever fills it is
              named there
  `readers`   the frame's readers, of the prover's input
TWO LETTERS, neither of them written here.
  `Sd`        the shared sending (Honest/K2/Part.lean)
  `closing`   what the fold that closed the group in front leaves: of the filling at the instance,
              the readers, the challenges in front of the part and the carried stretches

What is read of the input: what `D.entry` reads through the readers, at the next segment's own
messages of moment 0 (here) and at the own messages of all segments in front (the closing).
THE SWITCH's OWN SENDING's DATA IS ASKED AT NO CHALLENGE: `switchWit` hands `D.at_` the empty list:
so a filling lays `heardAt := 0` at a message of moment 0; the lot's closing asks `D.readyAt` there
and refuses otherwise (Honest/K2/AtPlan.lean, which this library may not hold).

What is carried. The closed group's rows hang on the coins of its members and of its fresh mask. One
member is the carrying message of the switch in front, which holds what the fold before left: so
they hang on the coins of the group before, and so on back. A part at segment l therefore carries
ONE STRETCH FOR EACH ORACLE MESSAGE THAT THE SEGMENTS 0 TO l - 1 HAVE SENT, in the order of sending,
but for what rides at the start of segment 0, which belongs to no segment's group.

Limits. Honest/K2/Seat.lean's. The order of the carried stretches is this file's own.
`switchPlaces` hands the targets' shapes as the kept members' (`Sizes.kept`). `switchPlaces` and
`switchHalves` want the public files' data: no test in this file evaluates them. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Part
import Johnson.Desc.ProofFile.Honest.K2.Seat
import Johnson.Desc.ProofFile.Lot.K2

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K2.Honest (Left Sizes zeroG)

variable {W₀ Rc Xi Tr X : Type}

/-! ## 1 The half -/

/-- **A place's public data**, for the honest side. -/
structure SwitchPlace where
  place : Place
  /-- the number of the group into which the switch leads: the next segment's; behind the last
  segment the number of segments -/
  link : Nat
  sizes : Sizes
  /-- the next segment's own messages of moment 0, then the next fold's fresh mask -/
  others : Array OnBytes.OracleNotice
  /-- the next fold's row variables -/
  foldVars : Nat
  /-- the oracle messages whose coins the part carries: the sender's address, the message's number
  in its sending, its coins -/
  front : List (Addr × Nat × Due)
  /-- the address of an own message of a segment in front: segment, the message's number among the
  segment's own -/
  addrs : Nat → Nat → Option MsgAddr

/-- The stretches that the part at the place carries, by name and count. -/
def SwitchPlace.carries (p : SwitchPlace) : List (String × Due) :=
  p.front.map fun x => (carriedName x.1 x.2.1 ⟨p.place, 0⟩, x.2.2)

/-- The address of the own message number m of the switch's own sending: behind the carrying message
and the copies. -/
def SwitchPlace.ownAddr (p : SwitchPlace) (m : Nat) : MsgAddr :=
  ⟨⟨p.place, 0⟩, 1 + p.sizes.kept.length + m⟩

/-- What the fold in front leaves, as the half is handed it: a letter. -/
abbrev Closing : Type :=
  SwitchPlace → RowData → Readers → List Fmt.Drawn → (Nat → Except String Stretch) →
    Except String Left

/-- **An entry as a row of its field takes it**, AS THE SHARED SENDING DOES (`K1.rowsR`,
Honest/K1/Coins.lean): over the extension field an element of either field; over the base field an
element of the base field alone: there an element of the extension field counts as none. Else 0. -/
def asRow (overE : Bool) : Option (Cb.Gl.F ⊕ Cb.Gl.E) → Cb.Gl.E
  | some (.inl x) => asE (some (.inl x))
  | some (.inr x) => if overE then x else zeroG
  | none => zeroG

/-- What the part reads of the prover's input: through the readers alone; the filling is applied to
the input's public instance. -/
def switchWit (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing)
    (p : SwitchPlace) (w : Local W₀ Rc Xi Tr) : SwitchAsk :=
  ⟨closing p (D w.x) (readers w), fun m b j =>
    asRow ((p.others.getD m default).shape.mainDeg == 3)
      ((D w.x).at_ (readers w) [] (p.ownAddr m) b j)⟩

/-- **The kind's half**: a row of one part of two rounds. -/
def switchHalf (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) :
    KindHalf SwitchPlace (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun p => ⟨p.place,
    [(switchPart Sd p.sizes p.others p.foldVars p.carries).lift (fun _ => ())
      (switchWit D readers closing p) (fun _ => ()) fun x _ => x]⟩

/-! ## 2 The places, out of the plan's public data -/

/-- **The oracle messages that segment k has sent**, each with its coins: `sentBy`
(Honest/K2/Seat.lean) with the counts. -/
def frontBy (codes : OnBytes.Codes) (f₀ : OnBytes.ReqFrame) (sps : List Spot) (k : Nat) :
    List (Addr × Nat × Due) :=
  (sentBy f₀ sps k).map fun x =>
    let fresh :=
      if x.2.2.2 == 0 then some (headCount f₀ k + ownFirst f₀ k, (f₀.groups.getD k {}).k) else none
    (x.1, x.2.1, messageDue codes x.2.2.1.shape (foldAt fresh x.2.1))

/-- **Those that the segments 0 to l - 1 have sent.** -/
def frontOf (codes : OnBytes.Codes) (f₀ : OnBytes.ReqFrame) (sps : List Spot) (l : Nat) :
    List (Addr × Nat × Due) :=
  (List.range l).flatMap (frontBy codes f₀ sps)

/-- **The places of the kind, each with its data.** None where the planner's sizes are not tied to
the chain's, or the table of steps has a word that is not known. -/
def switchPlaces (Z : Pub) (G : Ground) : List SwitchPlace :=
  match P1K2.prepOf Z G, spotsOf Z.cuts with
  | some P, some sps =>
    let f₀ : OnBytes.ReqFrame := { shape := P.z.request, groups := OnBytes.reqGroups P.z.request }
    (sps.filter fun sp => sp.place.kind == .K2).map fun sp =>
      let l := sp.place.link.getD P.z.request.link.length
      let T := (f₀.groups.getD l {}).target
      { place := sp.place, link := l
        sizes := ⟨P.z.codes, P.z.request.code, P.z.request.maskCode, T.kept.toList.map (·.shape), T⟩
        others := OnBytes.ReqFrame.notices ({ f₀ with link := l }.atMoment 0) ++
          #[OnBytes.foldMaskNotice (f₀.foldShape l {})]
        foldVars := (f₀.groups.getD l {}).k
        front := frontOf P.z.codes f₀ sps l
        addrs := addrOf f₀ sps }
  | _, _ => []

/-- **The kind's halves at all its places.** No lot: the one lot of the kind stands in
Honest/K2/AtPlan.lean, which this library may not hold. -/
def switchHalves (Sd : Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (Z : Pub) (G : Ground) :
    List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  (switchPlaces Z G).map (switchHalf Sd D readers closing)

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.SwitchPlace
#print axioms ProofFile.Honest.K2.SwitchPlace.carries
#print axioms ProofFile.Honest.K2.SwitchPlace.ownAddr
#print axioms ProofFile.Honest.K2.Closing
#print axioms ProofFile.Honest.K2.asRow
#print axioms ProofFile.Honest.K2.switchWit
#print axioms ProofFile.Honest.K2.switchHalf
#print axioms ProofFile.Honest.K2.frontBy
#print axioms ProofFile.Honest.K2.frontOf
#print axioms ProofFile.Honest.K2.switchPlaces
#print axioms ProofFile.Honest.K2.switchHalves
