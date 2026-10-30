-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaceFirst.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME
FOR THE HONEST SIDE: ITS FIRST PLACE: THE FIRST SEGMENT's OPENING (the place ⟨1, some 0, 1, .K1⟩ of
a proof file's description). Definitions with code, and four statements by unfolding.

  firstRide     which message's table rides, and at which public numbers: the fold's fresh mask,
                which stands behind the segment's own messages of moment 0: k and h of the shape of
                the fold that closes group 0: the terms of which the description's own text makes
                that message's notice (firstLaid, Johnson/Desc/K1/First.lean)
  firstAddr     the part's address: part 0 of the place
  firstFill     the data of the main rows: the filling firstData (Honest/K1/FirstData.lean) at the
                chain's own codes, shape and layout; nothing has been heard when the sending begins
  firstJobAt, firstJob   THE JOB, of the chain's parameters and the plan's two numbers; at the lot's
                own arguments: P: the lot's own call with the lot's own arguments (K1.firstPar
                G.first (K1.gpOf Z): Johnson/Desc/ProofFile/Lot/K1.lean, blocks) · first := 0: the
                chain's first two rounds are this place's, and the state in front holds no message
                (firstRecord, Johnson/Desc/First/State.lean) · ride := firstRide · data :=
                firstFill, read through the readers and what was heard in front alone
  firstSeatOk   THE SEAT's PUBLIC TEST: the job fits its place; at each of the segment's own
                messages the data is ready and none is laid at a pad's place
  firstHalf     the half at the place: the one part, seated by Part.lift in a wider input: of the
                four arguments three are the identity; wit makes the readers of the input
  firstLot      the lot's honest side, under the lot's name
  firstLot_name, firstHalf_place, lot_head, member_rounds   the name is the lot's own field · the
                place is the description's own member's · THE LOT's OWN FIRST MEMBER is K1.firstSegmentOpening
                at the arguments at which the job calls K1.firstPar · that member's rounds and
                oracle messages are those of the job's P

S: the model's sizes as the integer model has them (OnBytes.HonestTrace.Sz): public.

Limits. wit IS A LETTER: what makes the readers of a prover's input is not typed here. THE LOT HAS
MORE PLACES (each link's reads and digits): this side has a half at the first alone. That the sizes
S are those of the public files is not said. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.ProofFile.Honest.K1.FirstData
import Johnson.Desc.ProofFile.Lot.K1

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.HonestTrace (Sz)

variable {V W X : Type}

/-- **Which message's table rides**, and at which public numbers. -/
def firstRide (q : Params.First) (k : Nat) : Option Ride :=
  if k == ((K1.frame₀ q).atMoment 0).length then
    some ⟨((K1.frame₀ q).foldShape 0 {}).layout.k, ((K1.frame₀ q).foldShape 0 {}).layout.h⟩
  else none

/-- The part's address. -/
def firstAddr : Addr := ⟨⟨1, some 0, 1, .K1⟩, 0⟩

/-- The data of the main rows. -/
def firstFill (S : Sz) (q : Params.First) : RowData :=
  firstData S q.codes q.shape q.layout (firstSeat q.shape 0) fun _ => 0

/-- The job, of the chain's parameters and the plan's two numbers. -/
def firstJobAt (S : Sz) (q : Params.First) (gp : _root_.Desc.Plain.GPar) : SendJob Readers X :=
  { P := K1.firstPar q gp
    first := 0
    ride := firstRide q
    data := fun R fr k r j => (firstFill S q).forSend R firstAddr fr.heard k r j }

/-- **THE JOB**, at the lot's own arguments. -/
def firstJob (S : Sz) (Z : Pub) (G : Ground) : SendJob Readers X :=
  firstJobAt S G.first (K1.gpOf Z)

/-- **THE SEAT's PUBLIC TEST**: the job fits its place (sendFits, Honest/K1/Coins.lean) · at each of
the segment's own messages: the data is ready when nothing has been heard (RowData.readyAt), and no
data is laid at a pad's place (RowData.clear: Honest/RowData.lean). THE PART DOES NOT ASK THE LAST
TWO: it calls RowData.at_, which is total: whoever states a law on the data that is sent here names
this test. -/
def firstSeatOk (S : Sz) (q : Params.First) (gp : _root_.Desc.Plain.GPar) : Bool :=
  sendFits (K1.firstPar q gp) (firstRide q) &&
    (List.range ((K1.frame₀ q).atMoment 0).length).all fun k =>
      (firstFill S q).readyAt [] ⟨firstAddr, k⟩ &&
        (firstFill S q).clear ⟨firstAddr, k⟩
          (q.codes.base.getD (Johnson.Prover.Send.shapeAt (K1.firstPar q gp) k).code default).ell
          (Johnson.Prover.Send.shapeAt (K1.firstPar q gp) k)

/-- **The half at the place.** -/
def firstHalf (S : Sz) (wit : W → Readers) (Z : Pub) (G : Ground) : Placed V W X :=
  ⟨(firstJob (X := X) S Z G).P.place,
    [(sendPart (V := V) (firstJob (X := X) S Z G)).lift id wit id fun _ y => y]⟩

/-- **The lot's honest side.** THE NAME IS WRITTEN A SECOND TIME HERE; firstLot_name holds it
against the lot's own field. -/
def firstLot (S : Sz) (wit : W → Readers) : HLot V W X :=
  { name := "K1: the first segment's opening, each link's reads and digits"
    halves := fun Z G => [firstHalf S wit Z G] }

theorem firstLot_name (S : Sz) (wit : W → Readers) (quiet : K1.Quiet) (Z : Pub) :
    (firstLot (V := V) (X := X) S wit).name = (K1.lotWith quiet Z).name := rfl

/-- **THE LOT's OWN FIRST MEMBER** is K1.firstSegmentOpening at the arguments at which firstJob calls
K1.firstPar. -/
theorem lot_head (quiet : K1.Quiet) (Z : Pub) (G : Ground) :
    ((K1.lotWith quiet Z).own G).head? = some (K1.firstSegmentOpening G.first (K1.gpOf Z)) := rfl

/-- That member's rounds and oracle messages are those of the job's P. -/
theorem member_rounds (S : Sz) (Z : Pub) (G : Ground) :
    (K1.firstSegmentOpening (Cl := Unit) G.first (K1.gpOf Z)).rounds =
        K1.rounds (firstJob (X := X) S Z G).P ∧
      (K1.firstSegmentOpening (Cl := Unit) G.first (K1.gpOf Z)).oracles =
        K1.oracles (firstJob (X := X) S Z G).P := ⟨rfl, rfl⟩

theorem firstHalf_place (S : Sz) (wit : W → Readers) (Z : Pub) (G : Ground) :
    (firstHalf (V := V) (X := X) S wit Z G).place =
      (K1.firstSegmentOpening (Cl := Unit) G.first (K1.gpOf Z)).place := rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.firstLot_name
#print axioms ProofFile.Honest.K1.lot_head
#print axioms ProofFile.Honest.K1.member_rounds
#print axioms ProofFile.Honest.K1.firstHalf_place
#print axioms ProofFile.Honest.K1.firstRide
#print axioms ProofFile.Honest.K1.firstAddr
#print axioms ProofFile.Honest.K1.firstFill
#print axioms ProofFile.Honest.K1.firstJobAt
#print axioms ProofFile.Honest.K1.firstJob
#print axioms ProofFile.Honest.K1.firstSeatOk
#print axioms ProofFile.Honest.K1.firstHalf
#print axioms ProofFile.Honest.K1.firstLot
