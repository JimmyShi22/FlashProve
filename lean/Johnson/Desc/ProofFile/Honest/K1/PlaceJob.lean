-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/PlaceJob.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: THE JOB AT A PLACE, GENERAL IN THE PLACE AND IN THE FILLING; AND K1's LOT's HONEST
SIDE AT ALL ITS PLACES. Definitions with code, statements and proofs.

  PlaceIn       what the job reads of the prover's input: the public instance and the readers
  rideOf, firstFold   A RIDE IS MADE OFF A FOLD's SHAPE, NOT TYPED: at the number of that fold's
                fresh mask, at the fold's own k and h; the first place's
  placeJob      THE JOB: P: the lot's own call · first: the number that the first new message gets ·
                fold: its ride is rideOf fold · D: the data of the main rows, of the public
                instance · part
  rideOwn       A PUBLIC TEST: the message at that number is announced just as the programs announce
                that fold's fresh mask. IT CANNOT SEE k: the notice does not hold it
  placeSeatOk   THE SEAT's PUBLIC TEST, at a sample list of challenges of the plan's form: rideOwn;
                the job fits its place; at each message the data is ready at that list
                (RowData.readyAt, in which a filling's public tests on the layout live) and none is
                laid at a pad's place
  placeHalf     the half at a place: the one part, seated by Part.lift
  laterJobAt    the job at a segment's later moment: K1.parLater; no table rides
  lotHalves, lotSide   THE HALVES AT ALL PLACES OF K1's LOT, in the order and by the very numbers of
                the lot's own blocks (Johnson/Desc/ProofFile/Lot/K1.lean); the lot's honest side
  lotSide_name  the name is the lot's own field
  lotSide_places   PLACE BY PLACE, IN ORDER: the halves' places are the places of the lot's own
                blocks, whatever quiet step is joined
  later_rounds  at a later moment the rounds, oracle messages and place of K1's own block
                (K1.laterAt: in front of a quiet step where the lot joins one) are those of the
                job's P
  joined_rounds where the lot joins a step without a round and without an oracle message behind it,
                the member's are still those
  firstRide_eq, no_ride   the first place's ride is made so · where no fold is handed in no table
                rides and the test holds
  seat_job      a pin on placeJob's definition: where the seat's test accepts at a fold, the part's
                own guard passes at the job at that fold
  first_data    at a filling that reads no instance the general job's data at the first place are
                firstJobAt's (Honest/K1/PlaceFirst.lean)

Limits. THREE LETTERS: wit (what makes the instance and the readers of a prover's input) · no (the
number that a place's first new message gets: public; nothing here makes it off the description's
list; at the first place it must be 0 for the half there to send what firstJobAt sends) · D (the
fillings). JOB AND SEAT's TEST TAKE THE SAME LETTER fold: no caller of placeJob hands it a ride.
WHAT NO TEST ON P CAN SEE: THE FOLD's k (P holds notices alone: k is the group's, off the frame): A
fold THAT IS TYPED WITH ANOTHER k PASSES rideOwn · a fresh mask that is handed no ride: so a fold is
made off the description's own term (firstFold; lotHalves has no letter for it), never typed. fold
NAMES AT MOST ONE RIDING TABLE A SENDING: so it is at the first place, at the later moments and at
W's; of other sendings nothing is said. SendJob keeps its field ride: whoever writes a SendJob
without placeJob can still type one. THE PART ASKS sendFits ALONE: whoever states a law on what is
sent at a place names placeSeatOk, and RowData.readyAt at the list heard
(Honest/K1/PlaceJobSent.lean has such a law, and beside it a general form that does not name the
test: its head says why). THAT THE QUIET STEP WHICH THE DESCRIPTION JOINS HAS NO ROUND AND NO ORACLE
MESSAGE is joined_rounds' premise: paid at the real step in Honest/K1/PlaceQuiet.lean. TWO HONEST
SIDES BEAR THE LOT's NAME: firstLot (Honest/K1/PlaceFirst.lean: the first place alone, at the
readers) and lotSide: a description takes one. Who makes the sample list is not said. W's sending is
not of this lot. Nothing is played here. THREE LAWS ON THE FIRST PLACE (first_rideOwn, own_le_sent,
seat_first) STAND IN Honest/K1/PlaceJobLinks.lean: they lean on Johnson/Desc/K1/Law/Links.lean, a
law file with a wide cone, WHICH THIS FILE, WHICH HOLDS CODE, DOES NOT IMPORT.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

variable {V W X Xi : Type}

/-- What the job at a place reads of the prover's input: the public instance and the readers. -/
structure PlaceIn (Xi : Type) where
  x : Xi
  R : Readers

/-- **A ride is made off a fold's shape, not typed**: fold: the number, in the sending, of a fold's
fresh mask, and that fold's shape; none: no table rides. The table of that message rides, at the
fold's own k and h. -/
def rideOf (fold : Option (Nat × FoldShape)) (k : Nat) : Option Ride :=
  fold.bind fun x => if k == x.1 then some ⟨x.2.layout.k, x.2.layout.h⟩ else none

/-- The first place's: the terms of which the description's own text makes that message's notice
(firstLaid, Johnson/Desc/K1/First.lean). -/
def firstFold (q : Params.First) : Option (Nat × FoldShape) :=
  some (((K1.frame₀ q).atMoment 0).length, (K1.frame₀ q).foldShape 0 {})

/-- **THE JOB AT A PLACE, GENERAL IN THE PLACE AND IN THE FILLING.** P: the place's numbers: the
lot's own call · first: the number that the first new message gets · fold: which message's table
rides, and at which fold's numbers: THE LETTER THAT THE SEAT's TEST TAKES (rideOf makes the ride off
it) · D: the data of the main rows, of the public instance (RowDataOf, Honest/RowData.lean) · part:
the part's number at the place. Of what stands in front it reads what was heard alone. -/
def placeJob (P : K1.Par) (first : Nat) (fold : Option (Nat × FoldShape)) (D : RowDataOf Xi)
    (part : Nat := 0) : SendJob (PlaceIn Xi) X :=
  { P := P, first := first, ride := rideOf fold
    data := fun w fr k r j => (D w.x).forSend w.R ⟨P.place, part⟩ fr.heard k r j }

/-- **A PUBLIC TEST: THE RIDE STANDS AT A MESSAGE THAT IS ANNOUNCED AS A FOLD's FRESH MASK OF THAT
h**: the message at that number is announced just as the programs announce that fold's fresh mask
(foldMaskNotice, OnBytes/Iop/Fold.lean: 2 ^ h mask rows, the fold's mask code and class of leaves,
no sample). WHAT IT CANNOT SEE: **k**: THE NOTICE DOES NOT HOLD IT, AND NOTHING IN P DOES: two folds
that part in k alone are announced alike; at a k below the fold's own the table holds fewer values
and the written 0 behind them · a fresh mask that is handed no ride. SO fold IS TO BE MADE OFF THE
DESCRIPTION's OWN TERM (as firstFold is), NEVER TYPED. -/
def rideOwn (P : K1.Par) (fold : Option (Nat × FoldShape)) : Bool :=
  fold.all fun x => P.sent[x.1]? == some (foldMaskNotice x.2)

/-- **THE SEAT's PUBLIC TEST, GENERAL**, at a public instance's filling. fold: as in rideOf. hs: A
SAMPLE LIST OF CHALLENGES OF THE PLAN's FORM: as many as have been heard when the sending begins,
each of the form that its round states; their values are the caller's choice ([] where nothing has
been heard). The ride stands at a message announced as a fresh mask of its h (rideOwn: IT CANNOT SEE
k) · the job fits its place · at each message:
the data is ready at hs (RowData.readyAt: enough has been heard; and the filling's own test, IN
WHICH ITS PUBLIC TESTS ON THE LAYOUT LIVE) · no data is laid at a pad's place. WHAT IT CANNOT SEE:
whether the challenges that are heard in a run have that form: whoever states a law on the data that
is sent names RowData.readyAt at the list heard. -/
def placeSeatOk (P : K1.Par) (fold : Option (Nat × FoldShape)) (D : RowData)
    (hs : List Fmt.Drawn) (part : Nat := 0) : Bool :=
  rideOwn P fold && sendFits P (rideOf fold) &&
    (List.range P.sent.size).all fun k =>
      D.readyAt hs ⟨⟨P.place, part⟩, k⟩ &&
        D.clear ⟨⟨P.place, part⟩, k⟩ (P.codes.base.getD (shapeAt P k).code default).ell
          (shapeAt P k)

/-- The half at a place: the one part, seated by Part.lift. -/
def placeHalf (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) : Placed V W X :=
  ⟨J.P.place, [(sendPart (V := V) J).lift id wit id fun _ y => y]⟩

/-- The job at a segment's later moment: the lot's own call K1.parLater; no table rides. -/
def laterJobAt (q : Params.First) (gp : _root_.Desc.Plain.GPar) (link piece moment first : Nat)
    (D : RowDataOf Xi) : SendJob (PlaceIn Xi) X :=
  placeJob (K1.parLater q gp link piece moment) first none D

/-- **THE HALVES AT ALL PLACES OF K1's LOT**, in the order and by the very numbers of the lot's own
blocks (Johnson/Desc/ProofFile/Lot/K1.lean): the first segment's opening; then for each link its
reads (moment 1) and its digits (moment 2), at the pieces that linkNumbers names. no: the number
that a place's first new message gets. -/
def lotHalves (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi) (Z : Pub)
    (G : Ground) : List (Placed V W X) :=
  placeHalf wit (placeJob (K1.firstPar G.first (K1.gpOf Z)) (no ⟨1, some 0, 1, .K1⟩)
      (firstFold G.first) (D Z G)) ::
    G.built.toList.zipIdx.flatMap fun (Y, l) =>
      match K1.linkNumbers G Y with
      | none => []
      | some (pr, pd, _, _) =>
        [placeHalf wit (laterJobAt G.first (K1.gpOf Z) l pr 1 (no ⟨1, some l, pr, .K1⟩) (D Z G)),
         placeHalf wit (laterJobAt G.first (K1.gpOf Z) l pd 2 (no ⟨1, some l, pd, .K1⟩) (D Z G))]

/-- **K1's lot's honest side, whole.** -/
def lotSide (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi) :
    HLot V W X :=
  { name := "K1: the first segment's opening, each link's reads and digits"
    halves := lotHalves wit no D }

theorem lotSide_name (wit : W → PlaceIn Xi) (no : Place → Nat) (D : Pub → Ground → RowDataOf Xi)
    (quiet : K1.Quiet) (Z : Pub) :
    (lotSide (V := V) (X := X) wit no D).name = (K1.lotWith quiet Z).name := rfl

theorem later_rounds (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment first : Nat) (D : RowDataOf Xi) (arrays : Option (List Nat)) :
    (K1.laterAt (Cl := Unit) q gp link piece moment arrays).rounds =
        K1.rounds (laterJobAt (X := X) q gp link piece moment first D).P ∧
      (K1.laterAt (Cl := Unit) q gp link piece moment arrays).oracles =
        K1.oracles (laterJobAt (X := X) q gp link piece moment first D).P ∧
      (K1.laterAt (Cl := Unit) q gp link piece moment arrays).place =
        (laterJobAt (X := X) q gp link piece moment first D).P.place := ⟨rfl, rfl, rfl⟩

/-- **PLACE BY PLACE, IN ORDER.** -/
theorem lotSide_places (wit : W → PlaceIn Xi) (no : Place → Nat)
    (D : Pub → Ground → RowDataOf Xi) (quiet : K1.Quiet) (Z : Pub) (G : Ground) :
    ((lotSide (V := V) (X := X) wit no D).halves Z G).map (·.place) =
      ((K1.lotWith quiet Z).own G).map (·.place) := by
  show (lotHalves (V := V) (X := X) wit no D Z G).map (·.place) =
    (K1.blocks (K1.gpOf Z) quiet G).map (·.place)
  unfold lotHalves K1.blocks
  simp only [List.map_cons, List.map_append, List.map_nil, List.singleton_append,
    List.map_flatMap]
  congr 1
  refine List.flatMap_congr fun x _ => ?_
  obtain ⟨Y, l⟩ := x
  rcases hn : K1.linkNumbers G Y with _ | ⟨pr, pd, reads, digits⟩
  · simp only [hn]
    rfl
  · simp only [hn]
    cases quiet G l Y <;> rfl

theorem first_data (S : OnBytes.HonestTrace.Sz) (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (w : PlaceIn Xi) (fr : Front X) :
    (placeJob (X := X) (K1.firstPar q gp) 0 (firstFold q) (fun _ : Xi => firstFill S q)).data w
        fr =
      (firstJobAt (X := X) S q gp).data w.R fr := rfl

theorem joined_rounds (q : Params.First) (gp : _root_.Desc.Plain.GPar)
    (link piece moment first : Nat) (D : RowDataOf Xi) (arrays : Option (List Nat)) (z : K1.B)
    (hr : z.rounds = []) (ho : z.oracles = []) :
    ((K1.laterAt q gp link piece moment arrays).andThen
        (K1.laterAt (Cl := Unit) q gp link piece moment arrays).name z).rounds =
        K1.rounds (laterJobAt (X := X) q gp link piece moment first D).P ∧
      ((K1.laterAt q gp link piece moment arrays).andThen
        (K1.laterAt (Cl := Unit) q gp link piece moment arrays).name z).oracles =
        K1.oracles (laterJobAt (X := X) q gp link piece moment first D).P ∧
      ((K1.laterAt q gp link piece moment arrays).andThen
        (K1.laterAt (Cl := Unit) q gp link piece moment arrays).name z).place =
        (laterJobAt (X := X) q gp link piece moment first D).P.place := by
  refine ⟨?_, ?_, rfl⟩
  · show (K1.laterAt (Cl := Unit) q gp link piece moment arrays).rounds ++ z.rounds = _
    rw [hr, List.append_nil]
    rfl
  · show (K1.laterAt (Cl := Unit) q gp link piece moment arrays).oracles ++ z.oracles = _
    rw [ho, List.append_nil]
    rfl

theorem firstRide_eq (q : Params.First) : firstRide q = rideOf (firstFold q) := rfl

theorem no_ride (P : K1.Par) : rideOf none = (fun _ => none) ∧ rideOwn P none = true := ⟨rfl, rfl⟩

/-- A pin on placeJob's definition: two projections of the seat's test: where it accepts at a fold,
the guard that the part itself asks (sendFits J.P J.ride, Honest/K1/Part.lean) passes AT THE JOB AT
THAT FOLD. -/
theorem seat_job (P : K1.Par) (first : Nat) (fold : Option (Nat × FoldShape)) (D : RowDataOf Xi)
    (x : Xi) (hs : List Fmt.Drawn) (part : Nat)
    (h : placeSeatOk P fold (D x) hs part = true) :
    rideOwn P fold = true ∧
      sendFits (placeJob (X := X) P first fold D part).P
        (placeJob (X := X) P first fold D part).ride = true := by
  unfold placeSeatOk at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  exact h.1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.firstRide_eq
#print axioms ProofFile.Honest.K1.no_ride
#print axioms ProofFile.Honest.K1.joined_rounds
#print axioms ProofFile.Honest.K1.seat_job
#print axioms ProofFile.Honest.K1.lotSide_name
#print axioms ProofFile.Honest.K1.later_rounds
#print axioms ProofFile.Honest.K1.lotSide_places
#print axioms ProofFile.Honest.K1.first_data
#print axioms ProofFile.Honest.K1.PlaceIn
#print axioms ProofFile.Honest.K1.rideOf
#print axioms ProofFile.Honest.K1.firstFold
#print axioms ProofFile.Honest.K1.placeJob
#print axioms ProofFile.Honest.K1.rideOwn
#print axioms ProofFile.Honest.K1.placeSeatOk
#print axioms ProofFile.Honest.K1.placeHalf
#print axioms ProofFile.Honest.K1.laterJobAt
#print axioms ProofFile.Honest.K1.lotHalves
#print axioms ProofFile.Honest.K1.lotSide
