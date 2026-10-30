-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotData.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: THE DATA AT ALL PLACES OF K1's LOT AS ONE TERM, NO LETTER FOR A FILLING LEFT; THE
SEATS' PUBLIC TEST AT "reads"; THE LOT's PUBLIC TEST, WHOLE. Definitions with code, and statements
by unfolding.

  lotData       THE DATA: lotFill (Honest/K1/LotFill.lean) with the two letters laid: mats: where
                the matrices of a link's list are read: owner's segment, name there, first column
                there (K3.matsOwn, Honest/K3/WitOwner.lean) · reads: the vector "U3", of the public
                instance (U3.u3RowsOf, Johnson/HonestTrace/U3Rows.lean)
  dataSide      K1's lot's honest side (lotSide, Honest/K1/PlaceJob.lean) at that data
  readsSample   a sample list of challenges of the plan's form in front of a seat: every element is
                1, every position and every matrix entry 0
  readsSeatsOk  THE SEATS' PUBLIC TEST AT "reads", at a public instance: at each link, at the piece
                that the lot's own linkNumbers names, "U3" has a seat at part 0 of that place and
                placeSeatOk accepts there
  apartOk       A PUBLIC TEST ON THE DEALING: no seat of "BZ" stands at the first place's part; no
                seat of "U3" stands there or at a seat of "BZ": so lotData hands each array's own
                data at its seats and no other filling's
  jobsSeatsOk   THE SEAT's TEST OF EACH JOB OF dataSide, AT THE JOB's OWN P, fold AND DATA:
                placeSeatOk at lotData itself, at the first place and at each link's two
  lotSeatsOk    THE LOT's PUBLIC TEST, WHOLE: the first place's · the reads' · the digits' · apartOk
                · jobsSeatsOk
  dataSide_name, dataSide_places   the name is the lot's own field · place by place, in order, the
                halves' places are the places of the lot's own blocks
  lot_first_seat   a pin: the whole test hands the seat's test at the first place's job: the premise
                of the law on what that job sends (seated_sent, Honest/K1/PlaceJobSent.lean)
  data_first, data_digits, data_reads   what lotData hands out at the three sorts of address

Kin. readsSeatsOk is digitsSeatsOk's second half (Honest/K1/LotFill.lean) at "U3", the reads' piece
and moment 1. The three statements on the data are LotFill's at these terms. jobsSeatsOk asks at
lotData what the three tests beside it ask at the fillings that lotData deals: no law here says that
the one follows from the others: so both are asked.

Limits. S (the sizes that the first place's filling reads) STAYS A LETTER. wit and no stay lotSide's
letters. readsSeatsOk SPEAKS AT ONE PUBLIC INSTANCE ("U3" at the head's segment hangs on the
request's covered positions) AND AT A SAMPLE LIST: whether the challenges that are heard in a run
are such that the filling's own test accepts it cannot see: whoever states a law on the data that is
sent names RowData.readyAt at the list heard. What lies beneath u3RowsOf, bzRows, zzDataAt and
matsOwn is other files' text: nothing is said of it here. No entry of an array is evaluated here.
Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.LotFill
import Johnson.Desc.ProofFile.Honest.K3.WitOwner
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.HonestTrace (Seat seatsOf mineOf)
open OnBytes.HonestTrace.U3 (u3RowsOf u3Seats)

variable {V W X : Type}

/-- **THE DATA AT ALL PLACES OF K1's LOT, AS ONE TERM**: lotFill with its two letters laid: mats: a
borrowed matrix is read under its owner's segment and name (K3.matsOwn), as "U3"'s own values read
it · reads: u3RowsOf. -/
def lotData (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) : RowDataOf ProofFile.Inst :=
  lotFill S (K3.matsOwn G.W) u3RowsOf Z G

/-- **K1's lot's honest side at that data.** -/
def dataSide (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst) (no : Place → Nat) :
    HLot V W X := lotSide wit no (lotData S)

/-- A sample list of challenges of the plan's form in front of a seat: as many as rounds of the
first chain stand in front of its sending; each has its round's three counts; every element is 1,
every position and every matrix entry 0. -/
def readsSample (Z : Pub) (s : Seat) : List Fmt.Drawn :=
  (Z.D.1.take s.heard).map fun d =>
    ⟨List.replicate d.entry.drawE (1, 0, 0), List.replicate d.entry.poss 0,
      List.replicate d.entry.trits 0, none⟩

/-- **THE SEATS' PUBLIC TEST AT "reads"**, at a public instance: for each link, at the piece that
the lot's own linkNumbers names: "U3" has a seat at part 0 of that place, and placeSeatOk accepts
there at readsSample. -/
def readsSeatsOk (Z : Pub) (G : Ground) (x : ProofFile.Inst) : Bool :=
  G.built.toList.zipIdx.all fun (Y, l) =>
    match K1.linkNumbers G Y with
    | none => true
    | some (pr, _, _, _) =>
      ((u3Seats Z G).find? fun s => s.addr.sender == ⟨⟨1, some l, pr, .K1⟩, 0⟩).any fun s =>
        placeSeatOk (K1.parLater G.first (K1.gpOf Z) l pr 1) none (u3RowsOf Z G x)
          (readsSample Z s)

/-- **A PUBLIC TEST ON THE DEALING**: lotFill deals by the address: the first place's part, then
the seats of "BZ", else the reads: no seat of "BZ" is of the first; no seat of "U3" is of the first
two. -/
def apartOk (Z : Pub) (G : Ground) : Bool :=
  ((seatsOf Z G "BZ").all fun s => s.addr.sender != firstAddr) &&
    (u3Seats Z G).all fun s =>
      s.addr.sender != firstAddr && !mineOf (seatsOf Z G "BZ") s.addr

/-- **THE SEAT's TEST OF EACH JOB OF dataSide, AT THE JOB's OWN P, fold AND DATA**: placeSeatOk at
lotData itself: at the first place (lotHalves' own terms: K1.firstPar, firstFold; nothing has been
heard) and, for each link, at the two pieces that the lot's own linkNumbers names (K1.parLater; no
fold), at the sample lists of the seats of "U3" and "BZ" there. -/
def jobsSeatsOk (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst) : Bool :=
  placeSeatOk (K1.firstPar G.first (K1.gpOf Z)) (firstFold G.first) (lotData S Z G x) [] &&
    G.built.toList.zipIdx.all fun (Y, l) =>
      match K1.linkNumbers G Y with
      | none => true
      | some (pr, pd, _, _) =>
        (((u3Seats Z G).find? fun s => s.addr.sender == ⟨⟨1, some l, pr, .K1⟩, 0⟩).any fun s =>
          placeSeatOk (K1.parLater G.first (K1.gpOf Z) l pr 1) none (lotData S Z G x)
            (readsSample Z s)) &&
        (((seatsOf Z G "BZ").find? fun s => s.addr.sender == ⟨⟨1, some l, pd, .K1⟩, 0⟩).any fun s =>
          placeSeatOk (K1.parLater G.first (K1.gpOf Z) l pd 2) none (lotData S Z G x)
            (digitsSample Z G (K3.matsOwn G.W) s))

/-- **THE LOT's PUBLIC TEST, WHOLE**, at a public instance. -/
def lotSeatsOk (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst) : Bool :=
  firstSeatOk S G.first (K1.gpOf Z) && readsSeatsOk Z G x &&
    digitsSeatsOk Z G (K3.matsOwn G.W) && apartOk Z G && jobsSeatsOk S Z G x

theorem dataSide_name (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (quiet : K1.Quiet) (Z : Pub) :
    (dataSide (V := V) (X := X) S wit no).name = (K1.lotWith quiet Z).name := rfl

theorem dataSide_places (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (no : Place → Nat) (quiet : K1.Quiet) (Z : Pub) (G : Ground) :
    ((dataSide (V := V) (X := X) S wit no).halves Z G).map (·.place) =
      ((K1.lotWith quiet Z).own G).map (·.place) :=
  lotSide_places wit no (lotData S) quiet Z G

theorem data_first (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (R : Readers) (hd : List Fmt.Drawn) (k r j : Nat) :
    (lotData S Z G x).forSend R firstAddr hd k r j =
      (firstFill S G.first).forSend R firstAddr hd k r j :=
  fill_first S (K3.matsOwn G.W) u3RowsOf Z G x R hd k r j

theorem data_digits (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (R : Readers) (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) (h1 : a.sender ≠ firstAddr)
    (h2 : mineOf (seatsOf Z G "BZ") a = true) :
    (lotData S Z G x).at_ R hd a r j = (digitsFill Z G (K3.matsOwn G.W)).at_ R hd a r j :=
  fill_digits S (K3.matsOwn G.W) u3RowsOf Z G x R hd a r j h1 h2

/-- **AT A SEAT OF "U3", UNDER apartOk, lotData HANDS "U3"'s DATA.** -/
theorem data_reads (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (R : Readers) (hd : List Fmt.Drawn) (s : Seat) (r j : Nat) (ha : apartOk Z G = true)
    (hs : s ∈ u3Seats Z G) :
    (lotData S Z G x).at_ R hd s.addr r j = (u3RowsOf Z G x).at_ R hd s.addr r j := by
  unfold apartOk at ha
  rw [Bool.and_eq_true] at ha
  have h := List.all_eq_true.1 ha.2 s hs
  rw [Bool.and_eq_true] at h
  exact fill_reads S (K3.matsOwn G.W) u3RowsOf Z G x R hd s.addr r j
    (by simpa using h.1) (by simpa using h.2)

/-- A pin on lotSeatsOk's definition: a projection: the whole test hands the seat's test at the
first place's job, at that job's own data. -/
theorem lot_first_seat (S : OnBytes.HonestTrace.Sz) (Z : Pub) (G : Ground) (x : ProofFile.Inst)
    (h : lotSeatsOk S Z G x = true) :
    placeSeatOk (K1.firstPar G.first (K1.gpOf Z)) (firstFold G.first) (lotData S Z G x) [] =
      true := by
  unfold lotSeatsOk at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  unfold jobsSeatsOk at h2
  rw [Bool.and_eq_true] at h2
  exact h2.1

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.lot_first_seat
#print axioms ProofFile.Honest.K1.dataSide_name
#print axioms ProofFile.Honest.K1.dataSide_places
#print axioms ProofFile.Honest.K1.data_first
#print axioms ProofFile.Honest.K1.data_digits
#print axioms ProofFile.Honest.K1.data_reads
#print axioms ProofFile.Honest.K1.lotData
#print axioms ProofFile.Honest.K1.dataSide
#print axioms ProofFile.Honest.K1.readsSample
#print axioms ProofFile.Honest.K1.readsSeatsOk
#print axioms ProofFile.Honest.K1.apartOk
#print axioms ProofFile.Honest.K1.jobsSeatsOk
#print axioms ProofFile.Honest.K1.lotSeatsOk
