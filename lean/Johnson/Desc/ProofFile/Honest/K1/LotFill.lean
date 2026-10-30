-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotFill.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: THE DATA AT THE PLACES OF K1's LOT, WITH "digits" AS A TERM. Definitions with code,
and three statements by unfolding.

  digitsFill    THE DATA AT "digits" (a segment's moment 2): the arrays "BZ" (bzRows,
                Johnson/HonestTrace/BZRows.lean) and "ZZ" (zzDataAt, Honest/K8/ZzData.lean), which
                lie in one message, joined by place (RowData.over)
  lotFill       THE DATA AT ALL PLACES OF THE LOT, dealt by the address (RowData.join): the first
                place's part: firstFill · a seat of "BZ": digitsFill · else: reads: A LETTER
  digitsSample  a sample list of challenges in front of a seat of "BZ": of the plan's length; the
                last holds as many sampled zeros as the digits read, the others are empty
  digitsSeatsOk THE SEATS' PUBLIC TEST AT "digits": "ZZ"'s own public test (zzSeated) · at each
                link, at the piece that the lot's own linkNumbers names, "BZ" has a seat at part 0
                of that place and placeSeatOk (Honest/K1/PlaceJob.lean) accepts there
  join_at, fill_first, fill_digits, fill_reads   what RowData.join hands out: the chosen part's ·
                what lotFill hands out at the three sorts of address

Kin. The joined term and the sample list stand as local values in the integer model's own test
(Johnson/HonestTrace/BZRowsAtSmall.lean); no definition there bears them.

Limits. mats, A PARAMETER OF BOTH FILLINGS, AND reads, THE FILLING OF MOMENT 1, ARE LETTERS HERE:
Honest/K1/LotData.lean lays both. THE ORDER OF THE JOIN BY PLACE ("BZ" first) is
immaterial by the two texts (each filling's sizes know its own array's name alone): no statement
here says so. That no seat of "BZ" stands at the first place's part is a premise of fill_digits. No
entry of "BZ" or "ZZ" is evaluated here. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob
import Johnson.HonestTrace.BZRows
import Johnson.Desc.ProofFile.Honest.K8.ZzData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open OnBytes.HonestTrace (Seat seatsOf pairOf mineOf bzRows bzAtOf)

variable {Xi : Type}

/-- **THE DATA AT "digits"** (a segment's moment 2): the one message holds two arrays: "BZ" (the
integer model's filling bzRows, Johnson/HonestTrace/BZRows.lean) and "ZZ" (Honest/K8/ZzData.lean's
zzDataAt, at the same seats), joined BY PLACE (RowData.over): BZ's element where BZ lays one, else
ZZ's. mats: both fillings' own parameter. -/
def digitsFill (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) : RowData :=
  (bzRows Z G mats).over (ProofFile.Honest.K8.zzDataAt G Z.D.1 (pairOf (seatsOf Z G "BZ")) mats)

/-- **THE DATA AT ALL PLACES OF K1's LOT**, dealt BY THE ADDRESS (RowData.join): at the first
place's part: firstFill · at a seat of "BZ": digitsFill · at every other address: reads: the filling
of the segments' moment 1, of the public instance: A LETTER (of this lot's addresses these are the
reads' alone). -/
def lotFill (S : OnBytes.HonestTrace.Sz) (mats : Nat → List (Nat × String × Nat))
    (reads : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) : RowDataOf Xi := fun x =>
  RowData.join (fun a => a.sender == firstAddr) (firstFill S G.first)
    (RowData.join (mineOf (seatsOf Z G "BZ")) (digitsFill Z G mats) (reads Z G x))

/-- A sample list of challenges in front of a seat of "BZ": of the plan's length: as many as have
been heard; NOT OF THE PLAN's FORM: all empty but the last, which holds as many sampled zeros as the
digits read: its round's own count where BzAt.fits (Johnson/HonestTrace/BZVals.lean) accepts. -/
def digitsSample (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) (s : Seat) :
    List Fmt.Drawn :=
  List.replicate (s.heard - 1) (⟨[], [], [], none⟩ : Fmt.Drawn) ++
    [⟨[], [], List.replicate (((bzAtOf Z G mats s.seg).map (·.wanted)).getD 0) 0, none⟩]

/-- **THE SEATS' PUBLIC TEST AT "digits"**: "ZZ"'s own public test beside its filling (zzSeated,
Honest/K8/ZzData.lean: each segment whose plan has a state of the test has, among the seats'
addresses, one whose message bears "ZZ": else all of that segment's digits would be laid nowhere and
no address could say so) · for each link, at the piece that the lot's own linkNumbers names: "BZ"
has a seat at part 0 of that place, and placeSeatOk accepts there at digitsSample. -/
def digitsSeatsOk (Z : Pub) (G : Ground) (mats : Nat → List (Nat × String × Nat)) : Bool :=
  ProofFile.Honest.K8.zzSeated G.first.shape G.first.layout (pairOf (seatsOf Z G "BZ"))
      (ProofFile.Honest.K8.zzPubOf G Z.D.1 mats) ((seatsOf Z G "BZ").map (·.addr)) &&
  G.built.toList.zipIdx.all fun (Y, l) =>
    match K1.linkNumbers G Y with
    | none => true
    | some (_, pd, _, _) =>
      ((seatsOf Z G "BZ").find? fun s => s.addr.sender == ⟨⟨1, some l, pd, .K1⟩, 0⟩).any fun s =>
        placeSeatOk (K1.parLater G.first (K1.gpOf Z) l pd 2) none (digitsFill Z G mats)
          (digitsSample Z G mats s)

/-- What RowData.join hands out: the chosen part's. -/
theorem join_at (mine : MsgAddr → Bool) (A B : RowData) (R : Readers) (hd : List Fmt.Drawn)
    (a : MsgAddr) (r j : Nat) :
    (RowData.join mine A B).at_ R hd a r j =
      if mine a then A.at_ R hd a r j else B.at_ R hd a r j := by
  unfold RowData.at_ RowData.join
  by_cases h : mine a = true
  · simp only [h, if_true]
  · simp only [h, Bool.false_eq_true, if_false]

theorem fill_first (S : OnBytes.HonestTrace.Sz) (mats : Nat → List (Nat × String × Nat))
    (reads : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi) (R : Readers)
    (hd : List Fmt.Drawn) (k r j : Nat) :
    (lotFill S mats reads Z G x).forSend R firstAddr hd k r j =
      (firstFill S G.first).forSend R firstAddr hd k r j := by
  unfold RowData.forSend lotFill
  rw [join_at, if_pos (beq_self_eq_true _)]

theorem fill_digits (S : OnBytes.HonestTrace.Sz) (mats : Nat → List (Nat × String × Nat))
    (reads : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi) (R : Readers)
    (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) (h1 : a.sender ≠ firstAddr)
    (h2 : mineOf (seatsOf Z G "BZ") a = true) :
    (lotFill S mats reads Z G x).at_ R hd a r j = (digitsFill Z G mats).at_ R hd a r j := by
  unfold lotFill
  rw [join_at, if_neg (by simpa using h1), join_at, if_pos h2]

theorem fill_reads (S : OnBytes.HonestTrace.Sz) (mats : Nat → List (Nat × String × Nat))
    (reads : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) (x : Xi) (R : Readers)
    (hd : List Fmt.Drawn) (a : MsgAddr) (r j : Nat) (h1 : a.sender ≠ firstAddr)
    (h2 : mineOf (seatsOf Z G "BZ") a = false) :
    (lotFill S mats reads Z G x).at_ R hd a r j = (reads Z G x).at_ R hd a r j := by
  unfold lotFill
  rw [join_at, if_neg (by simpa using h1), join_at, if_neg (by rw [h2]; exact Bool.false_ne_true)]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.join_at
#print axioms ProofFile.Honest.K1.fill_first
#print axioms ProofFile.Honest.K1.fill_digits
#print axioms ProofFile.Honest.K1.fill_reads
#print axioms ProofFile.Honest.K1.digitsFill
#print axioms ProofFile.Honest.K1.lotFill
#print axioms ProofFile.Honest.K1.digitsSample
#print axioms ProofFile.Honest.K1.digitsSeatsOk
