-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Seat.lean: the half of the closing of a segment (K10), seated in
the input that a half of the first chain is handed. This file defines part of the honest prover.
Definitions with code; one line by `rfl`.

The fold's part is typed at a small record of the kind's own, `CloseIn`, and seated by `Part.lift` (the round "BAT"
reads nothing and is typed at every input). Of the prover's input its `wit` hands the part the readers that all callers
of the main rows' data share (`Readers`, Honest/RowData.lean: the cells, the index, the index committer's coins), the
filling of these data at the input's own public instance (`RowDataOf`, same file), the verifier's statement in front of
"BAT" as a function that is laid at that same public instance, and nothing else: where the caller lays `closeIn` as the
reader: in `seatFold`, `closeSeat` and `seatClosings` the reader is a letter. It hands nothing on, and its stops read
nothing of the input.

  `StAt`        the statement in front of "BAT", of a place's numbers and what was shown and drawn: the type
  `StAtOf`      the type of the lot's third parameter: of the public instance; then as `StAt`
  `CloseIn`     the small record: the readers; the main rows' data; the statement in front of "BAT", place by place
  `closeIn`     the small record off a half's input
  `closeIn_st`  its third field is the lot's third parameter at t.x: by `rfl`
  `seatFold`    the fold's part, typed at the small record, seated
  `closeSeat`   the kind's half at the first chain's types: `closeHalf` at the seated part
  `seatClosings`   the seated halves at the lot's places: `closings` (Honest/K10/AtLot.lean) at the
                seated part: the same text as `closeSeat` at each place

Limits. What is read through the readers is said by the main rows' data (`RowData`), which is a parameter whose type is
defined in Honest/RowData.lean. `foldDue` is not asked here. No property of the protocol is claimed: nothing is said on
its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Job
import Johnson.Desc.ProofFile.Honest.K10.AtLot
import Johnson.Desc.ProofFile.Honest.RowData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement)
open VerifiableInference.Desc.First.Close (Par)

/-- The statement in front of "BAT", and the number of the segment's group: at a place's numbers, of what was shown in
front of "BAT" (a `Seen`: the rounds, and the opened columns where they are handed) and the rounds' challenges. -/
abbrev StAt : Type := Par → Seen → List Fmt.Drawn → Except String (Statement × Nat)

/-- **The type of the lot's third parameter**: of the public instance; then as `StAt`. It is handed nothing else of the
input: so, of the input, what it yields hangs on t.x alone (what Xi holds, and what the letter closes over, no type
says). -/
abbrev StAtOf (Xi : Type) : Type := Xi → StAt

/-- **The small record**: what the kind's part needs of the prover's input. -/
structure CloseIn where
  readers : Readers
  data : RowData
  /-- the statement in front of "BAT", place by place: laid at the input's own public instance -/
  st : StAt

/-- **The small record off a half's input**: the two fillings are applied to the input's own instance. -/
def closeIn {W₀ Rc Xi Tr : Type} (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (t : Local W₀ Rc Xi Tr) : CloseIn := ⟨readers t, rows t.x, stAt t.x⟩

/-- **What the seat's reader lays as the statement in front of "BAT"**: the lot's third parameter at the input's own
instance, and nothing else of the input. -/
theorem closeIn_st {W₀ Rc Xi Tr : Type} (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (t : Local W₀ Rc Xi Tr) : (closeIn readers rows stAt t).st = stAt t.x := rfl

/-- **The fold's part, seated.** inOf: the small record off the prover's input. fold: the prover's side of the
rounds from "FOLD epsilon" on, typed at the small record. -/
def seatFold {W₀ Rc Xi Tr X : Type} (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (fold : ClosePub → Part Unit CloseIn Unit) :
    ClosePub → Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun Z => (fold Z).lift (fun _ => ()) inOf (fun _ => ()) fun x _ => x

/-- **The kind's half, seated.** -/
def closeSeat {W₀ Rc Xi Tr X : Type} (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (fold : ClosePub → Part Unit CloseIn Unit) :
    KindHalf ClosePub (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  closeHalf (seatFold inOf fold)

/-- **The seated halves at the lot's places.** -/
def seatClosings {W₀ Rc Xi Tr X : Type} (inOf : Local W₀ Rc Xi Tr → CloseIn)
    (borne : Pub → VerifiableInference.Desc.First.Close.Par → List Borne)
    (fold : ClosePub → Part Unit CloseIn Unit) :
    Pub → Ground → List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  closings borne (seatFold inOf fold)

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.StAt
#print axioms ProofFile.Honest.K10.StAtOf
#print axioms ProofFile.Honest.K10.CloseIn
#print axioms ProofFile.Honest.K10.closeIn
#print axioms ProofFile.Honest.K10.closeIn_st
#print axioms ProofFile.Honest.K10.seatFold
#print axioms ProofFile.Honest.K10.closeSeat
#print axioms ProofFile.Honest.K10.seatClosings
