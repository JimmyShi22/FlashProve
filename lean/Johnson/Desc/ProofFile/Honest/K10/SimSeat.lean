-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SimSeat.lean: the closing of a segment (K10): the statements of Honest/K10/Sim.lean at
the seated job, by name. Definitions; six statements, not one of which is proved in this file (`SeatedExact`,
`SeatedSentIs`, `SeatedOneToOne`, and `SeatedFresh`, which is without content: Honest/K10/SimSent.lean;
`SeatedAskPublic`, `SeatedOnFree`: nowhere); two small lemmas, proved (one by `rfl`). The spender's half alone, as
Sim.lean's head says.

Why. Sim.lean's statements stand at a letter J, and five of them bind a face of the frame, so they bite only at a job
typed at a face's input. What is to be proved of the description's own closing is typed here: at the lot's job (`jobAt`,
Honest/K10/SeatLot.lean), carried over to the frame's input through the seat's own reader (`closeIn`,
Honest/K10/Seat.lean), in the total form (tot = true), but for one, which is marked. The frame's face "in the first and
the second chain" (`Face.own`, Honest/Frame.lean) stands by name in `SeatedAskPublic`; `SeatedOnFree` binds none; the
others bind every face at these types. The other two chains: that every block of the kind K10 of the proof file's
description stands in its first chain, and none in the shared or the second, is the library's `LPFK10.k10_sits_file`
(Johnson/LPFK10R/SitsFile.lean), under its two premises.

  `seatedJob`        the lot's job, carried over: `(jobAt lay addrs segs (·.st pub.par) pub).over (closeIn readers rows
                   stAt)`: the statement in front of "BAT" is read off the small record, into which the seat's reader
                   has laid the lot's third parameter at the input's own public instance
  `seatedJob_const`  at a third parameter that drops the instance it is the seated job's text with a `stAt`
                   that is not handed the instance, at `jobAt`, `over`, `closeIn`: by `rfl`
  `foldAtT`, `seat_at`   the fold's part at a place, off Z and the ground G, cured and total: as `foldAt` (SeatLot.lean)
                   with `foldShellT true` for the caller; proved: seated as the kind's seat seats it, it is the part
                   at `seatedJob`
  `SeatedAskPublic`  `CloseAskPublic` at that face and the seated job (no statement of this library concludes it): which
                   end the making of the data takes (a refusal, nothing, the data) is one at any two inputs with one
                   public instance, at any carried runs and any run
    `SeatedExact`, `SeatedSentIs`, `SeatedOneToOne`, `SeatedFresh`   Sim.lean's (2), (3b), (3c), (5) there
  `SeatedOnFree`     Sim.lean's (4') there: not the row's: it speaks of `closeOnAt`, which is the letter On at tot =
                   false alone: at tot = true On asks nothing and it is not wanted

Limits. Of the six, statements alone, in this file. `SeatedAskPublic` is no premise of `SeatedExact`. By type the total
form's default can hang on more than what is public, shown or heard. `CloseAskPublic` (and, at the seated job,
`SeatedAskPublic`) says that it does not: a definition: no statement of this library concludes it, and none takes it as
a premise. What this part sends has the simulator's law either way (`close_exact`, `close_fresh`). All seven arguments
are letters here. At the description: lay, addrs, segs are what `foldAtT` lays off Z and the ground G; pub is handed to
it (`closeHalvesAt`, Honest/K10/AtLot.lean, lays it: the place's parameters and the list of what is borne); readers,
rows and stAt are the lot's three parameters that are left (`seatLotT`, SeatLotT.lean): letters there too.
`SeatedAskPublic` is stated at every readers: that is the letter through which the rest of the input comes. `jobAt`
calls the code switch's texts as they lie beneath at the build: a turn of these texts turns what these statements say.
`foldAtT` is laid in a lot by `seatLotT` (Honest/K10/SeatLotT.lean), which no definition and no maker of a description
calls. `seatLotC` (Honest/K10/SeatLotC.lean) lays the same part at the closings alone, and `closeLotAt`
(Honest/AtPureWiderK10.lean) lays its halves in a filling. No property of the protocol is claimed: nothing is said on
its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Sim
import Johnson.Desc.ProofFile.Honest.K10.SeatLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (E Statement)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (SegmentPub segmentsOf)

variable {W₀ Rc Xi Tr : Type}

/-- **The seated job.** -/
def seatedJob (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub)
    (stAt : StAtOf Xi) (pub : ClosePub) :
    CloseJob (Local W₀ Rc Xi Tr) :=
  (jobAt lay addrs segs (fun i => i.st pub.par) pub).over (closeIn readers rows stAt)

/-- **At a third parameter that drops the instance the seated job is the text written out here**: the lot's job at a
`stAt` that drops its input, carried over by the seat's reader: `seatedJob`'s body with `fun _ => st pub.par` where it
has `fun i => i.st pub.par`, and `fun _ => st` as `closeIn`'s third argument. (`seat_at`, `closingsT_are` hand
`stAt` on whole.) What the right side's names
do at a `stAt` that drops its input is read off their texts (Job.lean,
`closeAsk`, `closeAtHand`; Sim.lean, `CloseJob.over`): no theorem. -/
theorem seatedJob_const (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub)
    (st : StAt) (pub : ClosePub) :
    seatedJob readers rows lay addrs segs (fun _ => st) pub =
      (jobAt lay addrs segs (fun _ => st pub.par) pub).over (closeIn readers rows fun _ => st) := rfl

/-- **The fold's part at a place, off Z and the ground G, cured and total.** -/
def foldAtT {V X : Type} (Z : Pub) (G : Ground) : ClosePub → Part V CloseIn X :=
  fun pub => foldShellT true (jobAt G.first.layout (addrsAt Z G)
    ((segmentsOf Z G).take (pub.par.link + 1)) (fun i => i.st pub.par) pub) foldWords

/-- Seated as the kind's seat seats it, it is the part at the seated job. -/
theorem seat_at {X : Type} (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (Z : Pub)
    (G : Ground) (stAt : StAtOf Xi)
    (pub : ClosePub) :
    seatFold (X := X) (closeIn readers rows stAt) (foldAtT Z G) pub =
      foldShellT true (seatedJob readers rows G.first.layout (addrsAt Z G)
        ((segmentsOf Z G).take (pub.par.link + 1)) stAt pub) foldWords :=
  seat_is true (closeIn readers rows stAt)
    (fun pub => jobAt G.first.layout (addrsAt Z G) ((segmentsOf Z G).take (pub.par.link + 1))
      (fun i => i.st pub.par) pub) pub

section
variable (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
  (lay : OnBytes.Params.ReqLayout) (addrs : Nat → Nat → Option MsgAddr) (segs : List SegmentPub)
  (stAt : StAtOf Xi) (pub : ClosePub)

/-- **`CloseAskPublic` at the seated job.** A statement; no statement of this library concludes it. -/
def SeatedAskPublic : Prop :=
  CloseAskPublic (Face.own (W₀ := W₀) (Rc := Rc) (Xi := Xi) (Tr := Tr))
    (seatedJob readers rows lay addrs segs stAt pub)

/-- Sim.lean's (4') there. Not the row's: it belongs to the form tot = false. A statement; not proved. -/
def SeatedOnFree (X : Type) : Prop := CloseOnFree X (seatedJob readers rows lay addrs segs stAt pub)

/-- Sim.lean's (2) there, in the total form. A statement; not proved in this file (Honest/K10/SimSent.lean). -/
def SeatedExact (S Cl X : Type) : Prop :=
  CloseExact S Cl (Local W₀ Rc Xi Tr) X Xi true (seatedJob readers rows lay addrs segs stAt pub)

/-- Sim.lean's (3b) there. A statement; not proved in this file (Honest/K10/SimSent.lean). -/
def SeatedSentIs (S Cl X : Type) : Prop :=
  CloseSentIs S Cl (Local W₀ Rc Xi Tr) X Xi true (seatedJob readers rows lay addrs segs stAt pub)

/-- Sim.lean's (3c) there. A statement; not proved in this file (Honest/K10/SimSent.lean). -/
def SeatedOneToOne (S Cl X : Type) : Prop :=
  CloseOneToOne S Cl (Local W₀ Rc Xi Tr) X Xi true (seatedJob readers rows lay addrs segs stAt pub)

/-- Sim.lean's (5) there. A statement; not proved in this file (Honest/K10/SimSent.lean): an instance of `close_fresh`
(Honest/K10/SimLaws.lean): without content. -/
def SeatedFresh (S Cl X : Type) : Prop :=
  CloseFresh S Cl (Local W₀ Rc Xi Tr) X Xi true (seatedJob readers rows lay addrs segs stAt pub)

end

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seatedJob
#print axioms ProofFile.Honest.K10.seatedJob_const
#print axioms ProofFile.Honest.K10.foldAtT
#print axioms ProofFile.Honest.K10.seat_at
#print axioms ProofFile.Honest.K10.SeatedAskPublic
#print axioms ProofFile.Honest.K10.SeatedOnFree
#print axioms ProofFile.Honest.K10.SeatedExact
#print axioms ProofFile.Honest.K10.SeatedSentIs
#print axioms ProofFile.Honest.K10.SeatedOneToOne
#print axioms ProofFile.Honest.K10.SeatedFresh
