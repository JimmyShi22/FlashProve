-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/SeatLotT.lean: the closing of a segment (K10): the lot's honest side with the cured,
total part laid in. This file defines part of the honest prover. One definition with code; four theorems.

  `seatLotT`          `seatLotR` (Honest/K10/SeatLot.lean) with `foldAtT` (Honest/K10/SimSeat.lean) in `foldAt`'s
                   stead: the same three parameters are left: readers, rows, stAt
  `seatLotT_halves`   its halves: K9's own (`K9.batHalves`), then `seatClosings … (foldAtT Z G) Z G`
  `closingsT_are`     that second list, written out: at each place of `closePars` (Honest/K10/AtLot.lean): `closeHalf`
                   at `foldShellT true` at the seated job of that place (`seatedJob`, SimSeat.lean) and `foldWords`
  `seatLotT_const`    at a third parameter that drops the instance the lot is the term that the statement writes out:
                   the lot's text with a `stAt` that is not handed the instance, written out at the file's own
                   names: not by `rfl`
  `seatLotT_constH`   the same of its halves, written out

Limits. `seatLotT` is run by no line: it wants the public data of a real description. `seatLotR` is not taken away; it
is marked as not to be laid. Which lot a description lays is its maker's to do: no definition and no maker of a
description calls either; statements that name `seatLotT` stand in four files: this one, Honest/K10/SeatLotC.lean,
Reads/Door.lean and LotAll.lean. As at the older lot (SeatLot.lean's Limits): whoever lists the halves asks `borneDue`,
`foldDueAll` and `borneSame`: no maker of a half asks them; that the lot's seated part passes `foldDueAll`:
no statement of this library concludes it; of `borneDue` and `borneSame` no theorem. No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.SimSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement)
open VerifiableInference.Desc.First.Close (Par)
open ProofFile.Honest.K2 (segmentsOf)

variable {W₀ Rc Xi Tr X : Type}

/-- **The lot's honest side, seated, with the cured part**: `seatLotR` (Honest/K10/SeatLot.lean) with `foldAtT`
(Honest/K10/SimSeat.lean) in `foldAt`'s stead. -/
def seatLotT (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) :
    HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  K9.batLot fun Z g => seatClosings (closeIn readers rows stAt) borneAt (foldAtT Z g) Z g

/-- **The lot's halves**: K9's own, then the kind's. -/
theorem seatLotT_halves (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : Pub) (G : Ground) :
    (seatLotT (X := X) readers rows stAt).halves Z G =
      K9.batHalves Z ++ seatClosings (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G := rfl

/-- **The halves that it lays for the kind, written out**: at each place that `closePars` reads: one part: "BAT"'s
move, then the cured part at the seated job of that place. -/
theorem closingsT_are (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi)
    (stAt : StAtOf Xi) (Z : Pub) (G : Ground) :
    (seatClosings (X := X) (closeIn readers rows stAt) borneAt (foldAtT Z G) Z G) =
      (closePars Z).map fun P =>
        closeHalf (fun pub => foldShellT true (seatedJob readers rows G.first.layout (addrsAt Z G)
          ((segmentsOf Z G).take (pub.par.link + 1)) stAt pub) foldWords) ⟨P, borneAt Z P⟩ := by
  show (closePars Z).map (fun P => closeHalf (seatFold (closeIn readers rows stAt) (foldAtT Z G))
    ⟨P, borneAt Z P⟩) = _
  refine List.map_congr_left fun P _ => ?_
  show closeHalf (seatFold (closeIn readers rows stAt) (foldAtT Z G)) ⟨P, borneAt Z P⟩ = _
  rw [show (seatFold (X := X) (closeIn readers rows stAt) (foldAtT Z G)) = fun pub =>
    foldShellT true (seatedJob readers rows G.first.layout (addrsAt Z G)
      ((segmentsOf Z G).take (pub.par.link + 1)) stAt pub) foldWords from
    funext fun pub => seat_at readers rows Z G stAt pub]

/-- **At a third parameter that drops the instance the lot is the text written here**: `seatLotT`'s
own text with `foldAtT`'s body for its name, with `fun _ => st pub.par` where that body has
`fun i => i.st pub.par`, and with `fun _ => st` as `closeIn`'s third argument. Not by `rfl`: the two parts in front of
the seat stand at different jobs (one reads its statement off the small record, the other drops its input): they are one
only behind the seat, and that the seated part is the part at the carried-over job (`seat_is`, from `lift_is`,
Honest/K10/Sim.lean) is by `simp only` (`List.map_map`: the moves are a list of open length) and then `rfl`. The names
on the right side: what they do at a `stAt` that drops its input is read off
their texts (Job.lean, `closeAsk`, `closeAtHand`; Sim.lean, `CloseJob.over`): no theorem. -/
theorem seatLotT_const (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (st : StAt) :
    seatLotT (X := X) readers rows (fun _ => st) =
      K9.batLot fun Z g => seatClosings (closeIn readers rows fun _ => st) borneAt
        (fun pub => foldShellT true (jobAt g.first.layout (addrsAt Z g)
          ((segmentsOf Z g).take (pub.par.link + 1)) (fun _ => st pub.par) pub) foldWords) Z g := by
  unfold seatLotT
  refine congrArg K9.batLot (funext fun Z => funext fun g => ?_)
  have e : seatFold (X := X) (closeIn readers rows fun _ => st) (foldAtT Z g) =
      seatFold (closeIn readers rows fun _ => st) (fun pub => foldShellT true
        (jobAt g.first.layout (addrsAt Z g) ((segmentsOf Z g).take (pub.par.link + 1))
          (fun _ => st pub.par) pub) foldWords) := funext fun pub => by
    rw [seat_at, seat_is true (closeIn readers rows fun _ => st)
      (fun pub => jobAt g.first.layout (addrsAt Z g) ((segmentsOf Z g).take (pub.par.link + 1))
        (fun _ => st pub.par) pub) pub]
    rfl
  unfold seatClosings
  rw [e]

/-- **The same of the lot's halves, written out**: `seatLotT_halves`' and `closingsT_are`'s right sides,
with `seatedJob`'s body for its name, with `fun _ => st pub.par` where that body has `fun i => i.st pub.par`,
and with `fun _ => st` as `closeIn`'s third argument. Of the names on the right side: as at
`seatLotT_const`.
-/
theorem seatLotT_constH (readers : Local W₀ Rc Xi Tr → Readers) (rows : RowDataOf Xi) (st : StAt)
    (Z : Pub) (G : Ground) :
    (seatLotT (X := X) readers rows fun _ => st).halves Z G =
      K9.batHalves Z ++ (closePars Z).map fun P =>
        closeHalf (fun pub => foldShellT true ((jobAt G.first.layout (addrsAt Z G)
          ((segmentsOf Z G).take (pub.par.link + 1)) (fun _ => st pub.par) pub).over
            (closeIn readers rows fun _ => st)) foldWords) ⟨P, borneAt Z P⟩ := by
  rw [seatLotT_halves, closingsT_are]
  rfl

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.seatLotT
#print axioms ProofFile.Honest.K10.seatLotT_halves
#print axioms ProofFile.Honest.K10.closingsT_are
#print axioms ProofFile.Honest.K10.seatLotT_const
#print axioms ProofFile.Honest.K10.seatLotT_constH
