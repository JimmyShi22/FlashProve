-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Rows.lean: the kind "the code switch" (K2): THE KIND's ROWS WITH
THEIR SIMULATORS, as a lot of rows without letters (`SLot`, Honest/Thread/Rows.lean): at each place
of the kind: the part beside its simulator (`switchRow`, Honest/K2/Sim.lean), the premise on the
stand laid as "true", and the part's count (`switchBud`, Honest/K2/Exact.lean: each list of
positions against the messages of its own tree; no range is asked). Definitions with code; one
equation with its proof.

  `numbersAt`       a place's numbers, as the lot that seats the kind's blocks makes them
                    (`P1K2.pureSpots`, Johnson/Desc/ProofFile/Lot/K2.lean); nothing where it makes
                    none
  `roundsAt`        the kind's own two rounds at these numbers, each with its oracle messages: the
                    simulator's letter. No round where the place has no numbers
  `lotClosing`      the closing as the kind's lot lays it (`lotClosingAt`, Honest/K2/Exact.lean), at
                    a plan's public data
  `switchSLot`      THE LOT OF ROWS, under the lot's name. At a place: the sender is the shared
                    sending's core; the simulator's public test is `publicOk` at the segments in
                    front of the switch
  `switchSLot_toHLot`   THE EQUATION: forgetting the simulators, the premise on the stand and the
                    count, it is the kind's one lot (`switchLot`)

All of it can be run: no definition here is noncomputable.

Limits. Nothing is shown here of what a simulator yields. That `roundsAt` is the rounds of the block
that a description seats at the place is not shown: it is a premise of the statements in
Honest/K2/Exact.lean and Fresh.lean (`blocks`). No test in this library evaluates `switchSLot`: it
wants the public files' data. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Exact
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2
open VerifiableInference.Desc (Place Oracle)

variable {W₀ Rc Xi Tr X : Type}

/-- A place's numbers. -/
def numbersAt (Z : Pub) (G : Ground) (a : Place) : Option VerifiableInference.Desc.First.K2.P2 :=
  ((P1K2.pureSpots Z G).find? fun x => x.1.place == a).map (·.2)

/-- The kind's own two rounds at a place, each with its oracle messages. -/
def roundsAt (Z : Pub) (G : Ground) (a : Place) : List (Fmt.DeclaredRound × List Oracle) :=
  match numbersAt Z G a with
  | some q => (VerifiableInference.Desc.First.K2.rounds q).zip [q.sent, []]
  | none => []

/-- The closing as the kind's lot lays it, at a plan's public data. -/
def lotClosing (Z : Pub) (G : Ground) : Closing := lotClosingAt G.first.layout (segmentsOf Z G)

/-- **THE LOT OF ROWS.** -/
def switchSLot (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) :
    SLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi :=
  { name := "the code switch"
    rows := fun Z G => (switchPlaces Z G).map fun p =>
      { place := p.place
        row := switchRow (coreSender freshTable) D readers (lotClosing Z G) p
          (publicOk D G.first.layout p ((segmentsOf Z G).take p.link)) (roundsAt Z G p.place)
        On := fun _ _ _ _ => True
        bud := switchBud p } }

/-- **THE EQUATION.** -/
theorem switchSLot_toHLot (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers) :
    (switchSLot D readers : SLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi).toHLot =
      switchLot D readers := by
  unfold SLot.toHLot switchSLot switchLot switchHalves
  simp only [List.map_map]
  rfl

end ProofFile.Honest.K2

#print axioms ProofFile.Honest.K2.numbersAt
#print axioms ProofFile.Honest.K2.roundsAt
#print axioms ProofFile.Honest.K2.lotClosing
#print axioms ProofFile.Honest.K2.switchSLot
#print axioms ProofFile.Honest.K2.switchSLot_toHLot
