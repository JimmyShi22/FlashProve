-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/Sizes/TurnsThreeFull.lean: at the lines typed for the full-size parameter file
(Params.recordLines), a matrix of 3076096 rows and 1 mask row of the request's mask message, the
iteration that sizes the three groups of a proof's test on the table (Params.linTurns) ends at three
typed sizings.

The way is that of OnBytes/Params/KeyOnceRecord.lean, which does the same for a key's test: each
sizing of each turn has a closed statement of its own, proved by decide +kernel. The typed values
were printed by Lean's evaluator and laid in by a program; each is checked by the kernel in its own
statement.
Main names:
  `prLin`, `prGroups`, `prGroups_eq`: the lines of the test; the record of the three groups.
  `prTurns`: the iteration's answer.
Limits: that a proof's sizing calls linTurns at these arguments is not said here. Nothing on
soundness. Nothing on hiding. For proofs only; no program imports this file.

-/
import OnBytes.Params.KeyOnceRecord
import Johnson.Desc.K12.Law.Sizes.TurnsUFull
import Johnson.Desc.K12.Law.Sizes.TurnsOFull
import Johnson.Desc.K12.Law.Sizes.TurnsWFull

set_option autoImplicit false

namespace H2K.Sizes
open OnBytes.Params

/-- The lines of a proof's test on the table. -/
def prLin : LinLines := linLines recordLines 3076096 1 false

/-- The record of the three groups. -/
def prGroups : LinGroups :=
  ⟨true, .shared, .request, ⟨⟨24, 4194304, 0, true⟩, ⟨13, 64, 0, true⟩, 7, 0, 1, .johnson, 0⟩, ⟨⟨22,
    262144, 0, true⟩, ⟨13, 64, 0, true⟩, 4, 0, 1, .johnson, 0⟩, ⟨⟨22, 262144, 0, true⟩, ⟨13, 256, 0,
    true⟩, 5, 1, 1, .johnson, 0⟩, 68⟩

/-- It is the record that linSized's text forms. -/
theorem prGroups_eq : linGroupsOf recordSet prLin recordTable = prGroups := by decide +kernel

/-- The folded row's group after turn 1. -/
def prX1 : Sizing :=
  ⟨⟨⟨24, 4194304, 0, true⟩, ⟨13, 64, 0, true⟩, 7, 0, 1, .johnson, 182⟩, 101, true⟩

/-- Omega's group after turn 1. -/
def prY1 : Sizing :=
  ⟨⟨⟨22, 262144, 0, true⟩, ⟨13, 64, 0, true⟩, 4, 0, 1, .johnson, 158⟩, 51, true⟩

/-- The own group after turn 1. -/
def prZ1 : Sizing :=
  ⟨⟨⟨22, 262144, 0, true⟩, ⟨13, 256, 0, true⟩, 5, 1, 1, .johnson, 158⟩, 55, true⟩

/-- The folded row's group after turn 2. -/
def prX2 : Sizing :=
  ⟨gU1, 101, true⟩

/-- Omega's group after turn 2. -/
def prY2 : Sizing :=
  ⟨gO1, 51, true⟩

/-- The own group after turn 2. -/
def prZ2 : Sizing :=
  ⟨gW1, 55, true⟩

theorem prTurn1_x : sizeOne recordSet prGroups.foldedShape prLin.folded prGroups.shared
    ({} : Sizing).t (({} : Sizing).t + ({} : Sizing).t) prGroups.foldedRows {} =
      some prX1 := by
  decide +kernel

theorem prTurn1_y : sizeOne recordSet prGroups.omegaShape prLin.omega prGroups.shared
    (({} : Sizing).t + prLin.requests * ({} : Sizing).t) (({} : Sizing).t + ({} : Sizing).t)
    (1 + 2 * recordSet.samples) {} = some prY1 := by
  decide +kernel

theorem prTurn1_z : sizeOne recordSet prGroups.ownShape prLin.own prGroups.request
    (({} : Sizing).t + prLin.requests * ({} : Sizing).t) ({} : Sizing).t
    (2 + 3 * recordSet.samples) {} = some prZ1 := by
  decide +kernel

theorem prTurn2_x : sizeOne recordSet prGroups.foldedShape prLin.folded prGroups.shared
    prX1.t (prX1.t + prY1.t) prGroups.foldedRows prX1 =
      some prX2 := by
  decide +kernel

theorem prTurn2_y : sizeOne recordSet prGroups.omegaShape prLin.omega prGroups.shared
    (prY1.t + prLin.requests * prZ1.t) (prX1.t + prY1.t)
    (1 + 2 * recordSet.samples) prY1 = some prY2 := by
  decide +kernel

theorem prTurn2_z : sizeOne recordSet prGroups.ownShape prLin.own prGroups.request
    (prY1.t + prLin.requests * prZ1.t) prZ1.t
    (2 + 3 * recordSet.samples) prZ1 = some prZ2 := by
  decide +kernel

/-- **The iteration over the three groups**: 2 turns. -/
theorem prTurns :
    linTurns recordSet prLin (linGroupsOf recordSet prLin recordTable) 33 {} {} {} =
      some (prX2, prY2, prZ2) := by
  rw [prGroups_eq]
  exact (linTurns_step (fuel := 32) rfl prTurn1_x prTurn1_y prTurn1_z).trans
    ((if_neg (by decide)).trans
    ((linTurns_step (fuel := 31) rfl prTurn2_x prTurn2_y prTurn2_z).trans
    (if_pos (by decide))))

end H2K.Sizes

#print axioms H2K.Sizes.prGroups_eq
#print axioms H2K.Sizes.prTurns
