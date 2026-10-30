-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorInv0Members.lean: THE PUBLIC TEST ON THE ONE TREE's NUMBERS (seatPlanOk,
Johnson/Prover/Link/DoorInv0.lean) SAYS YES AT TWO SHAPES: at the toy's (tinyLink, tinyCodes:
Johnson/Prover/Link/ToyLink.lean; st: ToyParts.lean) and at the link's typed parameters of the full
size (frP: Johnson/Desc/K15/TypedP.lean; curF: Johnson/Prover/Link/DoorPlanFull.lean).

What is checked when the file compiles.
  seatPlan_toy, seatPlan_full   TWO THEOREMS, each one run of Lean's kernel ("decide +kernel") over
      the test's six clauses.
  #guard lines   the test says yes at both; its list has six clauses; and THREE CONTROLS, each with
      the names of the clauses that refuse: at the toy the second stage in the first's place
      ("log"); the like at the full size; at the toy a message without its third oracle message
      (both lists of symbols and the width). The names are written here; why just these clauses
      refuse is not argued here.

A NUMBER THAT CAN BE TURNED WITHOUT A REFUSAL. With 5 rows for 3 in the toy's shape no clause
refuses: a #guard line says so. Why: both sides of each clause are made of the same shape: the tree
is laid anew for 5 rows, and the lists and the width follow. The test ties the library's laying of
trees to the shape; it does not tie the shape to anything else.

Limits. Two shapes. A #guard line is run by Lean's evaluator (compiled code, outside the kernel) and
leaves no theorem. That the parameters that run are the typed ones is a law in scope elsewhere.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorInv0
import Johnson.Prover.Link.DoorPlanToy
import Johnson.Prover.Link.DoorPlanFull

set_option autoImplicit false

namespace Johnson.Prover.Link.Members
open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 Johnson.Prover.Link.Toy Johnson.Prover.Link.Full

/-- the names of the clauses that refuse -/
def seatNoes (S : LinkShape) (K : Codes) (cur : Fmt.M1.Stage) : List String :=
  ((seatPlanL S K cur).filter (!·.2)).map (·.1)

#guard seatPlanOk tinyLink tinyCodes (st 0)
#guard seatPlanOk frP.S frP.codes curF
#guard (seatPlanL tinyLink tinyCodes (st 0)).length = 6
-- controls
#guard seatNoes tinyLink tinyCodes (st 1) = ["log"]
#guard seatNoes frP.S frP.codes nxtF = ["log"]
#guard seatNoes { tinyLink with masksAhead := false } tinyCodes (st 0) =
  ["mainSymbols", "maskSymbols", "width"]
-- a number that can be turned without a refusal (the head says why)
#guard seatNoes { tinyLink with rows := 5 } tinyCodes (st 0) = []

theorem seatPlan_toy : seatPlanOk tinyLink tinyCodes (st 0) = true := by decide +kernel

theorem seatPlan_full : seatPlanOk frP.S frP.codes curF = true := by decide +kernel

end Johnson.Prover.Link.Members

#print axioms Johnson.Prover.Link.Members.seatPlan_toy
#print axioms Johnson.Prover.Link.Members.seatPlan_full
