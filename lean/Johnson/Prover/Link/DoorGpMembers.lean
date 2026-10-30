-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/DoorGpMembers.lean: gpPlanOk (Johnson/Prover/Link/DoorPayGp.lean) SAYS YES AT
TWO SHAPES: at the toy's (tinyLink, tinyCodes: Johnson/Prover/Link/ToyLink.lean; p12, st:
ToyParts.lean) and at the link's typed parameters of the full size (frP:
Johnson/Desc/K15/TypedP.lean; pF, curF: Johnson/Prover/Link/DoorPlanFull.lean).
gpPlanOk: a test with code on public numbers alone: the clauses of the description's two tests on
the record behind the batching (gpOk, labelsOk), asked of a record that is made of public numbers
(skelOf, DoorPayGp.lean: below "the skeleton"), and: the stage is the place's first.

What is checked when the file compiles.
  gpPlan_toy, gpPlan_full   TWO THEOREMS, each by Lean's kernel ("decide +kernel") on the one closed
      Boolean: AT THE FULL SIZE ONE KERNEL RUN OVER 37 CLAUSES (the first test's 35, the second
      test's one, and the stage). On one machine the whole file, guards and both theorems, took 10
      to 18 seconds in our builds; the largest resident set seen (samples every two
      seconds) was some 7.5 GiB: measured beside the build; no command here shows either figure.
  #guard lines   the test says yes at both; and THREE CONTROLS at the toy, each with the names of
      the clauses that refuse: the second stage in the first's place (thirteen); no tree declared
      for the first opening (four); a folded row of 5 rows for 3 (two). The names are written here;
      why just these clauses refuse is not argued here.

A NUMBER THAT CAN BE TURNED WITHOUT A REFUSAL. With the chain's first tree counted from 1
(nums.firstTree := 1, nothing else turned) NO CLAUSE REFUSES at the toy: a #guard line says so. Why:
the label of the tree that the first opening declares is written out in nums.first (0, by numsOf,
Johnson/Desc/Link/LinkDesc.lean), not made of firstTree; and the one clause that reads firstTree,
"opens.key", takes it away ON BOTH SIDES, in natural numbers: 0 - 1 = 0 = 0 - 1; and the skeleton's
tree has the number 0 by its make, whatever the plan's firstTree says: it is the number that the
book's tree has where the CONTEXT counts the chain's trees from 0 (gp_of_ran's premise on
c.ch.firstTree). That the plan's nums.firstTree is the context's number is asked by no clause here.
At both shapes here the plan's firstTree is 0 (numsOf's text), so there "opens.key" compares the
label with the number itself.

Limits. Two shapes. A #guard line is run by Lean's evaluator (compiled code, outside the kernel) and
leaves no theorem. That the parameters that run are the typed ones is a law in scope elsewhere.
Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.DoorPayGp
import Johnson.Prover.Link.DoorPlanToy
import Johnson.Prover.Link.DoorPlanFull

set_option autoImplicit false

namespace Johnson.Prover.Link.Members
open OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc VerifiableInference.Desc.K12
open Desc.K15 Johnson.Prover.Link.Toy Johnson.Prover.Link.Full

/-- the names of the first test's clauses that refuse at the skeleton -/
def gpNoes (S : LinkShape) (K : Codes) (p : P12) (cur : Fmt.M1.Stage) : List String :=
  match (layTrees K (linkMessage S 1)).bind (·.shapes[0]?) with
  | some sh => ((H2K.First.gpL p cur {} (skelOf S K p cur.k sh)).filter (!·.2)).map (·.1)
  | none => ["no tree"]

#guard gpPlanOk tinyLink tinyCodes p12 (st 0)
#guard gpPlanOk frP.S frP.codes pF curF
#guard gpNoes tinyLink tinyCodes p12 (st 0) = []
#guard gpNoes frP.S frP.codes pF curF = []
-- controls
#guard gpPlanOk tinyLink tinyCodes p12 (st 1) = false
#guard gpNoes tinyLink tinyCodes p12 (st 1) =
  ["0:long", "0:codeM", "0:roomM", "1:long", "1:codeM", "1:roomM", "f:mask", "f:zshort", "f:codeZ",
    "opens.n", "opens.key", "opens.a", "opens.W"]
#guard gpNoes tinyLink tinyCodes { p12 with nums := { p12.nums with first := [] } } (st 0) =
  ["opens.n", "opens.key", "opens.a", "opens.W"]
#guard gpPlanOk tinyLink tinyCodes { p12 with nums := { p12.nums with first := [] } } (st 0) = false
#guard gpNoes { tinyLink with rows := 5 } tinyCodes p12 (st 0) = ["1:roomM", "opens.W"]
#guard gpPlanOk { tinyLink with rows := 5 } tinyCodes p12 (st 0) = false
-- a number that can be turned without a refusal (the head says why)
#guard gpPlanOk tinyLink tinyCodes { p12 with nums := { p12.nums with firstTree := 1 } } (st 0)
#guard p12.nums.firstTree = 0 && pF.nums.firstTree = 0

theorem gpPlan_toy : gpPlanOk tinyLink tinyCodes p12 (st 0) = true := by decide +kernel

theorem gpPlan_full : gpPlanOk frP.S frP.codes pF curF = true := by decide +kernel

end Johnson.Prover.Link.Members

#print axioms Johnson.Prover.Link.Members.gpPlan_toy
#print axioms Johnson.Prover.Link.Members.gpPlan_full
