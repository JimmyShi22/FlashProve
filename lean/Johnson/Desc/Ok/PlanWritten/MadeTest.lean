-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/MadeTest.lean: the one row by which a verifier's list of tests holds
what follows from the public files against written values, and the two of its four tests that are
defined here. The first: the planner's sizes of a proof file, and its first list of rounds, each
round with its error bound, are the written ones. The second: six fields of the first chain's
parameters, as read back, are the written ones. The third, on the lists of what is sent, stands in
Johnson/Desc/Ok/PlanWritten/SendsTest.lean; the fourth, on the shape part of what the program
`verify-on-bytes`'s reader makes of the public files, in
Johnson/Desc/Ok/PlanWritten/XShapeTest.lean. Definitions alone.

What it is for. Laws on the IOP as written in Lean for the proof file read closed facts off written
values. That the planner's values at the public files are the written ones is, for two parts, no
theorem: nobody has got Lean's kernel through the planner's sizing of a proof file at the full
size, nor through what it reads of the 25 sub-proofs for the first list. So these two are asked at
the run, of whole values.

What is compared, and what is not. Of what the planner configures (`Configured`,
OnBytes/Params/Configure.lean) four fields do not hang on the digest of the public files: the sizes,
and the lists of rounds for the proof file, the key file and a copy's file (`Free`,
Johnson/G/MadeFree.lean). `madeIs` compares the proof file's sizes and the first of its three lists.
All else of the four is, in the goals' scope, the written value by theorems, some of them from these
two: Johnson/Goal/Numbers/MadeInScope.lean joins them, and ends in the equation of all four fields
with one written value.

The written side: `proofSizedFull` (Johnson/Desc/Ok/PlanWritten/SizedLit.lean); the first list,
48293 rounds, as distinct rounds and runs (Johnson/Desc/ProofFile/Written/Priced.lean); the layout
of a request's arrays, `layoutFull` (Johnson/G/LayoutLit.lean).

Why comparisons are written out: the types bear no decidable equality where they are declared, and a
file beneath a verifier's list of tests holds definitions alone. That no field and no round is left
out is a theorem (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean): a yes gives equations of whole
values.

Definitions.
  `proofLit`: the proof file's first written list.
  `madeIs made`: the sizes by `sameProof` (Johnson/Desc/Ok/PlanWritten/SizedTest.lean); the first
    list by the walk `rideB` (Johnson/G/RunsDefs.lean), which compares the setting and all seven
    fields of every round and never lays the written side out.
  `firstIs f`: the six fields: the codes, the shape of the linear test, the shape of a request, the
    number of rows left to the test on the table, the shape of the binding, and the layout. The
    layout's types bear a decidable equality where they are declared: it is compared by that, whole.
    In scope the layout file is fixed to the byte, but nobody has got Lean's kernel through its
    reading: so this too is asked at the run.
  `madeRow Z`: these two, the test on the proof file's three lists of what is sent (`proofSendsIs`,
    SendsTest.lean) and the test on the shape part (`xShapeIs`, XShapeTest.lean), at a public part Z
    (`ProofFile.Pub`, Johnson/Desc/ProofFile/Pub.lean): the one row of a verifier's list of tests. All
    four are bare: they ask at every key. The verifier's list of tests lays this one row. The
    earlier tests `sizedPinned` and `firstPinned` (Johnson/Desc/Ok/PlanWritten/SizedTest.lean) are
    forms of which laws speak, laid in no list of tests: they follow from the row's yes
    (`sized_of_made`, `first_of_made`). `firstPinned` gives five fields; for the layout see
    `layout_in_scope`, for the state before the first segment `start_in_scope`, for what is sent
    `sends_in_scope`, for the chain's two numbers `par_in_scope`, for the shape part
    `xShape_in_scope` (Johnson/Goal/Numbers/MadeInScope.lean). The verifier's list of tests asks
    them at the full size's key alone; the form with the key, of which the laws speak, is
    `madePinned` (MadeTestLaws.lean).

Limits. A yes says nothing of what else follows from the public files. That made and f are of the
same files is the caller's. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SizedTest
import Johnson.G.RunsDefs
import Johnson.Desc.ProofFile.Written.Priced
import Johnson.G.LayoutLit
import Johnson.Desc.Ok.PlanWritten.SendsTest
import Johnson.Desc.Ok.PlanWritten.XShapeTest
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open OnBytes OnBytes.Params Johnson.G
open VerifiableInference.Number.ByRuns (Lit rideB)

/-- The proof file's first written list of rounds with error bounds. -/
def proofLit : Lit := ⟨pricedProofSetFull, pricedProofRecsFull0, pricedProofRunsFull0⟩

/-- **The proof file's sizes and its first list of rounds are the written ones.** Bare: it asks at
every key. 60000 bounds the steps of the walk. The planner's rounds go as runs of one, so each step
takes one of them, unless a written run has no member, and one step more finds both lists at their
end: 48294 steps at a list of the written length. A list that is too long for the bound is rejected.
-/
def madeIs (made : Configured) : Bool :=
  sameProof made.sized.proof proofSizedFull &&
    match made.proof with
    | a :: _ => rideB 60000 a proofLit
    | [] => false

/-- **Six fields of the first chain's parameters, as read back, are the written ones**: five are
those of the written sizes; the sixth is the layout of a request's arrays, whole. Bare. -/
def firstIs (f : First) : Bool :=
  decide (f.codes = proofSizedFull.codes) && decide (f.lin = proofSizedFull.batch.shape) &&
    decide (f.shape = proofSizedFull.request) && decide (f.pendingRows = 13) &&
    decide (f.binding = ⟨6, 40⟩) && decide (f.layout = layoutFull)

/-- **The row**: the four tests at the public part that the IOP as written in Lean for the proof
file computes: what the planner configured; the first chain's parameters as read back; the proof
file's three lists of what is sent (`proofSendsIs`, Johnson/Desc/Ok/PlanWritten/SendsTest.lean); the
shape part of what `verify-on-bytes`'s reader makes of the public files (`xShapeIs`,
Johnson/Desc/Ok/PlanWritten/XShapeTest.lean). Bare: it asks at every key. -/
def madeRow (Z : ProofFile.Pub) : Bool :=
  madeIs Z.p.chains.made && firstIs Z.first && proofSendsIs Z.made && xShapeIs Z.p.X

end VerifiableInference.PlanWritten
