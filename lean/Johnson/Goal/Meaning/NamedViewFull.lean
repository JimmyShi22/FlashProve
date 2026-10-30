-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/NamedViewFull.lean: THE TEST namedV (Johnson/Goal/Meaning/NamedView.lean)
ACCEPTS AT THE TWO WRITTEN VALUES OF THE FULL SIZE: the view of the public part's shape (xShapeFull,
Johnson/G/XShapeLit.lean) and the request's layout (layoutFull, Johnson/G/LayoutLit.lean). Closed
facts, by the kernel; and what follows from two equations.

  named_full   namedV xShapeFull layoutFull = true.
  named_walks   the test walks 176 entries there: it is not idle.
  named_bent, named_empty   NEGATIVE TESTS: with every array's columns one higher in the layout's
    first segment, and at the empty layout: false.
  named_of_pins   xShapeOf Z.p.X = xShapeFull and Z.first.layout = layoutFull give namedAt Z = true.

OBJECT: namedV at two written values; namedAt. LETTERS: Z: free.

What is not claimed. That the two equations hold at any Z. The full size alone. No soundness.

-/
import Johnson.Goal.Meaning.NamedView
import Johnson.G.XShapeLit
import Johnson.G.LayoutLit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.NamedAsk

open VerifiableInference.PlanWritten (xShapeOf)
open Johnson.G (xShapeFull layoutFull)

set_option maxRecDepth 1000000 in
/-- **THE CLOSED FACT.** -/
theorem named_full : namedV xShapeFull layoutFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test walks 176 entries. -/
theorem named_walks : ((List.range 25).map fun k => (tailV xShapeFull k).1).sum = 176 := by
  decide +kernel

/-- Every array's columns one higher in the layout's first segment. -/
def layoutBent : OnBytes.Params.ReqLayout :=
  ⟨layoutFull.link.modifyHead fun as => as.map fun a => { a with sizeC := a.sizeC + 1 }⟩

set_option maxRecDepth 1000000 in
/-- A negative test. -/
theorem named_bent : namedV xShapeFull layoutBent = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the empty layout. -/
theorem named_empty : namedV xShapeFull ⟨[]⟩ = false := by decide +kernel

/-- **FROM THE TWO PINS.** -/
theorem named_of_pins {Z : ProofFile.Pub} (hx : xShapeOf Z.p.X = xShapeFull)
    (hl : Z.first.layout = layoutFull) : namedAt Z = true :=
  named_closed hx hl named_full

end Meaning.NamedAsk

#print axioms Meaning.NamedAsk.named_full
#print axioms Meaning.NamedAsk.named_walks
#print axioms Meaning.NamedAsk.named_bent
#print axioms Meaning.NamedAsk.named_empty
#print axioms Meaning.NamedAsk.named_of_pins
