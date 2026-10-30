-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Slice/LinkShape.lean: the shape of the written link `Link0 D d`
(OnBytes/TypedOracleCompiler/Slice/EntryX.lean) as a term that names no decision.

Why. `Link0 D d` is the written link at a decision d. Its shape does not look at d. A list of counts
for it has the type `Err (Link0 D d).shape`. Where one list is to serve every instance, and each
instance has a decision of its own, the list can be typed at the decision that says yes to all,
`Err (Link0 D fun _ => true).shape`, and used at `Link0 D (dec x)`. To type such a statement a
checker must see that the two shapes are one. Each is a field of a record, and the two records
differ in the decision alone; a checker that compares the records on the way meets the two
decisions. Where the second is a letter that comparison fails at once, and the shapes are then found
equal by unfolding. Where it is a whole program at written parameters the comparison unfolds that
program, which is costly. With the list typed at `link0Shape D` no second record stands on the other
side, and the comparison is not made. So the statements whose decision is the program at written
parameters type their list at `link0Shape D`; the others (a letter for the decision, or the program
at parameters that are letters) stay as they are, and the two forms pass into each other by
unfolding.

Main names.
  `link0Shape D`: the shape.
  `link0_shape`: it is the shape of `Link0 D d` at every decision d, by unfolding.

Not claimed. Nothing new is proved: a definition and one equation by unfolding. That any given
checker takes the road that is told above: it is a reading of the definitions' text, held at no
checker's source. That a checker finishes the statements so typed. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Slice.EntryX

set_option autoImplicit false

noncomputable section

namespace TypedOracleCompiler.Slice
open TypedOracleCompiler.Run
open TypedOracleCompiler.Run.PQ (XD)
open _root_.Iop (Shape)
open _root_.Run.PQ (View)

/-- The shape of the written link, as a term that names no decision. -/
def link0Shape (D : XD) : Shape := _root_.Run.Twin.up (PQ.SOf D.C D.ds)

/-- It is the shape of the written link at every decision, by unfolding. -/
theorem link0_shape (D : XD) (d : View → Bool) : (Link0 D d).shape = link0Shape D := rfl

end TypedOracleCompiler.Slice
