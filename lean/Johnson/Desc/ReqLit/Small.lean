-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ReqLit/Small.lean: THE REQUEST's SHAPE (`OnBytes.Params.ReqShape`: the links, each
message with its shape, class of leaves, moment and LIFE; what rides at the start; the last test's
stages) AT THE SMALL EXAMPLE, AS A WRITTEN VALUE, for statements that Lean's kernel is to evaluate.
A definition, and two theorems by an evaluation in the kernel. It imports OnBytes/Iop/Req.lean
alone.

  `shapeSmall : ReqShape`: the value. `shapeSmall_ok`: the program's own test on a shape,
    `reqShapeOk`, says yes. `shapeSmall_groups`: what the program's `reqGroups` makes of it: each
    group's k and h, and the switch's kept targets with the flag "kept again". `shapeSmall_moments`:
    along each link's list the moments do not fall. Whence the numbers: a program wrote the value
    from a print that Lean's evaluator made of the planner's own request:
    `(OnBytes.Model.Verify.planned ..).chains.made.sized.proof.request`, at the library's own copies
    of the three public files of prover/examples/target_small_f2_roomy
    (`OnBytes.Model.TestRecordWork.plannedAt smallHead`). No file was read.
Limits. THE THEOREMS SPEAK OF THE WRITTEN VALUE. That it IS the planner's request is held BY A RUN
of Lean's evaluator, outside the library (the whole value compared; a control with one
number turned says no): Lean's kernel does not evaluate the planner (`decide +kernel` gets stuck in
the parsing), and no test that a build runs holds the two together. That a running request has this
shape is not said. Nothing on soundness.

-/
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ReqLit

open OnBytes OnBytes.Params

/-- **The request's shape at the small example, as a written value.** A message: its shape (code,
main rows, degree of the main rows, mask rows, mask code, answers), its class of leaves, its moment,
its life. -/
def shapeSmall : ReqShape :=
  { code := 0, maskCode := 0
    link := [
    ⟨0, [⟨⟨0, 61, 1, 1, 0, 1⟩, 0, 0, 0⟩,
      ⟨⟨0, 3, 1, 0, noId, 1⟩, 0, 0, 1⟩,
      ⟨⟨0, 1, 1, 0, noId, 1⟩, 0, 0, 2⟩,
      ⟨⟨0, 2, 3, 0, noId, 1⟩, 0, 1, 0⟩,
      ⟨⟨0, 129, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩,
    ⟨0, [⟨⟨0, 23, 1, 1, 0, 1⟩, 0, 0, 0⟩,
      ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
      ⟨⟨0, 61, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩,
    ⟨0, [⟨⟨0, 60, 1, 1, 0, 1⟩, 0, 0, 0⟩,
      ⟨⟨0, 3, 1, 0, noId, 1⟩, 0, 0, 1⟩,
      ⟨⟨0, 1, 1, 0, noId, 1⟩, 0, 0, 2⟩,
      ⟨⟨0, 2, 3, 0, noId, 1⟩, 0, 1, 0⟩,
      ⟨⟨0, 129, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩,
    ⟨0, [⟨⟨0, 23, 1, 1, 0, 1⟩, 0, 0, 0⟩,
      ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
      ⟨⟨0, 61, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩,
    ⟨1, [⟨⟨0, 34, 1, 1, 0, 1⟩, 0, 0, 0⟩,
      ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
      ⟨⟨0, 81, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩]
    atStart := [⟨⟨noId, 0, 1, 1, 10, 1⟩, 1⟩]
    answers := 1
    last := [⟨0, 0, 1, 0⟩, ⟨1, 1, 4, 3⟩, ⟨2, 2, 3, 3⟩, ⟨3, 3, 3, 3⟩, ⟨4, 4, 0, 0⟩]
    choice := ⟨true⟩ }

/-- The program's own test on a shape says yes. -/
theorem shapeSmall_ok : reqShapeOk shapeSmall = true := by
  decide +kernel

/-- The groups that the program makes of it: k, h, and the switch's kept targets (main rows; kept
again). The last is the last test's first stage. -/
theorem shapeSmall_groups :
    (reqGroups shapeSmall).toList.map (fun G =>
      (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain))) =
    [(9, 0, []), (7, 0, [(3, false), (1, true)]), (9, 0, [(1, false)]),
      (7, 0, [(3, false), (1, true)]), (8, 0, [(1, false)]), (1, 0, [])] := by
  decide +kernel

/-- Along each link's list the moments do not fall: so "the link's list in its order" is "by
moment". -/
theorem shapeSmall_moments : (shapeSmall.link.all fun L =>
    (L.messages.zip (L.messages.drop 1)).all fun x => decide (x.1.moment ≤ x.2.moment)) = true := by
  decide +kernel

end VerifiableInference.Desc.ReqLit

#print axioms VerifiableInference.Desc.ReqLit.shapeSmall_ok
#print axioms VerifiableInference.Desc.ReqLit.shapeSmall_groups
#print axioms VerifiableInference.Desc.ReqLit.shapeSmall_moments
