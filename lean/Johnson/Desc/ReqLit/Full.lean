-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ReqLit/Full.lean: THE REQUEST's SHAPE (`OnBytes.Params.ReqShape`) AT THE FULL-SIZE
EXAMPLE, AS A WRITTEN VALUE, for statements that Lean's kernel is to evaluate. Definitions, and two
theorems by an evaluation in the kernel. It imports OnBytes/Iop/Req.lean alone. The twin of
Small.lean, beside this file.

  `Full.linkG0`, `Full.linkA`, `Full.linkG`, `Full.linkH`: the four distinct links. `shapeFull :
    ReqShape`: the value: 25 links (the first; then the second and the first sort in turn; the
    last), 99 messages. `shapeFull_ok`: `reqShapeOk` says yes. `shapeFull_groups`: what `reqGroups`
    makes of it: 26 groups. Whence the numbers: a program wrote the value from a print that Lean's
    evaluator made of the planner's own request, `(OnBytes.Model.Verify.planned pol KL (some
    layout)).chains.made.sized.proof.request`, at the three shipped public files of
    prover/examples/target_full_f2: policy.txt (sha256 ce9e126b..4a3fae), layout.txt
    (a99b964b..3e8f80), KL.bin (1c319116..35b919). No other file was read.
Limits. Those of Small.lean: THE THEOREMS SPEAK OF THE WRITTEN VALUE; that it is the planner's
request at these three files is held by a run of Lean's evaluator outside the library, with a
control; no test that a build runs does. Nothing on soundness.

-/
import OnBytes.Iop.Req

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.ReqLit

open OnBytes OnBytes.Params

namespace Full

/-- The first link. -/
def linkG0 : ReqLink :=
  ⟨0, [⟨⟨0, 106, 1, 1, 0, 1⟩, 0, 0, 0⟩,
    ⟨⟨0, 9, 1, 0, noId, 1⟩, 0, 0, 1⟩,
    ⟨⟨0, 3, 1, 0, noId, 1⟩, 0, 0, 2⟩,
    ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
    ⟨⟨0, 31, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩

/-- A link of the second sort. -/
def linkA : ReqLink :=
  ⟨0, [⟨⟨0, 42, 1, 1, 0, 1⟩, 0, 0, 0⟩,
    ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
    ⟨⟨0, 14, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩

/-- A link of the first sort, from the third link on. -/
def linkG : ReqLink :=
  ⟨0, [⟨⟨0, 104, 1, 1, 0, 1⟩, 0, 0, 0⟩,
    ⟨⟨0, 9, 1, 0, noId, 1⟩, 0, 0, 1⟩,
    ⟨⟨0, 3, 1, 0, noId, 1⟩, 0, 0, 2⟩,
    ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
    ⟨⟨0, 31, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩

/-- The last link: one plain scalar goes in front. -/
def linkH : ReqLink :=
  ⟨1, [⟨⟨0, 103, 1, 1, 0, 1⟩, 0, 0, 0⟩,
    ⟨⟨0, 1, 3, 0, noId, 1⟩, 0, 1, 0⟩,
    ⟨⟨0, 24, 1, 0, noId, 1⟩, 0, 2, 0⟩]⟩

end Full

open Full in
/-- **The request's shape at the full-size example, as a written value.** A message: its shape
(code, main rows, degree of the main rows, mask rows, mask code, answers), its class of leaves,
its moment, its life. -/
def shapeFull : ReqShape :=
  { code := 0, maskCode := 0
    link :=
      [linkG0, linkA, linkG, linkA, linkG, linkA, linkG, linkA, linkG, linkA, linkG, linkA, linkG,
        linkA, linkG, linkA, linkG, linkA, linkG, linkA, linkG, linkA, linkG, linkA, linkH]
    atStart := [⟨⟨noId, 0, 1, 1, 12, 1⟩, 1⟩]
    answers := 1
    last := [⟨0, 0, 1, 0⟩, ⟨1, 1, 4, 3⟩, ⟨2, 2, 3, 3⟩, ⟨3, 3, 3, 3⟩, ⟨4, 4, 4, 4⟩, ⟨5, 5, 0, 0⟩]
    choice := ⟨true⟩ }

/-- The program's own test on a shape says yes. -/
theorem shapeFull_ok : reqShapeOk shapeFull = true := by
  decide +kernel

/-- The groups that the program makes of it: k, h, and the switch's kept targets (main rows; kept
again): the first link's; then twelve times the second sort's and the first sort's (the last of
these is the last link's); the last test's first stage. -/
theorem shapeFull_groups :
    (reqGroups shapeFull).toList.map (fun G =>
      (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain))) =
    (8, 0, []) ::
      ((List.replicate 12 [(7, 0, [(9, false), (3, true)]), (8, 0, [(3, false)])]).flatten ++
        [(1, 0, [])]) := by
  decide +kernel

/-- Along each link's list the moments do not fall: so "the link's list in its order" is "by
moment". -/
theorem shapeFull_moments : (shapeFull.link.all fun L =>
    (L.messages.zip (L.messages.drop 1)).all fun x => decide (x.1.moment ≤ x.2.moment)) = true := by
  decide +kernel

end VerifiableInference.Desc.ReqLit

#print axioms VerifiableInference.Desc.ReqLit.shapeFull_ok
#print axioms VerifiableInference.Desc.ReqLit.shapeFull_groups
#print axioms VerifiableInference.Desc.ReqLit.shapeFull_moments
