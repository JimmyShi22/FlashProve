-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Head/HeadLight.lean: the output head's batching (member 347 of the first
chain, the batching of the head's row) at its light rows: BatchHeadFrame.lean at the light runs of
HeadCover.lean. Nothing is evaluated.

Why. A closed line on the light step then stands for the table's cell at this member. "Light" is as
in ClaimCovers.lean.

  headLightRows           the eleven rows' runs: equationsRunCovered, headThreeRunCovered at "norm",
                          "policy" and "logits", headJoinRunCovered at "join", the equal text of
                          "planes", else the table's.
  **headLightRows_standUnder**   they stand for the table's rows, at every shape.
  headBatchingLight, **headBatchingLight_standsUnder**   where the light step returns, the table's
                          cell at member 347 returns the same.

Limits. One way: where the light step refuses nothing is said, and that it returns at the shape in
front of member 347 is not said here. What any of this costs Lean's kernel is not measured here.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Lines.Head.BatchHeadFrame
import Johnson.AtFull.Shape.Lines.Head.HeadCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.K9.Shape
open VerifiableInference.Desc.Kinds.Head (parOf)
open VerifiableInference.Desc.Kinds.Head.Law (workAtW)
open VerifiableInference.Desc.Kinds.Head.Shape (headThreeRunCovered headJoinRunCovered
    headThreeRunCovered_standsUnder headJoinRunCovered_standsUnder)

/-- **The eleven rows' runs, five of them light, and "planes" in an equal text.** n: the length of
the reads. -/
def headLightRows (W : Verify.Public) (iU3 lm n : Nat) (o : Nat × String) :
    Nat → ChainSh → Except String (List ClaimSh × ChainSh) :=
  headLightRowsFrame W iU3 lm (headThreeRunCovered W.hS iU3 (parOf W.hS (workAtW W)) n)
    (headJoinRunCovered W.hS iU3 (parOf W.hS (workAtW W)) n) o

/-- The light rows stand for the table's, at every shape. -/
theorem headLightRows_standUnder (W : Verify.Public) (iU3 lm n : Nat) :
    RowsStandUnder (fun _ => True) (headLightRows W iU3 lm n) (fun o =>
        (tabOf (rowsHead W iU3 lm) o).g) :=
  headLightRowsFrame_standUnder W iU3 lm (fun _ _ _ _ h => headThreeRunCovered_standsUnder rfl h)
    (fun _ _ _ h => headJoinRunCovered_standsUnder rfl h)

/-- **The light step at member 347.** -/
def headBatchingLight (L : TabLetters) : ShA → Except String ShA :=
  headBatchingLightFrame L (fun iU3 n => headThreeRunCovered L.XG.hS iU3 (parOf L.XG.hS (workAtW
      L.XG)) n)
    (fun iU3 n => headJoinRunCovered L.XG.hS iU3 (parOf L.XG.hS (workAtW L.XG)) n)

/-- **Where it returns, the table's cell returns the same.** -/
theorem headBatchingLight_standsUnder (L : TabLetters) {x y : ShA} (h : headBatchingLight L x =
    .ok y) :
    (TabL.cells L 347).1 x = .ok y :=
  headBatchingLightFrame_atCell L (fun iU3 lm n => headLightRows_standUnder L.XG iU3 lm n) h

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.headLightRows
#print axioms Johnson.AtFull.Shape.headLightRows_standUnder
#print axioms Johnson.AtFull.Shape.headBatchingLight
#print axioms Johnson.AtFull.Shape.headBatchingLight_standsUnder
