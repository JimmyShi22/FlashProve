-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/Shapes.lean: the rounds of the layers' blocks, written out as lists.

Each block of Cb/Pv/Lay/ is a reduction whose shape is put together from the shapes of its parts.
Here the shapes of six blocks (the product layer, the merge, the weights' two stretches, the routed
experts', the squares') are given, each as one written list of rounds, for all sizes and for any
short sumcheck; the shapes of the folder's other blocks are not in this file. A list of a plan's
entries can then be laid beside it round by round.

The rounds that occur:
  `pRound0 E`: one scalar, then one element is drawn (the sum of the hiding polynomial; the
    coefficient);
  `sRound (pfCube E 2)` (the short round of Cb/G6/Johnson/Layers/Short.lean): two scalars, then one
    element is drawn (a variable's round);
  `sRound (pDummy E d)`: d scalars, then one element other than 0 is drawn (the round of the further
    variable);
  `pRoundV E A`: one scalar for each member of A, and nothing is drawn (the end values);
  `IOR.drawRound D`: an empty message, then a member of D is drawn;
  `sendRound E ι D`: one scalar for each member of ι, then a member of D is drawn.

Main names: `pscShape`, `ProdL.shape_eq`, `MergeL.shape_eq`, `WeightsL.shape_eq`,
`WFirstL.shape_eq`, `RoutedL.shape_eq`, `SquaresL.shape_eq`.

Limits: a shape says which types are sent and drawn from; it says nothing on names, kinds or work.

-/
import Cb.Pv.Lay.Squares
import Cb.Pv.Lay.WeightsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay
open Iop Prob Cb IOR Finset TWhole Johnson.L5.Layers

variable {E : Type} [Field E] [Fintype E]

theorem fmt_rep : ∀ g : ℕ, ldPartFmt E g (fun _ => 2) = List.replicate g (pfCube E 2)
  | 0 => rfl
  | g + 1 => by
    show pfCube E 2 :: ldPartFmt E g (fun _ => 2) = pfCube E 2 :: List.replicate g (pfCube E 2)
    rw [fmt_rep g]

/-- the rounds of a short sumcheck: k cube variables of degree 2, a further variable of degree d -/
noncomputable def pscShape (E : Type) [Field E] [Fintype E] (k d : ℕ) (A : Type) : Shape :=
  pRound0 E :: (List.replicate k (Johnson.L5.Layers.sRound (pfCube E 2)) ++
    [Johnson.L5.Layers.sRound (pDummy E d), pRoundV E A])

theorem shapeS_eq (k d : ℕ) (A : Type) :
    pRound0 E :: (Johnson.L5.Layers.sRounds (ldPartFmt E k (fun _ => 2) ++ [pDummy E d]) ++
      [pRoundV E A]) = pscShape E k d A := by
  unfold pscShape
  rw [fmt_rep]
  simp [Johnson.L5.Layers.sRounds]

theorem ProdL.shape_eq (L : ProdL E) {Ex : ExtSpec} (V : ShortK L.T.par Ex) :
    (L.blk V).shape = pscShape E L.k 2 Bool ++ [IOR.drawRound E] := by
  show V.R.shape ++ [IOR.drawRound E] = _
  rw [V.shape]
  exact congrArg (· ++ [IOR.drawRound E]) (shapeS_eq L.k 2 Bool)

theorem MergeL.shape_eq (L : MergeL E) {Ex : ExtSpec} (V : ShortK L.T.par Ex) :
    (L.blk V).shape = pscShape E L.k 1 Unit := by
  show V.R.shape = _
  rw [V.shape]
  exact shapeS_eq L.k 1 Unit

theorem WeightsL.shape_eq (G : WeightsL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) :
    (G.blk V).shape = IOR.drawRound E :: pscShape E G.k 1 Unit := by
  show IOR.drawRound E :: (G.L.blk V).shape = _
  rw [G.L.shape_eq V]

theorem WFirstL.shape_eq (G : WFirstL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) :
    (G.blk V).shape = sendRound E Unit E :: pscShape E G.k 1 Unit := by
  show sendRound E Unit E :: (G.L.blk V).shape = _
  rw [G.L.shape_eq V]

theorem RoutedL.shape_eq (G : RoutedL E) {Ex : ExtSpec} (V : ShortK G.L.T.par Ex) :
    (G.blk V).shape =
      IOR.drawRound (Fin G.g → E) :: (pscShape E (G.g + G.k') 2 Bool ++ [IOR.drawRound E]) := by
  show IOR.drawRound (Fin G.g → E) :: (G.L.blk V).shape = _
  rw [G.L.shape_eq V]

theorem SquaresL.shape_eq (G : SquaresL E) {Ex : ExtSpec} (V : ShortK G.R.L.T.par Ex) :
    (G.blk V).shape =
      sendRound E (Fin G.n × Fin G.ns) E :: IOR.drawRound (Fin G.g → E) ::
        (pscShape E (G.g + G.k') 2 Bool ++ [IOR.drawRound E]) := by
  show sendRound E (Fin G.n × Fin G.ns) E :: (G.R.blk V).shape = _
  rw [G.R.shape_eq V]

end Cb.Pv.Lay

#print axioms Cb.Pv.Lay.ProdL.shape_eq
#print axioms Cb.Pv.Lay.MergeL.shape_eq
#print axioms Cb.Pv.Lay.WeightsL.shape_eq
#print axioms Cb.Pv.Lay.WFirstL.shape_eq
#print axioms Cb.Pv.Lay.RoutedL.shape_eq
#print axioms Cb.Pv.Lay.SquaresL.shape_eq
