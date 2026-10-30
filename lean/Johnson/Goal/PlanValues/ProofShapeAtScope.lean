-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/PlanValues/ProofShapeAtScope.lean: at every three public files in the goals' scope, the
shape of a proof file's test on the committed table, in what the program computes, passes the test
fullShapeB (Johnson/Desc/Sound/PlanAsk.lean): the table's code, its 2 ^ 11 rows and its one stored
OOD answer a row are the full size's, the matrix has 3076096 rows, and a row of the table holds 2 ^
7 of its columns. STATED AND PROVED.
  linFinish_three: what linSized's closing text returns has the table's shape indexShapeOf s T, and
      the lines' kLo and matrixRows: at all arguments.
  shape_full: whatever linSized returns at the typed lines, the written table and ANY codes passes
      fullShapeB.
  fullShape_at_scope: so at Model.Verify.planned's value at files in scope. fullShape_at_made: the
      same from Johnson.G.OfPlan.madeOf.
On what it rests. batch_at_scope (Johnson/Desc/K12/Law/Sizes/StageSizesAtScope.lean): the batch
is the sizing function's value at closed arguments but for the codes; linSized_named
(OnBytes/Params/Fit/KeySizedParts.lean); one closed evaluation by the kernel.
Limits. One direction: from a program that returns: that planned or madeOf returns at any files in
scope is not shown: no example of the two premises together is exhibited in Lean (runs say it of the
stored full-size set). It is stated at the library's planned, not at the plain road's planner
(ProofFile.Plain.planned): at o := the second hash function the two are meant to be one; not carried
here. The salt's bytes are left free, as fullShapeB leaves them. Nothing on soundness.

-/
import Johnson.Desc.K12.Law.Sizes.StageSizesAtScope
import Johnson.Desc.Sound.PlanAsk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify
open H2K.Sizes H2K.Member
open Desc.K14.Law (fullShapeB)

/-- What linSized's closing text returns has the table's shape and the lines' two numbers. -/
theorem linFinish_three {s : Setting} {L : LinLines} {T : TableSize} {codes c : Codes}
    {x y z : Sizing} {stU stO stW : List StageSize} {r : LinSized}
    (h : linFinish s L T codes x y z stU stO stW = some (r, c)) :
    r.shape.fold.index = indexShapeOf s T ∧ r.shape.kLo = L.kLo ∧
      r.shape.matrixRows = L.matrixRows := by
  unfold linFinish at h
  dsimp only at h
  split at h
  · obtain rfl := (Prod.mk.inj (Option.some.inj h)).1
    exact ⟨rfl, rfl, rfl⟩
  · cases h

/-- The closed evaluation. -/
theorem full_numbers :
    (decide (indexShapeOf recordSet recordTable =
        ⟨⟨32, 402653184, 44040191⟩, 11, 1, (indexShapeOf recordSet recordTable).saltBytes⟩) &&
      prLin.matrixRows == 3076096 && prLin.kLo == 7) = true := by decide +kernel

/-- **Whatever linSized returns at the typed lines, the written table and any codes passes
fullShapeB.** -/
theorem shape_full {codes c : Codes} {x : LinSized}
    (h : linSized recordSet prLin recordTable codes = some (x, c)) :
    fullShapeB x.shape = true := by
  obtain ⟨X, Y, Z, stU, stO, stW, _, _, _, _, hF⟩ := linSized_named h
  obtain ⟨e1, e2, e3⟩ := linFinish_three hF
  unfold fullShapeB
  rw [e1, e2, e3]
  exact full_numbers

/-- **fullShapeB in the goals' scope.** -/
theorem fullShape_at_scope {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {p : Verify.Planned}
    (hp : planned Z.pol Z.KL (some Z.lay) = .ok p) :
    fullShapeB p.chains.made.sized.proof.batch.shape = true := by
  obtain ⟨codes1, h⟩ := batch_at_scope hZ hp
  exact shape_full h

/-- The same from the structure that Johnson.G.OfPlan.madeOf makes of the three files. -/
theorem fullShape_at_made {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {m : Johnson.G.OfPlan.Made} (h : Johnson.G.OfPlan.madeOf Z.pol Z.lay Z.KL = .ok m) :
    fullShapeB m.p.chains.made.sized.proof.batch.shape = true :=
  fullShape_at_scope hZ (madeOf_planned h)

end Lk6.AtPlan

#print axioms Lk6.AtPlan.shape_full
#print axioms Lk6.AtPlan.fullShape_at_scope
#print axioms Lk6.AtPlan.fullShape_at_made
