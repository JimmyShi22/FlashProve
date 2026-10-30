-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Own/DataThreeOwn.lean

THE FIRST THREE CLAUSES OF `DataFront`, WHERE THE FIRST FOLD SENDS ITS OWN TABLE: the twin of `dataThree_of_front`
(ManyFitsAt.lean in the folder above). `dataThree_many` is general in where the fresh table stands, so the twin turns
only what `frontFiveB` gave: that nothing passes is a premise here, for `frontFiveB` is false at this case by its mask.

  `dataThree_of_front_own`   the statement

HOW EACH PREMISE WOULD BE PAID AT jobKO. he: `early_of_planOk`. hp: `pass_of_five`, at `five_O` (KeyTenPubKernel.lean), under
`shape_doorOmegaF`. S: ShapeAsksOwn.lean's head. hS: `many_O` (KeyTenLinesKernel.lean), with the job's members
and trees against `bareO`'s, and the shape, `shape_doorOmegaF`.

Limits. As in ManyFitsLaw.lean. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.Own.ShapeAsksOwn
import Johnson.Desc.ProofFile.Honest.K12.ManyFitsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Own
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc.K12 (T12)
open H2K.First (Plain logAt)
open ProofFile.Honest.Sh (testSh claimsB)
open ProofFile.Honest.K12.Light (ManyJob manyFitsS many_of_S dataThree_many colsMany plainMany)

variable {W X : Type}

/-- **The three clauses at the plain data of `FrontAsksO`.** -/
theorem dataThree_of_front_own (A : ManyJob W X) (w : W) (fr : Front X) (K : Codes) (Dp : Plain)
    (he : A.p.early = true) (hp : (A.rec₀ w fr).pass = .nothing)
    (S : FrontAsksO A.toRun.toTest w fr K Dp)
    (hS : manyFitsS A.p (A.mems.map (·.shape)) A.trees
      (ProofFile.Honest.Sh.thinOf (testSh (A.rec₀ w fr))) = true) (C : TestCoins) :
    ColsAt A.s₀ Dp (colsMany A Dp.ts w fr C) (plainMany A w fr C) ∧
      StateAt A.s₀ Dp (A.toRun.toTest.first w fr C) (plainMany A w fr C) ∧
      A.toRun.toTest.trees₀ w fr C.mem (A.toRun.toTest.first w fr C) =
        groupTrees Dp.ts (logAt Dp.book) (colsMany A Dp.ts w fr C) := by
  rw [ProofFile.Honest.Sh.thinOf_eq] at hS
  have hc : claimsB (A.rec₀ w fr) = true := S.claims
  unfold claimsB at hc
  cases hG : (A.rec₀ w fr).st.groups[(A.rec₀ w fr).g]? with
  | none =>
    rw [hG] at hc
    cases hc
  | some G =>
    exact dataThree_many A Dp (many_of_S A.p _ _ _ hp he hS G hG Dp (S.plain G hG).1) w fr C

end ProofFile.Honest.K12.Own

#print axioms ProofFile.Honest.K12.Own.dataThree_of_front_own
