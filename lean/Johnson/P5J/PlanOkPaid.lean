-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/PlanOkPaid.lean: WHICH OF THE NAMED TESTS ON THE LIST OF ROUNDS (PlanOk, Johnson/P5J/PlanOk.lean) ARE THEOREMS IN SCOPE ALREADY: SO THAT THE LIST SHRINKS WITHOUT THE STRUCTURE's FORM TURNING. Two theorems. A joint build of the files of several groups.
  At.shape_paid: IN SCOPE, WHERE Zp IS THE PLAIN ROAD's PUBLIC PART OF Z's OWN THREE FILES, AT EVERY SecondHashFunctionArgument o: the field "shape" (fullShapeB at the shared chain's shape) HOLDS: a theorem (Lk6.AtPlan.fullShape_pub, Johnson/Goal/PlanValues/ProofShapeAtPlain.lean), carried to the seat's own path by p14_shape.
  At.PlanOk.of_six: so PlanOk follows from scope, that equation and THE OTHER SIX TESTS.
Limits. It shows none of the other six to accept. That InScope Z = true and "the plain road returns" can be met together is not shown here. The full size alone. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.PlanOk
import Johnson.Goal.PlanValues.ProofShapeAtPlain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J.At
open VerifiableInference.Desc (Chain)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub}

/-- **The field "shape" is a theorem in scope.** -/
theorem shape_paid (hZ : VerifierAndGoals.InScope Z = true) (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp)
    (Np : H2U.Places4) :
    Desc.K14.Law.fullShapeB (Desc.K14.p14Of Zp.p.chains (Desc.K14.beforePointOf Np)).par.S = true := by
  rw [Desc.K14.Law.p14_shape]
  exact Lk6.AtPlan.fullShape_pub hZ h

/-- **PlanOk from the other six, in scope.** -/
theorem PlanOk.of_six (hZ : VerifierAndGoals.InScope Z = true) (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl)
    (laid : Meaning.laidThere (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) = true)
    (named : seatsNamedC (X Zp) (Meaning.sizesOf (X Zp)) (layout Zp) (num Zp) (arr Zp) (N Zp cF) = true)
    (fit : P5T.seatsFitP (F0T o Zp Np cF) (cs Zp) (pseats Zp) = true)
    (groups : P5T.groupsP (N Zp cF) (nG Zp) (pseats Zp) = true)
    (radii : P5T.radIsB ((P5T.rowsAt? Zp.pol Z.lay Zp.KL).getD []) Zp.made.proof.1.sends.length
      (rad Zp Z.lay) (pseats Zp) = true)
    (poss : VerifiableInference.Desc.First.possThereB cF.blocksInOrder links.length = true) :
    PlanOk o Zp Np cF Z.lay :=
  ⟨shape_paid hZ h Np, laid, named, fit, groups, radii, poss⟩

end P5J.At

#print axioms P5J.At.shape_paid
#print axioms P5J.At.PlanOk.of_six
