-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/IndexAtHead.lean: TWO CLAUSES OF PlanAt AT THE INDEX MASKS' MESSAGE's SHAPE, UNDER
THE HEAD: clause one (K1's tie: the test tieB) and clause five (K12's files'
ShapeFits: the test fitsB), at the codes and the shape that the plan's sized proof
names: the terms of LLT25.vAt's field indexShape and of (p14At Zp).codes, written out. At every o.
HOW. Under the head the sized proof is the written one (the step inside AtMg.five_at_head,
Johnson/P5J/PlanSitsCore.lean: sized_in_scope over sized_of_made over AtMg.made_accepts): so both
tests are closed, and Lean's kernel evaluates them.
  indexShapeFull   the written shape, as a term with its type.
  tie_index_written · fits_index_written   the two closed facts, by the kernel.
  AtMg.sized_at_head   the sized proof is the written one.
  **AtMg.tie_index** · **AtMg.fits_index**   the two tests at the plan's own terms.
WHAT IT SERVES. Of PlanOk₃'s field planAt Johnson/LLT25R/PlanAtW.lean leaves four clauses: the
radius at W's member, and the tie, the radius and the fit at the index masks' member. These are the
tie and the fit, at that member's shape.
Limits. ShapeFits' FIRST ARM (main rows; the mask's code) IS FALSE AT THE WRITTEN SHAPE, BY LEAN's
KERNEL: so fits_index goes by the SECOND arm and KEEPS A PREMISE: hlg: the tree's told depth is at
most the stage's Z.a: A COMPARISON OF TWO NUMBERS THAT IS NOT SHOWN HERE. (That the first arm is
false at the written shape: IM.iShape_written, Johnson/IMR/SampleAtW.lean: no main rows; no theorem
of this file says it.) THAT A MEMBER OF THE JOIN's LIST HAS THIS SHAPE is the fields mineI and
oneSeat: not here. The two radii are not spoken of. NO MEMBER: that a head can be had is not said.
The full size alone. It leans on the door's asksAt2 (made_accepts).
(Where this and lean/THEOREM.md differ, the page holds.) Raised limits:
maxRecDepth 1000000 at the two closed facts. Nothing on soundness.

-/
import Johnson.P5J.PlanSitsCore
import Johnson.ToldDescR.TieB
import Johnson.LLT25R.PlanAtB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull)

set_option maxRecDepth 1000000 in
/-- Clause one at the written codes and the written shape: a closed fact. -/
theorem tie_index_written :
    ToldDesc.tieB proofSizedFull.codes
      ((proofSizedFull.request.atStart.head?.map (·.shape)).getD default) = true := by
  decide +kernel

/-- The written shape of the index masks' message. -/
def indexShapeFull : OracleShape :=
  (proofSizedFull.request.atStart.head?.map (·.shape)).getD default

set_option maxRecDepth 1000000 in
/-- The closed half of the SECOND arm of clause five there: mask rows, and the main code's index
beyond the table. (THE FIRST ARM IS FALSE AT THIS SHAPE: Lean's kernel said so of this file's second
typing.) -/
theorem fits_index_written :
    0 < indexShapeFull.maskRows ∧ proofSizedFull.codes.base.size ≤ indexShapeFull.code := by
  decide +kernel

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- Under the head the sized proof is the written one. -/
theorem AtMg.sized_at_head (h : AtMg o Z D r Zp Np cF) :
    Zp.p.chains.made.sized.proof = proofSizedFull :=
  VerifiableInference.PlanWritten.sized_in_scope h.scope h.laid.pub
    (VerifiableInference.PlanWritten.sized_of_made h.made_accepts)

/-- **CLAUSE ONE AT THE INDEX MASKS' MESSAGE's SHAPE.** -/
theorem AtMg.tie_index (h : AtMg o Z D r Zp Np cF) :
    ToldDesc.tieB Zp.p.chains.made.sized.proof.codes
      ((Zp.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) = true := by
  rw [h.sized_at_head]
  exact tie_index_written

/-- **CLAUSE FIVE THERE, WHERE THE TREE IS NO DEEPER THAN THE STAGE's MASK CODE.** -/
theorem AtMg.fits_index (h : AtMg o Z D r Zp Np cF) (st : Fmt.M1.Stage) (lg : Nat)
    (hlg : lg ≤ st.Z.a) :
    LLT25.fitsB Zp.p.chains.made.sized.proof.codes st
      ((Zp.p.chains.made.sized.proof.request.atStart.head?.map (·.shape)).getD default) lg =
      true := by
  rw [h.sized_at_head]
  exact (LLT25.fitsB_iff _ _ _ _).2
    (Or.inr ⟨fits_index_written.1, fits_index_written.2, hlg⟩)

end P5J

#print axioms P5J.tie_index_written
#print axioms P5J.fits_index_written
#print axioms P5J.AtMg.sized_at_head
#print axioms P5J.AtMg.tie_index
#print axioms P5J.AtMg.fits_index
