-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/ShapeAtEnd.lean: TWO NAMES FOR THE FIRST CHAIN's RUN ON SHAPES THAT NEED NO WRITTEN VALUE: the family J at the seat's own ground,
and the end of the run at a record of the stored files AS WHAT THE RUN RETURNS. So a file of definitions in the main library can name both,
while the written end (a large literal) and the kernel's lines on it stay in a library of their own.

  shapesAtSeat A        the family: shapeJ of the table at the seat's own ground, from startShA
  shapesAtSeat_of_base  it is the family at Bs.G₀ wherever baseOf returns Bs
  shapeAtEndOf X₀       what the run over all 358 members returns at the record X₀ (startShA where it returns nothing)
  shapeAtEnd_of_whole   from the whole run at the stored files: shapeAtEndOf X₀ = c
  shapesToEnd_of_whole  from the whole run: the run returns shapeAtEndOf X₀
  shapesEnd_of_whole    from the whole run and the end's test at c: the test at shapeAtEndOf X₀

Limits. Definitions and three rewritings. THE WHOLE RUN (hW) AND THE TEST AT ITS END (hE) ARE PREMISES. On shapes alone. Nothing on soundness,
completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.YesOfWhole
import Johnson.AtFull.Shape.Scope.EndLaws
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open ProofFile.Honest (OnlineProverWithDescription shapeJ)
open ProofFile.Honest.FirstThread (seatGround seatGround_of_base)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (publicOfO)

/-- **The family J of the first chain, at the seat's own ground.** -/
def shapesAtSeat {W₀ Rc Tr X₀ X : Type} (A : OnlineProverWithDescription W₀ Rc Tr X₀ X) : Nat → S → Prop :=
  shapeJ (firstZA (Tab.g A.Z (seatGround A)) (Tab.vals A.Z (seatGround A))) startShA

theorem shapesAtSeat_of_base {W₀ Rc Tr X₀ X : Type} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} {Bs : ProofFile.PureBase}
    (hB : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs) :
    shapesAtSeat A = shapeJ (firstZA (Tab.g A.Z Bs.G₀) (Tab.vals A.Z Bs.G₀)) startShA := by
  unfold shapesAtSeat
  rw [seatGround_of_base hB]

/-- **The end of the run on shapes at a record**: what the run returns. -/
def shapeAtEndOf (X₀ : Verify.Public) : ShA :=
  match (shapeL (LWn X₀)).run 358 startShA with
  | .ok c => c
  | .error _ => startShA

theorem shapeAtEnd_of_whole {c : ShA} (hW : RunsAll 0 358 startShA c) (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) :
    shapeAtEndOf X₀ = c := by
  unfold shapeAtEndOf
  rw [run_of_whole hW X₀ hX]

theorem shapesToEnd_of_whole {c : ShA} (hW : RunsAll 0 358 startShA c) (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀) :
    (shapeL (LWn X₀)).run 358 startShA = .ok (shapeAtEndOf X₀) := by
  rw [shapeAtEnd_of_whole hW X₀ hX]
  exact run_of_whole hW X₀ hX

theorem shapesEnd_of_whole {c : ShA} (hW : RunsAll 0 358 startShA c) (X₀ : Verify.Public)
    (hX : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (hE : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true) :
    endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape (shapeAtEndOf X₀) = true := by
  rw [shapeAtEnd_of_whole hW X₀ hX]
  exact hE

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.shapesAtSeat_of_base
#print axioms Johnson.AtFull.Shape.Scope.shapesToEnd_of_whole
#print axioms Johnson.AtFull.Shape.Scope.shapesEnd_of_whole
