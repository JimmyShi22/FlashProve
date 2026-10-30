-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OpenFilesRun.lean: THE NAMED HOLES AT THE STORED FILES (OpenFiles, AtFullSide/Honest/TheLettersFirst.lean) AGAINST THE RUN ON SHAPES' OWN
LAWS: what a value of that structure gives, and what makes one.

  whole_of_open     a value's fields publicData and shapesToEnd give the whole run at the stored files (RunsAll 0 358 startShA F.shapeAtEnd)
  yes_of_open       so the table's run on shapes says yes at 358 under the head, at the value's own base
  letterJ_is_seat   the letter J₁ at any value is the family at the seat's own ground (shapesAtSeat)
  openFilesOf       **a value**, under the head, from the whole run at the stored files and the end's test at its end

Limits. openFilesOf TAKES THE WHOLE RUN (hW) AND THE END's TEST (hE) AS PREMISES: closed lines of the kernel, in a library of their own. Its base and its
record are chosen from "there is" (the head's opened seat; record_there): they are no written values. On shapes alone. Nothing on soundness,
completeness or hiding.
-/
import AtFullSide.Honest.TheLettersFirst
import Johnson.AtFull.Shape.Scope.ShapeAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest.TheLetters (OpenFiles J₁)
open VerifiableInference.PlanWritten (publicOfO)

variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **A value of the holes holds the whole run at the stored files.** -/
theorem whole_of_open (F : OpenFiles A) : RunsAll 0 358 startShA F.shapeAtEnd :=
  runsAll_of_ex ⟨F.publicAtFiles, F.publicData,
    (run_is_from (shapeL (LWn F.publicAtFiles)) 358 startShA).symm.trans F.shapesToEnd⟩

/-- So the run on shapes says yes under the head, at the value's own base. -/
theorem yes_of_open (h : HeadAtReturn Z A) (F : OpenFiles A) :
    (firstZA (Tab.g A.Z F.base.G₀) (Tab.vals A.Z F.base.G₀)).yes startShA 358 = true :=
  yes_of_whole h.head F.seat (whole_of_open F)

/-- The letter J₁ is the family at the seat's own ground, whatever the value. -/
theorem letterJ_is_seat (h : HeadAtReturn Z A) (F : OpenFiles A) : J₁ h F = shapesAtSeat A :=
  (shapesAtSeat_of_base F.seat).symm

/-- The head's seat makes a base. -/
theorem seat_there (h : HeadAtReturn Z A) :
    ∃ Bs : ProofFile.PureBase, ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok Bs := by
  obtain ⟨Bs, _, O⟩ := h.head.laid.opened
  exact ⟨Bs, O.made⟩

/-- **A VALUE OF THE HOLES**, from the whole run and the end's test. -/
noncomputable def openFilesOf (h : HeadAtReturn Z A) {c : ShA} (hW : RunsAll 0 358 startShA c)
    (hE : endOk VerifiableInference.PlanWritten.proofSizedFull.batch.shape c = true) : OpenFiles A where
  base := Classical.choose (seat_there h)
  publicAtFiles := Classical.choose (record_there Johnson.Unfolds.Layout.lay_size)
  shapeAtEnd := c
  seat := Classical.choose_spec (seat_there h)
  publicData := Classical.choose_spec (record_there Johnson.Unfolds.Layout.lay_size)
  shapesToEnd := run_of_whole hW _ (Classical.choose_spec (record_there Johnson.Unfolds.Layout.lay_size))
  shapesEnd := hE

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.whole_of_open
#print axioms Johnson.AtFull.Shape.Scope.yes_of_open
#print axioms Johnson.AtFull.Shape.Scope.letterJ_is_seat
#print axioms Johnson.AtFull.Shape.Scope.openFilesOf
