-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Door/TheOpenFiles.lean: A VALUE OF THE NAMED HOLES AT THE STORED FILES (OpenFiles, AtFullSide/Honest/TheLettersFirst.lean), UNDER THE HEAD AT A RETURN ALONE:
its shapeAtEnd is the written end border358; shapesToEnd is the whole run on shapes at the stored files (runOnShapes_toEnd,
ShapeLines/FirstChainRuns.lean); shapesEnd is the closed line endOk_358 (ShapeLines/Door/EndLines.lean).

  theOpenFiles h        the value
  theOpenFiles_end      its shapeAtEnd is border358

Limits. Under the head at a return of the maker; that the head can be met is not shown here. Its base and its record are chosen from "there is".
On shapes alone: no member's acceptance, no value. Nothing on soundness, completeness or hiding.
-/
import ShapeLines.FirstChainRuns
import ShapeLines.Door.EndLines
import Johnson.AtFull.Shape.Scope.OpenFilesRun

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ShapeLines
open AtPublicFiles.AtFiles (FullSizeMatrix)
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest.TheLetters (OpenFiles)
open Johnson.AtFull.Shape.Scope (openFilesOf)

variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

/-- **The value.** -/
noncomputable def theOpenFiles (h : HeadAtReturn Z A) : OpenFiles A :=
  openFilesOf h runOnShapes_toEnd endOk_358

theorem theOpenFiles_end (h : HeadAtReturn Z A) : (theOpenFiles h).shapeAtEnd = border358 := rfl

end ShapeLines

#print axioms ShapeLines.theOpenFiles
