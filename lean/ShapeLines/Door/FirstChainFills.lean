-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Door/FirstChainFills.lean: THE THREE FIELDS yes₁, carry₁, startJ AT THE LETTERS' NAMES, at the OpenFiles that the run on shapes gives (theOpenFiles), with the 25 tested runs laid in.

  first_chain_filled_at_letters   yes₁ ∧ carry₁ at thread₁, said₁, J₁ h (theOpenFiles h), falls₁
  startJ_filled                   from startFit, a field of its own

Limits. Those of first_chain_stored. Each speaks at stands of the thread; at the base filling.
Nothing on soundness, completeness or hiding.
-/
import ShapeLines.Door.TheOpenFiles
import ShapeLines.Equations.TestedBeforeEquations
import AtFullSide.K1.FirstChainAtLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

noncomputable section

namespace ShapeLines
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest.TheLetters
open ProofFile.Honest.Term (matrixInput)
open AtPublicFiles.AtFiles (FullSizeMatrix)
open OnBytes (TableKey)

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}

theorem first_chain_filled_at_letters
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A)
    (h : HeadAtReturn files A) (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) :
    (∀ b, b < (thread₁ h R).bs.length →
      AcceptedJ (thread₁ h R) (said₁ h R) (J₁ h (theOpenFiles h))
        (fallsBy (falls₁ h) h.description.first.blocksInOrder) b) ∧
    (∀ b, b < (thread₁ h R).bs.length →
      NextJ (thread₁ h R) (said₁ h R) (J₁ h (theOpenFiles h))
        (fallsBy (falls₁ h) h.description.first.blocksInOrder) b) :=
  first_chain_at_letters hA h R (theOpenFiles h)
    (fun X₀ hX l hl => firstChain_testedBeforeEquation l hl X₀ hX)
    (fun X₀ hX => firstChain_testedBeforeHeadEquation X₀ hX)

theorem startJ_filled (h : HeadAtReturn files A) (x : ProofFile.Inst)
    (hx : h.description.okStart x = true) :
    J₁ h (theOpenFiles h) 0 (h.description.start₁ (h.description.pub x)) :=
  startJ_at_letters h (theOpenFiles h) x hx

end ShapeLines

#print axioms ShapeLines.first_chain_filled_at_letters
#print axioms ShapeLines.startJ_filled
