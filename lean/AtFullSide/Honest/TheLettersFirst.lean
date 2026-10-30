-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheLettersFirst.lean: the first chain's letters of the proof file, as definitions.
TheLetters.lean, which imports this file, has the two later chains'; the head there says what the
letters are. This file stands apart so that the first chain's payers do not stand over the later
chains' files. OpenFiles is a structure of named holes.

Imports. No file is imported for a law: these hold definitions read here, and theorems beside them.
-/
import AtFullSide.Honest.TheThreeThreads
import AtFullSide.K1.FirstScript
import E2E.TheFalls
import Johnson.AtFull.Shape.LettersNumerals
import Johnson.AtFull.Shape.LettersRun
import Johnson.AtFull.Shape.RuleAtTable
import Johnson.AtFull.Shape.Scope.EndLaws
import Johnson.Desc.ProofFile.Honest.Thread.ShapeJ

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K1 (firstScriptAt)
open OnBytes (TableKey)
open VerifierAndGoals (PublicFiles)

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-! ## The first chain -/

/-- **numbers**: the stated numbers of the first chain's falls. -/
def numbers : FallNumbers where
  columns := K8.k8ColsAt A.G
  tau := K8.k8TauAt A.G
  share := P1K8.k8ShareAt A.Z A.G
  notGood := AtPublicFiles.TheFalls.noneNotGood
  roundsBefore := AtPublicFiles.TheFalls.roundsBeforeK4 h.firstChain

/-- **The first thread's parts**: the Script at the base filling's letters. -/
def first : FirstThreadParts A where
  script := firstScriptAt matrixInput OnBytes.HonestTrace.Sz.ref openHonest A h.firstChain
  numbers := numbers h

/-- **falls**, at the first chain. -/
abbrev falls₁ : List (Fall h.description.S₁) := firstFalls A (numbers h)

/-- falls at the shared chain: none. -/
abbrev falls₂ : List (Fall h.description.S₂) := []

/-- falls at the second chain: none. -/
abbrev falls₃ : List (Fall h.description.S₃) := []


/-- **A number and its place.** The first chain's debts are asked by number, and some kinds pay at
the written list P5J.At.ps, others at the chain's own list. This sentence joins the two. It is stated
here; `numberIsPlace_at_letters` (AtFullSide/K1/AtTheLetters.lean) proves it. -/
def NumberIsPlace : Prop :=
  ∀ (b : Nat) (blk : VerifiableInference.Desc.Block P5J.TS ProofFile.Cl),
    h.firstChain.blocksInOrder[b]? = some blk → P5J.At.ps[b]? = some blk.place

section Run
variable (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)

abbrev thread₁ := threadOne h (first h) R
abbrev said₁ := saidOne h (first h) R

end Run

/-! ## J, and the run on shapes -/

/-- **The named holes at the stored files.** The value of shapeAtEnd lies in
the side library ShapeLines. The seat's base is a value of the maker's seat at the return. -/
structure OpenFiles (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) where
  base : ProofFile.PureBase
  publicAtFiles : OnBytes.Model.Verify.Public
  shapeAtEnd : Johnson.AtFull.Shape.ShA
  seat : ProofFile.baseOf A.Z (ProofFile.pureSeat OnBytes.secondHashFunction A.Z) = .ok base
  publicData : VerifiableInference.PlanWritten.publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol
    VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok publicAtFiles
  shapesToEnd : (Johnson.AtFull.Shape.shapeL (Johnson.AtFull.Shape.LWn publicAtFiles)).run 358
    Johnson.AtFull.Shape.startShA = .ok shapeAtEnd
  shapesEnd : Johnson.AtFull.Shape.Scope.endOk
    VerifiableInference.PlanWritten.proofSizedFull.batch.shape shapeAtEnd = true

/-- **J**, at the first chain: the state has the shape that the run on shapes gives. At the two later
chains J says nothing. -/
abbrev J₁ (F : OpenFiles A) : Nat → h.description.S₁ → Prop :=
  shapeJ (Johnson.AtFull.Shape.firstZA (Johnson.AtFull.Shape.Tab.g A.Z F.base.G₀)
    (Johnson.AtFull.Shape.Tab.vals A.Z F.base.G₀)) Johnson.AtFull.Shape.startShA


end AtFullSide.Honest.TheLetters
