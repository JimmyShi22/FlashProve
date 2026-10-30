-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheLettersShared.lean: the shared chain's letters of the proof file, as definitions. The head of
TheLetters.lean says what the letters are.
-/
import AtFullSide.Honest.TheLettersFirst
import AtFullSide.K12.LaterDefs
import Johnson.Desc.ProofFile.Honest.Thread.TheLaterThreads

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest.TheLetters
open AtPublicFiles.AtFiles
open ProofFile.Honest ProofFile.Honest.FirstThread
open AtFullSide.Honest
open ProofFile.Honest.Term (readsBase laterBase)
open VerifiableInference.Desc (Place Block)
open OnBytes (TableKey)
open VerifierAndGoals (PublicFiles)

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)

/-- **rand**, with the index's reader. -/
abbrev reads : IndexReaders FullSizeMatrix IndexCommitterCoins := readsBase h

/-! ## The shared chain -/

/-- The shared chain's eight sub-protocols, from the plan. -/
def sharedBlocks : List (Block Desc.K14.St Unit) :=
  (Desc.K14.blocks (VerifiableInference.Desc.K1.qAt A.Z h.places)).getD []

/-- **keeps**, at the shared chain's members that neither K14 nor the test at U or O holds: the step
leaves the state. This is a choice; it stands for keepsEq
(Johnson/Desc/ProofFile/Honest/K12/AtFile/SharedStandTwelve.lean). -/
def keepsOff : Place → Desc.K14.St → Desc.K14.St → Prop := fun _ s s' => s' = s

/-- **What the shared chain's thread reads of the witness beyond K14's words.** Its value is openZero;
the houses that stand general in it stand at that value. -/
structure OpenShared (A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) where
  /-- the shared witness behind K14's messages. IOP's tops are general in it -/
  rest : Coins A.B → Common FullSizeMatrix IndexCommitterCoins TableKey → List Fmt.Drawn → WtShared

/-- A witness of zeros. -/
def zeroWitness : WtF := ⟨fun _ _ => 0, 0, fun _ _ _ _ => 0, fun _ _ _ _ _ => 0⟩

/-- **The value of OpenShared**: the shared witness behind K14's messages is zeros, a choice.
The first component is read by no clause of the shared thread; the second is
witAll's fallback off K14's own message numbers. That K12's rows at members 9 and 10 read only K14's
numbers is by reading mgWords. -/
def openZero : OpenShared A := ⟨fun _ _ _ => (zeroWitness, fun _ _ _ => 0)⟩

variable {h} in
/-- **later**: no rider. -/
def later (O : OpenShared A) : LaterLetters A :=
  laterBase h (sharedBlocks h)
    ((ProofFile.Honest.K12.AtProof.fourOf h.places).O.getD (ProofFile.Honest.K12.AtProof.fourOf h.places).U)
    O.rest [] keepsOff

/-- **The shared thread's parts.** -/
abbrev shared (O : OpenShared A) : SharedThreadParts A WtShared := sharedParts h (later (h := h) O)

section Run
variable {O : OpenShared A} (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit)

abbrev thread₂ := threadTwo h (reads h) (shared h O) R
abbrev said₂ := saidTwo h (reads h) (shared h O) R

end Run

end AtFullSide.Honest.TheLetters
