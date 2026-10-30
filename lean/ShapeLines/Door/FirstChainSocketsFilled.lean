-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ShapeLines/Door/FirstChainSocketsFilled.lean: ONE LETTER AND THREE FIELDS OF TheOneObject (AtFullSide/Honest/TheOneObject.lean), IN THAT STRUCTURE's OWN FIELD TYPES, at every
tied run: the letter files (the named holes at the stored files), yes₁ (at every stand of the first thread the verifier's member steps), carry₁ (the family on shapes is carried
one member on) and startJ (the family at the first state). Statements with their proofs: calls alone.

  files_filled     the letter: theOpenFiles h (ShapeLines/Door/TheOpenFiles.lean)
  yes₁_filled      **the field yes₁**, from the maker's return
  carry₁_filled    **the field carry₁**, from the maker's return
  startJ_filled    **the field startJ**, from the structure's own field startFit

Limits. EACH OF yes₁, carry₁ IS AN IMPLICATION FROM THE FIRST THREAD's INVARIANT WITH ITS Said IN FRONT OF THE MEMBER, at challenges that fit, where nothing stops, no listed fall speaks
and the prover's side has moved: NOTHING HERE SHOWS THAT THE THREAD STANDS AT ANY BORDER OF ANY RUN. At the base prover's filling. The run on shapes and its 25 tests are closed lines of the
kernel at the stored full-size files, in this library; the laws are at every public files under the head. At member 354 the yes comes from another house's law on the proximity test
(Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLAcceptedWhole.lean): it is no closed line. startFit is another house's field. The full size and the hash function OnBytes.secondHashFunction alone.

What is not claimed. That the first chain accepts the honest prover. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.Honest.TheOneObject
import ShapeLines.Door.FirstChainFills

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000
/- Elaborated on one thread. Measured: with asynchronous elaboration the build of this file aborts (exit code 134, no message) under a cap of
32 GiB and passes under 96 GiB; with it off it passes under 32 GiB. The cause has not been looked into. -/
set_option Elab.async false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles)

/- The three instances that the structure's own file gives by hand. -/
local instance (priority := high) nonemptyPadZ_firstChainSockets : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_firstChainSockets : Nonempty RunValue :=
  ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_firstChainSockets : Inhabited RunValue :=
  ⟨fun _ => 0⟩

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {pp : Inst.Model.ScalesAndPolicy} (hr : readFiles Z = .ok pp)

/-- **The letter files.** -/
noncomputable def files_filled : TheLetters.OpenFiles A := ShapeLines.theOpenFiles h

/-- **The field yes₁.** -/
theorem yes₁_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.yes₁ h (TheLetters.first h) r.R (TheLetters.J₁ h (files_filled h))
      (TheLetters.falls₁ h) :=
  fun r => (ShapeLines.first_chain_filled_at_letters made h r.R).1

/-- **The field carry₁.** -/
theorem carry₁_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    ∀ r : TiedRun h hr, Socket.carry₁ h (TheLetters.first h) r.R (TheLetters.J₁ h (files_filled h))
      (TheLetters.falls₁ h) :=
  fun r => (ShapeLines.first_chain_filled_at_letters made h r.R).2

/-- **The field startJ**, from the field startFit. -/
theorem startJ_filled (startFit : ∀ r : TiedRun h hr, Socket.startFit h r.x) :
    ∀ r : TiedRun h hr, Socket.startJ h (TheLetters.J₁ h (files_filled h)) r.x :=
  fun r => ShapeLines.startJ_filled h r.x (startFit r)

/-- The letter and the three fields go into the structure by name; the two later chains' yes are handed through. -/
noncomputable example (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (T : TheThreadsHalf h hr)
    (y₂ : ∀ r : TiedRun h hr, Socket.yes₂ h (TheLetters.reads h) (TheLetters.shared h T.open₂) r.R [])
    (y₃ : ∀ r : TiedRun h hr, Socket.yes₃ h (TheLetters.first h) (TheLetters.reads h)
      (TheLetters.shared h T.open₂) (lastParts h (TheLetters.first h) (TheLetters.last h T.open₃))
      r.R []) : TheOneObject h hr :=
  { T with
    files := files_filled h
    yes₁ := yes₁_filled h hr made
    carry₁ := carry₁_filled h hr made
    yes₂ := y₂
    yes₃ := y₃
    startJ := startJ_filled h hr T.startFit }

end AtFullSide.Honest

#print axioms AtFullSide.Honest.files_filled
#print axioms AtFullSide.Honest.yes₁_filled
#print axioms AtFullSide.Honest.carry₁_filled
#print axioms AtFullSide.Honest.startJ_filled
