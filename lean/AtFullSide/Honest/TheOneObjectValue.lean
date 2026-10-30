-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/Honest/TheOneObjectValue.lean: the value of TheOneObject.

The online part has three chains. TheOneObject.lean lists what the honest prover owes at every served
request. theOneObjectValue is one term of that structure at the base filling: every field is its
filler by name. Its premises: h, hr, made, live and the two Inhabited letters of the frames.

Most fields are implications from a thread's invariant, so this does not show that a thread stands at
a run. open₂ is laid at zeros. This is a definition: no goal of the library, and it says nothing of
soundness, completeness or hiding by itself.
-/
import AtFullSide.Honest.DoorSocketsFilled
import AtFullSide.Honest.FixedSocketsFilled
import AtFullSide.Honest.LastSocketsFilled
import AtFullSide.Honest.OpenSharedFilled
import AtFullSide.Honest.OpensTakenFilled
import AtFullSide.Honest.OwesOneFilled
import AtFullSide.Honest.OwesTwoFilled
import AtFullSide.Honest.YesTwoFilled
import AtFullSide.K1.K1SocketsFilled
import AtFullSide.HonestTrace.TraceTiedAndStartSocketsFilled
import AtFullSide.K12.PlaysAtTreesFilled
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtTheLetters
import Johnson.Desc.ProofFile.Honest.K1.Pay.Whole
import Johnson.Desc.ProofFile.Honest.Law.ReadyPlugs
import ShapeLines.Door.FirstChainSocketsFilled

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.Honest
open ProofFile.Honest ProofFile.Honest.FirstThread
open ProofFile.Honest.Term (matrixInput matrixFilling tableCoins onlineMaker OnlineReturn
  onlinePayments_at_return readyDebts_online)
open ProofFile.Honest.K12.AtFile (openLast)
open AtPublicFiles.AtFiles AtPublicFiles.AtFiles.HonestTerm AtPublicFiles.Committed AtPublicFiles.TheFalls
open OnBytes (TableKey)
open OnBytes.Slice (frS)
open VerifierAndGoals (PublicFiles readFiles InScope)

local instance (priority := high) nonemptyPadZ_whatIsLeft : Nonempty PadZ :=
  pads_nonempty frS 402653181

local instance (priority := high) nonemptyRunValue_whatIsLeft : Nonempty RunValue := ⟨fun _ => 0⟩

local instance (priority := high) inhabitedRunValue_whatIsLeft : Inhabited RunValue := ⟨fun _ => 0⟩

variable {Z : PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {h : HeadAtReturn Z A}
  {pp : Inst.Model.ScalesAndPolicy} {hr : readFiles Z = .ok pp}

/-- The rooted sides, by part 5's law. -/
theorem rootedSides_filled (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A) :
    Socket.rootedSides h := by
  have whole := (ProofFile.Honest.K1.Pay.sides_are_whole matrixInput OnBytes.HonestTrace.Sz.ref openHonest
    rfl h.head made).2.1
  rwa [(atPure_at_laid h.head.laid made).2] at whole

variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]

/-- **THE VALUE OF THE OBJECT**: each field by its filler, with no hole left. -/
def theOneObjectValue (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL matrixFilling = .ok A)
    (live : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) : TheOneObject h hr where
  open₂ := open₂_filled A
  open₃ := openLast h made (open₂_filled A)
  readyDebts := readyDebts_online h.head (onlineMaker_returns made)
    (onlinePayments_at_return h.head (onlineMaker_returns made))
  traceAtTied := HonestTraceRun.Meets.traceAtTied_filled h hr live made
  planServes := planServes_filled h hr made h.head.scope live
  fix₂ := fix₂_filled h (open₂_filled A)
  fix₃ := fix₃_filled h hr (openLast h made (open₂_filled A)) made
  takenAre := takenAre_filled h (openLast h made (open₂_filled A))
  owes₁ := owes₁_filled made live
  owes₂ := owes₂_filled h.head.scope made (open₂_filled A) (HonestTraceRun.Meets.tied_filled h hr)
  owes₃ := owes₃_whole_filled h hr (openLast h made (open₂_filled A)) made
  playsAtTrees₃ := AtFullSide.K12.playsAtTrees₃_filled h hr made (open₂_filled A)
    (openLast h made (open₂_filled A))
  rootedSides := rootedSides_filled made
  tied := HonestTraceRun.Meets.tied_filled h hr
  opensTaken := opensTaken_filled h hr (openLast h made (open₂_filled A))
  startFit := HonestTraceRun.Meets.startFit_filled h hr live
  requestParses := HonestTraceRun.Meets.requestParses_filled h hr live
  served := HonestTraceRun.Meets.served_filled h hr made live
  doorTrees := doorTrees_filled h hr (openLast h made (open₂_filled A)) made
  doorFive := doorFive_filled h hr (openLast h made (open₂_filled A)) made
  doorRides := doorRides_filled h hr (openLast h made (open₂_filled A))
  files := files_filled h
  yes₁ := yes₁_filled h hr made
  carry₁ := carry₁_filled h hr made
  yes₂ := yes₂_filled h.head.scope made (open₂_filled A) (HonestTraceRun.Meets.tied_filled h hr)
  yes₃ := yes₃_whole_filled h hr (openLast h made (open₂_filled A)) made
  startJ := HonestTraceRun.Meets.startJ_filled h hr live (files_filled h)

end AtFullSide.Honest

#print axioms AtFullSide.Honest.rootedSides_filled
#print axioms AtFullSide.Honest.theOneObjectValue
