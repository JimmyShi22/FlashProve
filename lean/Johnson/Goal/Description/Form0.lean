-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Form0.lean: the form that the parser lays where a decoder refuses. One
named part of `VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: the true one. `theForm0`: empty files, and further tokens that are no tokens of the
vocabulary (`theForm0_aux`), so that the verifier says no there.

-/
import Johnson.Goal.Tie.DescriptionOnBytes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

open FlashProve (DecodedProof auxNo)

def emptyCarrier : Carrier.File :=
  ⟨ByteArray.empty, [], ByteArray.empty, 0, [], ByteArray.empty, [], ByteArray.empty, [], [], [],
      ByteArray.empty, 0, 0,
    ByteArray.empty, []⟩

def emptyLeaf : PV.EntryInOf.LeafP :=
  ⟨ByteArray.empty, [], ByteArray.empty, [], ByteArray.empty, [], [], [], []⟩

def theForm0 : DecodedProof where
  aux := auxNo
  cm := fun _ => false
  rcd := PV.Front.r0Full
  copy := 0
  fT := (LKF.FileInOf.ofCarrier "" ByteArray.empty emptyCarrier).inD
  e := ⟨fun _ => false, PV.Front.r0Full, ByteArray.empty, PV.EntryInOf.chainOut emptyLeaf, [], []⟩
  fB := (LKF.FileInOf.ofCarrier "" ByteArray.empty emptyCarrier).inD

theorem theForm0_aux : theForm0.aux = auxNo := rfl

end FlashProve
