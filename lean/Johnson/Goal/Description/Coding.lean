-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Coding.lean: how an index is held. One named part of
`VerifierAndGoals.theDescription` (Description.lean), in a file of its own.
State: the true one. `theCoding`: `OnBytes.Flat.codingCells` (Johnson/Flat/CodingCells.lean) at the
full size's written code, the reference shape's numbers and what the reader of the public files
returned.
Limit. That the hypotheses on the key file's and the proof file's soundness are met at this
coding is not shown here; where they are proved, and how far: the head of
Johnson/Goal/TopOfThree.lean, limit (1).

-/
import Johnson.Goal.Description.Claims
import Johnson.Flat.CodingCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace FlashProve
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.SlotsBehindCutD
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Run
open _root_.Iop (Dig)
open LPFD.Full (XF GF sBG sTG saltG KF FsAtR)
open PV.EntryFive (dsF xsF)

def theCoding (Zk : OnBytes.K.Pub) : Coding (theClaims Zk) :=
  OnBytes.Flat.codingCells frS frZ 402653181 numsRef (ppAtFiles Zk.pol Zk.KL) Subtype.val

end FlashProve
