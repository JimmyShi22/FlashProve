-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/Claims.lean: the claims. One named part of `VerifierAndGoals.theDescription`
(Description.lean), in a file of its own.
State: the true one. `theClaims`: the claims on requests at the reference shape's numbers and at
what the reader of the public files returned (scales and policy).

-/
import Johnson.Goal.Tie.DescriptionOfData
import Johnson.Flat.PolicyAtFrame
import Johnson.Flat.ThreeFull
import Johnson.Top.Fire.Code.Vals.DvFull

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

/-- The claims at one set of public files. -/
def theClaims (Zk : OnBytes.K.Pub) : (frS.toDecR frZ 402653181).Claims XF :=
  claimsReqAt (frS.toDecR frZ 402653181) numsRef (ppAtFiles Zk.pol Zk.KL)

end FlashProve
