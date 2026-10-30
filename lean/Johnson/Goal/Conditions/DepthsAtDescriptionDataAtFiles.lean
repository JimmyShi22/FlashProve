-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Conditions/DepthsAtDescriptionDataAtFiles.lean: two equations by definition, stated as
  theorems: the two depths at which the frame's test on numbers is asked
  (G.c.first.binding.logLeaves · G.k.oneTime.binding.logLeaves) are the two depths of the
  description's own letters.
  sBG_logLeaves     (sBG G).logLeaves = G.c.first.binding.logLeaves := rfl        (the frame's
    depthReq at tAt)
  depthReqT_tOf     (S.inputFieldsAtReadings c m).depthReqT = S.G.k.oneTime.binding.logLeaves := rfl   (at every c m)
Nothing else. (verifierQueryCountBound_descriptionDataAtFiles, ToldBound.lean, leans on both by unification.)
No soundness is claimed.
-/
import Johnson.Flat.Told.Dec.LayoutsAtDescriptionDataAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals VerifiableInference VerifiableInference.OnPublicFiles OnBytes.Flat
open _root_.Iop (Dig)
open LPFD.Full (XF sBG)

attribute [local irreducible] LPFD.Full.mOneAt PV.EncId.encF PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8

theorem sBG_logLeaves (G : FilesParameters XF RecFull) : (sBG G).logLeaves = G.c.first.binding.logLeaves := rfl

theorem depthReqT_tOf {Zk : OnBytes.K.Pub} (S : DescriptionDataAtFiles Zk) (c : Digest) (m : List (Dig 256)) :
    (S.inputFieldsAtReadings c m).depthReqT = S.G.k.oneTime.binding.logLeaves := rfl

end FlashProve

#print axioms FlashProve.sBG_logLeaves
#print axioms FlashProve.depthReqT_tOf
