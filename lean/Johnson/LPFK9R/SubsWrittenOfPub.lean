-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LPFK9R/SubsWrittenOfPub.lean: `ProofFile.subsOf Z = Johnson.AtFull.Desc.subsW`: THE PREMISE hk OF
`shape_written` (Johnson/AtFull/Desc/ShapeAtWritten.lean), TO THE LETTER: FROM THE
GOALS' SCOPE, THE READING OF THE FILES AND THE RETURN OF `ProofFile.pubPlain` ALONE: NO OPENING. Two
theorems: a closed line and a call.

  `linksW_subsW`: the written row `IM.linksW` is that file's written row `subsW`: by decide.
  `subs_written_of_pub`: **MAIN**: `subs_of_pub` (SubsOfPub.lean), then that line.
Limits. As in SubsOfPub.lean: at the second hash function alone; that pubPlain returns is a
premise. No soundness statement.

-/
import Johnson.LPFK9R.SubsOfPub
import Johnson.AtFull.Desc.ShapeAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

theorem linksW_subsW : IM.linksW = Johnson.AtFull.Desc.subsW := by decide

/-- **hk, FROM THE PUBLIC PART's RETURN.** -/
theorem subs_written_of_pub {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z) :
    ProofFile.subsOf Z = Johnson.AtFull.Desc.subsW :=
  (subs_of_pub hS hR hZ).trans linksW_subsW

end LPFK9

#print axioms LPFK9.linksW_subsW
#print axioms LPFK9.subs_written_of_pub
