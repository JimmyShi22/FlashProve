-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/HeadOfLive.lean: THE CLOSED CONSTANT's HEAD (`AtMgA`, Johnson/P5J/MgAtAll.lean) HAS A
MEMBER WHEREVER THE LIVE TEST ACCEPTS, IN SCOPE, AT FILES THAT ARE READ: NO OTHER PREMISE. One
theorem: two calls. A law file.

Why. Every kind's law "from the head" is an implication from `AtMgA`. Whether the head can be met
hangs on two things: the live test and the condition `rowsRead` on the public files
(`head_exists_at_name`, HeadExistsAtName.lean beside this file). As the proof file's entry tests ask
`rowsMadeB` (test 14 of Johnson/Desc/Laid/ProofAsks.lean), the second follows from the first
(`owed_of_live`, Johnson/Goal/Skeleton/OwedOfLive.lean). So at a set of public files that is in
scope and is read, a yes of ONE Bool, `protocolDataWellFormed (asDescriptionFiles Z)`, is enough for the head to have a
member. The converse is not stated.

  head_of_live    in scope · the files are read · protocolDataWellFormed (asDescriptionFiles Z) = true ⊢ ∃ Zp Np cF x, AtMgA …

Limits. Its proof spends the yes of entry test 14 (`owed_of_live`). THE THREE
PREMISES ARE PREMISES: that a set of files is in scope, is read, and that the live test accepts it
is shown here of no files. Other Lean files prove them at `VerifierAndGoals.storedPublicFiles` and `VerifierAndGoals.zGap`: the
first two `VerifierAndGoals.filesRead` (Johnson/Goal/Files/FilesReadProof.lean), the third `theLive_zFull`,
`theLive_zGap` (AtFullSide/Top/LiveAtFull.lean, LiveAtPolicies.lean). Limits there. Nothing on how
many heads there are. The full size alone. At the second hash function. Nothing on soundness.
-/
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- **Where the live test accepts, in scope, there is a head.** -/
theorem head_of_live (Z : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy} (scope : VerifierAndGoals.InScope Z = true)
    (read : VerifierAndGoals.readFiles Z = .ok pp) (hl : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ Zp Np cF x, AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x :=
  head_exists_at_name Z scope read hl (owed_of_live hl)

end P5J

#print axioms P5J.head_of_live
