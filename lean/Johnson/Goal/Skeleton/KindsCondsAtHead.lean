-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Skeleton/KindsCondsAtHead.lean: `kindsConds_at_head`: under every head the structure
`KindsConds h h.free` (Johnson/Goal/Skeleton/KindsOfConds.lean) holds. One term.

Why. In the form of KindsOfConds.lean over which this file compiles, `KindsConds` has two fields, k9
and frame25. Each was a theorem from the head in its own file, but no theorem ended in `KindsConds`:
so the theorems that ask it (among them `sound_of_conditions_door_at`,
`sound_of_conditions_head_at`, `sound_of_conditions_free_at`, `sound_of_conditions_core_at`,
`kindsLaws_of_conds`) could not be said to be other than empty. Here the two are put together, at
the description's own data under the head and at `h.free` alone:
  k9       `P5J.k09_kind_of_head` (Johnson/P5J/K09EndC.lean)
  frame25  `P1L20.frameBehind_of_k9` (Johnson/P1L20R/FrameOfBehind.lean) at
           `P5J.k09_cond_of_head` (Johnson/P5J/K09CondHead.lean)

Limits. CALLS ALONE: NOTHING IS PROVED IN THIS FILE. What it is worth is what the three called
theorems are worth, with the limits that their files' heads and KindsOfConds.lean's tell. The two
fields are one road, not two: both go through `P5J.k9LastC_at_head` (Johnson/P5J/K09EndC.lean). That
there is a head is proved in the side library at `storedPublicFiles`, `zGap` (`headMember_zFull`,
`headMember_zGap`, AtFullSide/Top/, with those files' limits); at every Z in scope it follows where
the files are read and `protocolDataWellFormed` accepts (`P5J.head_of_live`, Johnson/P5J/HeadOfLive.lean). It
compiles over the form of KindsOfConds.lean with these two fields alone: a form with other fields
wants another term. The top, `sound_of_verify_at`, does not go through `KindsConds`.
No soundness is claimed.

-/
import Johnson.Goal.Skeleton.KindsLawsAtHead
import Johnson.Goal.Skeleton.KindsOfConds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifierAndGoals.AtTheName
open VerifierAndGoals FlashProve FlashProve
open P5J

/-- **The two fields under a head, each by its own file's theorem from the head.** -/
theorem kindsConds_at_head {Z : VerifierAndGoals.PublicFiles} {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) Zp Np cF x) :
    KindsConds h h.free :=
  ⟨k09_kind_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃,
    P1L20.frameBehind_of_k9 h h.free (k09_cond_of_head h h.free h.free_q₁ h.free_q₂ h.free_q₃)⟩

end VerifierAndGoals.AtTheName

#print axioms VerifierAndGoals.AtTheName.kindsConds_at_head
