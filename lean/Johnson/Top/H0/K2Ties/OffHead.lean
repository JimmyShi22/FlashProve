-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/OffHead.lean: the code switch's law at the closed constant
(P5J.mgAtAll, Johnson/P5J/MgAtAll.lean): THE NAMED TEST offC (P5J.AtMg.offC, HidBearsAtMg.lean)
ACCEPTS UNDER THE HEAD AND THE PIN ALONE: OffAt.lean's offC_const with its third premise (the public
parameters have the full size's shape) paid from the head's own fields.
  fullShaped_head  under the head: X has the full size's shape:
               fullShaped_scope (Johnson/Goal/Meaning/NamedAskLaw.lean) at the head's fields scope ·
               reads · pubOne
  offC_head    h.offC = true from the head at the concrete second hash function and pin madePinnedAt
LIMITS. OffAt.lean's: the full size alone; under the pin, which is row 9 of the fourteen entry tests
that the verifier asks (row 10 is the written cut; AtHead.lean reads both off the head): a verifier
whose entry tests lack these two rows gives no such head; a member of the head is proved at storedPublicFiles
and zGap alone (at secondHashFunction; side library AtFullSide/Top/). No soundness is claimed.
-/
import Johnson.Top.H0.K2Ties.OffAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (madePinnedAt)
open _root_.Meaning.NamedAsk (fullShaped fullShaped_scope)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

theorem fullShaped_head (h : P5J.AtMg o Z D r Zp Np cF) : fullShaped Zp.p.X = true :=
  fullShaped_scope h.scope h.reads h.pubOne

/-- **offC, UNDER THE HEAD AND THE PIN ALONE.** -/
theorem offC_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) : h.offC = true :=
  offC_const h hy (fullShaped_head h)

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.fullShaped_head
#print axioms VerifiableInference.Desc.First.K2Ties.offC_head
