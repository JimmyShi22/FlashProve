-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Loose/H2K12/ReachedAtHead.lean:
THE LAW OF THE PROXIMITY TEST (the kind K12) ON THE PROOF FILE's
FIRST CHAIN: THE HEAD WITH THE FACTS ON EVERY REACHED STATE (AtMgR, Johnson/P5J/AtMgR.lean), AT THE
HEAD's OWN CONDITION "REACHED" (AtMg.rch, Johnson/P5J/FourAtMg.lean), FROM THE HEAD AND THREE TESTS
ON THE PUBLIC PART. One theorem: one call of atMgR_madeRow
(Johnson/P5J/FoldJ3Whole.lean). It pays nothing of its own.
Main name:
  reached_at_head   the field reached of K12Rest₆ (H2K12/K12LeftOfRest.lean),
                    to the letter. The condition's first half is "reached" in the form RchAt
                    (Johnson/Top/H0/Walk/ReachAt.lean): that is the call's premise on the condition.
PREMISES THAT STAY, each a test with code on the public part, WITH WHO IS TO PAY:
  hl   the laying of the first chain's listed places returns L. Under the four equations that the
       entry test madeRow gives (Written354, H2K12/ClosedOfPins354.lean) the
       laying is that of the written notices at the written codes (laid_written there): a closed
       term, which returns (laid_full there).
  hs   the test startB (Johnson/Top/H0/Fill/D1At.lean) at the index masks' message's number in the
       table's numbers: the request announces one message at the chain's start, and its shape is the
       listed shape of that number. Under the same four equations and "the first chain's cut is the
       written one" it is a closed test at the number 4 (indexNo_at, H2K12/ClosedAtHead354.lean).
       No theorem says so.
  hy   the entry test madeRow (Johnson/Desc/Ok/PlanWritten/MadeTest.lean).
Limits. (1) A CALL: every fact on a reached state is another file's theorem. (2) A MEMBER OF THE
HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/); that hl, hs and hy
hold at any public files is no theorem. (3) At the concrete
second hash function alone; the full size alone. No soundness statement. Nothing on hiding.

-/
import Johnson.P5J.MgAtAll
import Johnson.P5J.FourAtMg
import Johnson.P5J.FoldJ3Whole

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

/-- **The head with the facts on every reached state, at the head's own "reached".** -/
theorem reached_at_head {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {L : VerifiableInference.Desc.K12.Door.Laid}
    (hl : P5J.At.laid? Zp = some L)
    (hs : VerifiableInference.Desc.First.FillP1.startB Zp
      (VerifiableInference.Desc.K12.Door.msgsOfChain Zp.made.proof.1)
      (P5J.At.N Zp cF).indexNo = true)
    (hy : VerifiableInference.PlanWritten.madeRow Zp = true) :
    P5J.AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) L :=
  P5J.atMgR_madeRow h.toAtMg h.toAtMg.rch (fun _ _ hr => hr.1) hl hs hy

end H2K12

#print axioms H2K12.reached_at_head
