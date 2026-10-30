-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstReachPaid.lean: A JOIN OF TWO FILES THAT LIE; nothing new is proved here.
The sentence that the shared table's constant spends on every reached last state of the first chain
(Sh.ReachOwed, Johnson/Desc/K14/Law/SharedConstReachOwed.lean) from Sh.reachOwed_in_scope
(Johnson/Desc/K14/Law/SharedConstReachAt.lean), with its premise h5 paid by
Meaning.K2.h5_planOk (Johnson/IMR/EndFivePaid.lean).

  Sh.reachOwed_paid    in the goals' scope, at the value laid, at the second hash function itself:
                       ReachOwed … c L, under reachOwed_in_scope's seven premises and three more:
                       hP   the IOP as written in Lean passes its own test on the list of rounds
                       hB   at every opening, the closed test on what the 358 sub-protocols send
                       hLd  the written list L is what is laid of the first chain's own sendings
What is not claimed. hP, hB, hLd are shown nowhere here. At OnBytes.secondHashFunction alone. No soundness.

-/
import Johnson.Desc.K14.Law.SharedConstReachAt
import Johnson.IMR.EndFivePaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (First.S)
open VerifiableInference.Desc.K12 (guardedProximityTestParts)
open Johnson.G (codesFull2)
open VerifiableInference.Desc.K1 (realSized)
open H2K.JointK (descN)
open OnBytes.Params

namespace Sh

/-- **ReachOwed, with the five facts paid.** -/
theorem reachOwed_paid {S : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : LinSized} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl}
    {L : VerifiableInference.Desc.K12.Door.Laid} (hS : VerifierAndGoals.InScope S = true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (D, r))
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (descN OnBytes.secondHashFunction
                                   ProofFile.pureRoad.links guardedProximityTestParts Z N c))
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction S.pol S.lay S.KL = .ok Z)
    (hs : VerifiableInference.PlanWritten.sizedPinnedAt Z.p.X.P Z.p.chains.made = true)
    (hf : VerifiableInference.PlanWritten.firstPinnedAt Z.p.X.P Z.first = true)
    (hx : realSized = some (x, codesFull2))
    (hP : (descN OnBytes.secondHashFunction ProofFile.pureRoad.links guardedProximityTestParts Z N c).planOk = true)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction S.pol S.lay S.KL (descN OnBytes.secondHashFunction
                    ProofFile.pureRoad.links guardedProximityTestParts Z N c) Z Bs base c A B →
      VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358
        (VerifiableInference.Desc.K12.Door.snAt Z Bs.G₀ IM.placesW) = true)
    (hLd : VerifiableInference.Desc.K12.Door.laidAtCodes Z.first.codes Z.made.proof.1 = some L) :
    ReachOwed OnBytes.secondHashFunction Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c L :=
  reachOwed_in_scope hS hL hF hZ hs hf hx (Meaning.K2.h5_planOk hS hP hB hLd)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.reachOwed_paid
