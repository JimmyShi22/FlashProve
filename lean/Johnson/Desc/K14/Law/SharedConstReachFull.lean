-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstReachFull.lean: A JOIN; nothing new is proved here. Sh.reachOwed_paid
(Johnson/Desc/K14/Law/SharedConstReachPaid.lean) AT THE WRITTEN LIST LFull
(Johnson/HB/LLHARD/LaidWritten.lean), under the yes of the one row on written values (madePinnedAt,
Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean): that row gives the two earlier tests (sized_of_made,
first_of_made) and, in the goals' scope, that LFull is what is laid of the first chain's own sendings
(laid_in_scope, Johnson/HB/LLHARD/PlanInScope.lean).

  Sh.reachOwed_full    ReachOwed … c LFull, in scope, at the value that is laid, under hy (the row),
                       hx, hP (the IOP as written in Lean passes its own test on the list of rounds)
                       and hB (at every opening, the closed test on what the 358 sub-protocols send)
What is not claimed. hy, hx, hP, hB are shown nowhere here. At OnBytes.secondHashFunction alone. No soundness.

-/
import Johnson.Desc.K14.Law.SharedConstReachPaid
import Johnson.HB.LLHARD.PlanInScope

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

/-- **ReachOwed at the written list, under the one row on written values.** -/
theorem reachOwed_full {S : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : LinSized} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} (hS : VerifierAndGoals.InScope S = true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (D, r))
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (descN OnBytes.secondHashFunction
                                   ProofFile.pureRoad.links guardedProximityTestParts Z N c))
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction S.pol S.lay S.KL = .ok Z)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hx : realSized = some (x, codesFull2))
    (hP : (descN OnBytes.secondHashFunction ProofFile.pureRoad.links guardedProximityTestParts Z N c).planOk = true)
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction S.pol S.lay S.KL (descN OnBytes.secondHashFunction
                    ProofFile.pureRoad.links guardedProximityTestParts Z N c) Z Bs base c A B →
      VerifiableInference.Desc.K12.Door.sendsAreB Z.made.proof.1 358
        (VerifiableInference.Desc.K12.Door.snAt Z Bs.G₀ IM.placesW) = true) :
    ReachOwed OnBytes.secondHashFunction Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c
      VerifiableInference.Desc.K13.Law.LFull :=
  reachOwed_paid hS hL hF hZ (VerifiableInference.PlanWritten.sized_of_made hy)
    (VerifiableInference.PlanWritten.first_of_made hy) hx hP hB
    (VerifiableInference.Desc.K13.Law.laid_in_scope hS hZ hy)

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.reachOwed_full
