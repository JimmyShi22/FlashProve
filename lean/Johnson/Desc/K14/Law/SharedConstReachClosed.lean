-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/SharedConstReachClosed.lean: A JOIN; nothing new is proved here. Sh.reachOwed_full
(Johnson/Desc/K14/Law/SharedConstReachFull.lean) with its premise hB paid by
Meaning.K2.hB_paid (Johnson/IMR/EndFiveMade.lean): in
the goals' scope the key is the full size's (key_in_scope_pure, Johnson/Goal/Numbers/KeyInScope.lean),
so a yes of the law form madePinnedAt is a yes of the row madeRow (pinnedAt_row,
Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean).

  Sh.row_in_scope       in scope, madePinnedAt … = true gives madeRow Z = true
  Sh.reachOwed_closed   ReachOwed … c LFull, in scope, at the value that is laid, under hy (the one row
                        on written values), hx, and hP (the IOP as written in Lean passes its own test
                        on the list of rounds)
What is not claimed. hy, hx, hP are shown nowhere here. At OnBytes.secondHashFunction alone. No soundness.

-/
import Johnson.Desc.K14.Law.SharedConstReachFull
import Johnson.IMR.EndFiveMade

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

/-- In the goals' scope a yes of the law form is a yes of the row. -/
theorem row_in_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} {Z : ProofFile.Pub}
    (hS : VerifierAndGoals.InScope S = true) (hZ : ProofFile.pureRoad.pub o S.pol S.lay S.KL = .ok Z)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true) :
    VerifiableInference.PlanWritten.madeRow Z = true := by
  have e := VerifiableInference.PlanWritten.pinnedAt_row Z
  rw [if_pos (VerifiableInference.PlanWritten.key_in_scope_pure hS hZ)] at e
  exact e.symm.trans hy

/-- **ReachOwed at the written list, with the test on the sendings paid.** -/
theorem reachOwed_closed {S : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {x : LinSized} {Z : ProofFile.Pub} {N : H2U.Places4}
    {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} (hS : VerifierAndGoals.InScope S = true)
    (hL : LPFD.Full.proofDataAndDecisionOfPublicFiles OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (D, r))
    (hF : ProofFile.onlineDescription OnBytes.secondHashFunction S.pol S.lay S.KL = .ok (descN OnBytes.secondHashFunction
                                   ProofFile.pureRoad.links guardedProximityTestParts Z N c))
    (hZ : ProofFile.pureRoad.pub OnBytes.secondHashFunction S.pol S.lay S.KL = .ok Z)
    (hy : VerifiableInference.PlanWritten.madePinnedAt Z.p.X.P Z.p.chains.made Z.first Z.made = true)
    (hx : realSized = some (x, codesFull2))
    (hP : (descN OnBytes.secondHashFunction ProofFile.pureRoad.links guardedProximityTestParts Z N c).planOk = true) :
    ReachOwed OnBytes.secondHashFunction Z N (H2K.JointK.secondN guardedProximityTestParts Z N) c
      VerifiableInference.Desc.K13.Law.LFull :=
  reachOwed_full hS hL hF hZ hy hx hP (Meaning.K2.hB_paid hS hP (row_in_scope hS hZ hy))

end Sh

end Desc.K14.Law

#print axioms Desc.K14.Law.Sh.row_in_scope
#print axioms Desc.K14.Law.Sh.reachOwed_closed
