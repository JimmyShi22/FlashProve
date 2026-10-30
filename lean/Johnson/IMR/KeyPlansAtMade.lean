-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/IMR/KeyPlansAtMade.lean: THE PINS AT Key.madeAt's OWN RETURN, A SECOND FILE:
THE KEY FILE's THREE PLANS: in the goals' scope, from the two returns hX (publicOfO's, at every o)
and hm (Key.madeAt's, at every digest): the setting is the written one; the three plans that the
planner has made for a key file are the three written plans; AND THE THREE PLANS THAT THE PROGRAM
READS BACK FROM THE PARAMETER BYTES ARE THESE.
It belongs to «the carrying of the pins». The first file: IMR/KeyPinsAtMade.lean.

WHAT IS SAID.
  keyPlans_at_chains   at the parameter file at any values of the eight free numbers, from ReadOf
                       and chainsOf's return.
  keyPlans_at_made     **in scope, from hX and hm.**
HOW. Calls alone. chainsOf_parts (OnBytes/Model/Fit/PlannedParts.lean) opens chainsOf's return:
the shapes, configure's return, AND THE READ-BACK's OWN EQUATION «KeyChains.read ‹the three strings
that configure has spelt› = some ch.key»: it is a step of chainsOf's text (the program reads its own
bytes back, and refuses where that reading refuses), no unfolding of a record. The setting:
sized_link. The made plans: keyPlans_of_configure with keySized_returns and
shapesOf_ranges. The plans read back: key_read_made (OnBytes/Model/ReadBackMade.lean), whose one
condition, that the made plans fit the format's words, stands as three closed facts: key_fit0 |
key_fit1 | key_fit2 (Johnson/Desc/Ok/NumberPrices/PlansAtWritten.lean).
What is not claimed. THAT EITHER RETURN IS HAD AT ANY FILES. THE SEVEN ITEMS THAT ARE READ BACK
BESIDE THE PLANS (the one-time chain's index masks, ranges, binding, codes and shape; the shared
chain's codes and shape): no law «reading undoes spelling» is shown for them.
The three sendings as written values. What declKOf and toldOfMade return. No soundness.

-/
import Johnson.IMR.KeyPinsAtMade
import Johnson.Goal.Numbers.KeyPlansOfConfigure
import Johnson.Desc.Ok.NumberPrices.PlansAtWritten
import OnBytes.Model.ReadBackMade
import OnBytes.Model.Fit.PlannedParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IM

open OnBytes OnBytes.Model OnBytes.Model.Config OnBytes.Model.Verify
open OnBytes.Params (recordLines recordSet)
open Lk6.AtPlan
open VerifiableInference VerifiableInference.Number.ByRuns
open Johnson.G.OfPlan (Made)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)

/-- At the parameter file at any values of the eight free numbers, any layout file, any digest. -/
theorem keyPlans_at_chains {v : VerifierAndGoals.FreeLines} {layout : Option ByteArray} {X : Public}
    {cfg : ByteArray} {ch : Chains} (hP : ReadOf (VerifierAndGoals.policyFile v) X)
    (hc : chainsOf X layout cfg = .ok ch) :
    ch.made.sized.set = recordSet ∧
      ch.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] ∧
      ch.key.oneTime.given.plan = keyThree.A.plan.plan ∧
      ch.key.shared.given.plan = keyThree.B.plan.plan ∧
      ch.key.second.given.plan = keyThree.C.plan.plan ∧
      Params.KeyChains.read ch.made.keyOneTime ch.made.keyShared ch.made.keySecond =
        some ch.key := by
  obtain ⟨links, shapes, hs, hm, hr, -⟩ := chainsOf_parts hc
  have hw := Johnson.RunOne.Law.UnitsInScope.wsLay_at_policy hP
  obtain ⟨y, hy, -⟩ := hP
  have hf := scan_frame (polLayout_scan hy)
  rw [hf] at hm
  have hk := keyPlans_of_configure hm (keySized_returns hw (shapesOf_ranges hs))
  have hfit : ∀ Q ∈ ch.made.key, Q.plan.fit = true := by
    intro Q hQ
    rw [hk] at hQ
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
    rcases hQ with rfl | rfl | rfl
    · exact key_fit0
    · exact key_fit1
    · exact key_fit2
  obtain ⟨g1, g2, g3⟩ := OnBytes.Params.key_read_made hm hr hfit hk
  exact ⟨(Params.sized_link (Params.configure_plans hm).1).1, hk, g1, g2, g3, hr⟩

/-- **The key file's three plans, made and read back, in scope.** -/
theorem keyPlans_at_made {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {o : ℕ → ByteArray → ByteArray} {X₀ : Public}
    (hX : PlanWritten.publicOfO o Z.pol Z.KL (some Z.lay) = .ok X₀) {cfg : ByteArray} {m : Made}
    (hm : Desc.Key.madeAt X₀ Z.lay cfg = .ok m) :
    m.p.chains.made.sized.set = recordSet ∧
      m.p.chains.made.key = [keyThree.A.plan, keyThree.B.plan, keyThree.C.plan] ∧
      m.p.chains.key.oneTime.given.plan = keyThree.A.plan.plan ∧
      m.p.chains.key.shared.given.plan = keyThree.B.plan.plan ∧
      m.p.chains.key.second.given.plan = keyThree.C.plan.plan ∧
      Params.KeyChains.read m.p.chains.made.keyOneTime m.p.chains.made.keyShared
        m.p.chains.made.keySecond = some m.p.chains.key := by
  obtain ⟨-, hc, -⟩ := madeAt_sends hm
  have hP := Johnson.RunOne.Law.ReadAtO.readOf_publicOfO hX
  obtain ⟨v, hv⟩ := inScope_policy hZ
  rw [hv] at hP
  exact keyPlans_at_chains hP hc

end IM

#print axioms IM.keyPlans_at_chains
#print axioms IM.keyPlans_at_made
