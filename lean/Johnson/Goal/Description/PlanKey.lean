-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Description/PlanKey.lean: the plan that the frame lays and the plan of which the key
file's description is made are one; and the key's binding tree has one leaf there.
`chainsOf_key_oneLeaf`: `OnBytes.Model.Verify.planned_key_oneLeaf` (Johnson/Flat/PlanDepthZero.lean)
at `chainsOf` itself, at any digest of 32 bytes: its proof, step for step. `plannedAtO_of_madeAt`:
where `publicOfO o` returns X₀ and `Key.madeAt X₀ lay c` returns m, `plannedAtO o` at c returns m's
plan: the two run the same two steps of the planner. `thePlan_of_made`: so `thePlan` is the record
made of that plan. `thePlan_key`: where `protocolDataWellFormed` says yes,
`thePlan` is the record made of the plan of which the key file's description is made, and each of
that plan's seven strings of parameter bytes is shorter than 2 ^ 64 (the key's door asks it).
`thePlan_oneLeaf`: so the key's binding tree in `thePlan` has one leaf.
Limits. Of the proof file's description's plan nothing is said. `thePlan_key` and `thePlan_oneLeaf`
stand under `protocolDataWellFormed`'s yes; `protocolDataWellFormed` says yes at the written copies by theorem (AtFullSide/Top/),
as bytes by evaluation alone. Nothing on soundness.

-/
import Johnson.Goal.Description.KeySeat
import Johnson.Desc.Key.AsksLaw
import Johnson.Flat.PlanDepthZero
import OnBytes.TieK.G.SameChainsG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify
open OnBytes.Params (exc_bind)

/-- **In what `chainsOf` returns at a digest of 32 bytes the key's binding tree has one leaf**, if
the parameter bytes of the key's one-time chain are fewer than 2 ^ 64. -/
theorem chainsOf_key_oneLeaf {X : Public} {layout : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : chainsOf X layout c = .ok ch) (h32 : c.size = 32)
    (hb : (ch.bytes .keyOneTime).size < 2 ^ 64) : ch.key.oneTime.binding.logLeaves = 0 := by
  obtain ⟨r1, -, -⟩ := OnBytes.TieK.G.chainsOf_read h
  obtain ⟨shapes, hm⟩ := chainsOf_made h
  obtain ⟨-, ⟨P1, e1⟩, -, -⟩ := Params.configure_items hm
  obtain ⟨m, r, t, c', ll, F⟩ := TieK.oneTime_read_open (Params.KeyChains.read_parts r1).1
  have g1 := F.given
  have b1 : ch.bytes .keyOneTime = ch.made.keyOneTime := rfl
  rw [b1, e1] at g1 hb
  have t1 := Params.Given.read_items hb h32 (by
    intro y hy
    simp only [Plan.oneTimeItems, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl <;> (dsimp only; decide)) g1
  have q1 := F.items
  rw [t1] at q1
  simp only [Plan.oneTimeItems, List.cons.injEq, Prod.mk.injEq, true_and, and_true] at q1
  have w := F.binding
  rw [← q1.2.2.1] at w
  exact Params.readBinding_zero w

end OnBytes.Model.Verify

namespace FlashProve
open VerifierAndGoals
open OnBytes.Params (exc_bind)
open OnBytes.Model.Verify (chainsOf builtOf)
open VerifiableInference.PlanWritten (publicOfO plannedAtO)
open VerifiableInference.Desc.Key

/-- **The key's plan is the frame's planner's answer**, at one digest. -/
theorem plannedAtO_of_madeAt {o : SecondHashFunctionType} {pol KL lay c : ByteArray}
    {X₀ : OnBytes.Model.Verify.Public} {m : Johnson.G.OfPlan.Made}
    (hX : publicOfO o pol KL (some lay) = .ok X₀) (hm : madeAt X₀ lay c = .ok m) :
    plannedAtO o pol KL (some lay) c = .ok m.p ∧ chainsOf X₀ (some lay) c = .ok m.p.chains := by
  unfold madeAt at hm
  obtain ⟨chains, h1, hm⟩ := exc_bind hm
  obtain ⟨built, h2, hm⟩ := exc_bind hm
  obtain ⟨l, _, hm⟩ := exc_bind hm
  split at hm
  · cases hm
    refine ⟨?_, h1⟩
    unfold plannedAtO
    simp only [hX, h1, h2, bind, Except.bind, pure, Except.pure]
  · cases hm

/-- The frame's plan at what the key's maker returns. -/
theorem thePlan_of_made {Z : PublicFiles} {X₀ : OnBytes.Model.Verify.Public} {m : Johnson.G.OfPlan.Made}
    (hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀)
    (hm : madeAt X₀ Z.lay fixedDigest = .ok m) :
    thePlan (asDescriptionFiles Z) = VerifiableInference.OnPublicFiles.bigReq m.p := by
  have hl : thePlanLaid (asDescriptionFiles Z) = .ok (VerifiableInference.OnPublicFiles.bigReq m.p) := by
    show (plannedAtO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) fixedConfigurationDigest).map
      VerifiableInference.OnPublicFiles.bigReq = _
    rw [show fixedConfigurationDigest = fixedDigest from rfl, (plannedAtO_of_madeAt hX hm).1]
    rfl
  exact thePlanAt_ok hl

/-- **Where `protocolDataWellFormed` says yes, the frame's plan is the key file's description's.** -/
theorem thePlan_key (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∃ X₀ m, publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) = .ok X₀ ∧
      madeAt X₀ Z.lay fixedDigest = .ok m ∧
      thePlan (asDescriptionFiles Z) = VerifiableInference.OnPublicFiles.bigReq m.p ∧
      chainsOf X₀ (some Z.lay) fixedDigest = .ok m.p.chains ∧
      ∀ n : OnBytes.Model.Verify.ChainName, (m.p.chains.bytes n).size < 2 ^ 64 := by
  obtain ⟨X₀, m, X, N, P, hX, hm, _, _, _, _, ha, _, _⟩ := kseat_name Z live
  exact ⟨X₀, m, hX, hm, thePlan_of_made hX hm, (plannedAtO_of_madeAt hX hm).2, asks_bytes ha⟩

/-- **Where `protocolDataWellFormed` says yes, the key's binding tree in the frame's plan has one leaf.** -/
theorem thePlan_oneLeaf (Z : PublicFiles) (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    (thePlan (asDescriptionFiles Z)).k.oneTime.binding.logLeaves = 0 := by
  obtain ⟨X₀, m, _, _, hG, hc, hb⟩ := thePlan_key Z live
  rw [hG]
  exact OnBytes.Model.Verify.chainsOf_key_oneLeaf hc VerifiableInference.Desc.theCfg_size
    (hb .keyOneTime)

end FlashProve

#print axioms OnBytes.Model.Verify.chainsOf_key_oneLeaf
#print axioms FlashProve.plannedAtO_of_madeAt
#print axioms FlashProve.thePlan_of_made
#print axioms FlashProve.thePlan_key
#print axioms FlashProve.thePlan_oneLeaf
