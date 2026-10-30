-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/LiveOfTwo.lean: In the goals' scope the test
`protocolDataWellFormed` (Johnson/Goal/Description/Live.lean) accepts wherever TWO of its three makers return a
value: the key file's (`theKeyLaid`) and the proof file's (`theProofLaid`).

Why. `theLive_of_returns` (Johnson/Goal/Skeleton/LiveOfReturns.lean) takes three returns and a bound
on two depths in the plan. The key file's maker runs the planner itself (at the constant `fixedConfigurationDigest`
in the digest's place, not at the digest of the files), so its return holds the third return, and
its own entry tests bound the lengths of the parameter bytes, from which the two depths follow.

Main names:
  `plan_of_key`: in scope, where `theKeyLaid` returns, `thePlanLaid` returns a plan whose two depths
    are 6 and 0.
  `theLive_of_two`: the statement above.

How. The opening is that of `kseat_name` (Johnson/Goal/Description/KeySeat.lean), begun at the
return and not at `protocolDataWellFormed`'s accept. Then `plannedAtO_of_madeAt`, `chainsOf_key_oneLeaf`
(Johnson/Goal/Description/PlanKey.lean) and `chainsOf_proof_binding`
(Johnson/Goal/Numbers/DepthAtThe.lean).

What is not claimed. THAT EITHER MAKER RETURNS A VALUE AT ANY FILES: so this is no example that
`protocolDataWellFormed` accepts anywhere. A yes of `protocolDataWellFormed` is no sign that the verifier accepts anything
(Johnson/Goal/Description/Live.lean). Nothing on soundness.

-/
import Johnson.Goal.Skeleton.LiveOfReturns
import Johnson.Goal.Description.PlanKey
import Johnson.Goal.Numbers.DepthAtThe

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace FlashProve
open VerifierAndGoals
open VerifiableInference.PlanWritten (publicOfO plannedAtO)
open VerifiableInference.Desc.Key

/-- **In scope, where the key file's maker returns, the plan's maker returns, and the two depths in
its plan are 6 and 0.** -/
theorem plan_of_key {Z : PublicFiles} (hZ : InScope Z = true)
    {K : OnBytes.Maker.WholeD × (OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
      _root_.Run.PQ.View → Bool)}
    (hK : theKeyLaid (asDescriptionFiles Z) = .ok K) :
    ∃ G : OnBytes.Flat.FilesParameters LPFD.Full.XF OnBytes.Flat.RecFull,
      thePlanLaid (asDescriptionFiles Z) = .ok G ∧ G.c.first.binding.logLeaves = 6 ∧
        G.k.oneTime.binding.logLeaves = 0 := by
  obtain ⟨D, r⟩ := K
  have hK' : (publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay)).bind
      (fun X => keyDataAndDecisionAtFixedDigest X Z.lay) = .ok (D, r) := hK
  cases hX : publicOfO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) with
  | error e => rw [hX] at hK'; cases hK'
  | ok X₀ =>
    rw [hX] at hK'
    obtain ⟨m, X, N, P, hm, _, _, _, _, _, _, _, ha, _, _⟩ := laidFixed_is X₀ Z.lay D r hK'
    have hb := asks_bytes ha
    obtain ⟨hp, hc⟩ := plannedAtO_of_madeAt hX hm
    refine ⟨VerifiableInference.OnPublicFiles.bigReq m.p, ?_, ?_, ?_⟩
    · show (plannedAtO OnBytes.secondHashFunction Z.pol Z.KL (some Z.lay) fixedConfigurationDigest).map
        VerifiableInference.OnPublicFiles.bigReq = _
      rw [show fixedConfigurationDigest = fixedDigest from rfl, hp]
      rfl
    · show m.p.chains.proof.first.binding.logLeaves = 6
      rw [OnBytes.Model.Verify.chainsOf_proof_binding hc
        (H2K.Sizes.publicO_at_scope hZ hX).frame VerifiableInference.Desc.theCfg_size
        (hb .proofFirst)]
    · exact OnBytes.Model.Verify.chainsOf_key_oneLeaf hc VerifiableInference.Desc.theCfg_size
        (hb .keyOneTime)

/-- **In scope: two returns give that `protocolDataWellFormed` accepts.** -/
theorem theLive_of_two (Z : PublicFiles) (hZ : InScope Z = true)
    {K : OnBytes.Maker.WholeD × (OnBytes.Flat.RecFull → _root_.Run.PQ.View → _root_.Run.PQ.View →
      _root_.Run.PQ.View → Bool)}
    {P : OnBytes.Maker.WholeD × (LPFD.Full.XF × OnBytes.Flat.RecFull → _root_.Run.PQ.View →
      _root_.Run.PQ.View → _root_.Run.PQ.View → Bool)}
    (hK : theKeyLaid (asDescriptionFiles Z) = .ok K) (hP : theProofLaid (asDescriptionFiles Z) = .ok P) :
    protocolDataWellFormed (asDescriptionFiles Z) = true := by
  obtain ⟨G, hG, h6, h0⟩ := plan_of_key hZ hK
  exact theLive_of_returns Z hZ hG hK hP (by omega)

end FlashProve

#print axioms FlashProve.plan_of_key
#print axioms FlashProve.theLive_of_two
