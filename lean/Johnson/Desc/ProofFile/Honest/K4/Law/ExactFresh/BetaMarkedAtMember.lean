-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K4/Law/ExactFresh/BetaMarkedAtMember.lean: CONDITIONAL: on hS, hR, L and
hG. The test on the rounds at the member of the first chain at a place of K4's: at each masked
sumcheck of the row `betaMarked` holds, which with `drawsFit` keeps the factor of the end values' mask
entries from 0.

  `k4_rounds_marked_at_member`   **`k4StatedAllB` at the member's own rounds and oracles.**

Limits. A test on the declared rounds: that the term's challenges keep to them is `drawsFit`'s, at a
caller. No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ExactFresh.AtLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.ExactFresh
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Block)
open P5J (TS LaidAt)

/-- CONDITIONAL: on hS, hR, L and hG. **At the member at a place of K4's the test on the rounds says
yes: at each masked sumcheck `betaMarked`, by `statedWalk`.** -/
theorem k4_rounds_marked_at_member {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {D : WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
    (hS : VerifierAndGoals.InScope Z = true) (hR : VerifierAndGoals.readFiles Z = .ok pp)
    (L : LaidAt OnBytes.secondHashFunction Z.pol Z.lay Z.KL D r Zp Np cF) {G₀ : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G₀) {x : Bool × Par}
    (hx : x ∈ ProofFile.k4From Zp G₀ G₀.built.toList 0 none) {Q : K4Pub} (hQ : k4PubOf Zp x.2 = some Q)
    {b : Block TS ProofFile.Cl} (hb : b ∈ cF.blocksInOrder) (hp : b.place = k4Place Q) :
    k4StatedAllB Q (b.rounds.zip b.oracles) = true := by
  obtain ⟨he, hs⟩ := k4_member_of_lot hS hR L hG hx hQ hb hp
  exact block_stated_shaped Q b he hs

end ProofFile.Honest.K4.ExactFresh

#print axioms ProofFile.Honest.K4.ExactFresh.k4_rounds_marked_at_member
