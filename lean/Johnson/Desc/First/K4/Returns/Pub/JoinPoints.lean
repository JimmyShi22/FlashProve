-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/JoinPoints.lean: CONDITIONAL: THE HEARING OF THE SUB-PROTOCOL K4
RETURNS, WITH PUBLIC TESTS IN THE PLACE OF THE PREMISES ON layTables, callsTS, panelsT, stackEnd,
weightClaims, claimE, pointsOf AND funsOf: hearB (Hear.lean) with the test pointsB of
Johnson/Desc/First/K4/Returns/Points.lean, at the tables' places that the plan gives.

Limits. OF HearPub THERE STAYS JoinPub: that weighedOf, joinPart and laidOf return, two comparisons
with what the lookup leaves, and that no part of the join names a slot; it is asked at the lookup's
own values and shown nowhere in this folder. With it stay three tests on what the lookup hands over:
the sizes of the calls' points (zkFits), the planes' columns at its shape, and what K3Hands holds.
The request's tokens stay a premise (tokensFit). All other premises of hear_returns stand as they
stood, among them the two tests on sampled values. That the premises can be met together is not
shown: this folder gives no example. No file of this folder proves hearPB true at any plan (under
the head, at each of the twelve groups' plans: `hearPB_head`,
Johnson/Desc/ProofFile/Honest/K4/Law/DearX.lean). No property is claimed.

  hearPB              the two tests as one.
  hearPub_of_PB       HearPub from it.
  hear_returns_of_PB  hear_returns called at that member.
-/
import Johnson.Desc.First.K4.Returns.Pub.JoinHear
import Johnson.Desc.First.K4.Returns.Points

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.K.Kc D6.Ret
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.Desc.First.K4.Rt (TapeOf rowsNorms)

/-- **The two tests as one**: hearB, and the test on the points at the families that the plan
places. -/
def hearPB (P : Pub) (hp : HPlan2) (g : Nat) : Bool :=
  hearB P hp g && (tablesAt P g).any fun r => Rt.pointsB P g r.2.1

/-- **HearPub from the two tests.** Z: the last coordinates of the lookup's point. -/
theorem hearPub_of_PB {P : Pub} {hp : HPlan2} {g : Nat} (h : hearPB P hp g = true) :
    ∃ iU3 tab laid n, hp.tl.ix.U.getD 2 none = some iU3 ∧ tablesAt P g = some (tab, laid, n) ∧
      ∀ (fo : Forest.Heard) (Z ztF : Array E), zkFits P fo.zk = true →
        tokensFit P g = true → (lastOf fo.zx P.y.h.la).toOption = some Z →
        ztF.size = P.y.h.lt → (Forest.planeCols fo.shape P.y.h.lmb).toBool = true →
        Rt.JoinPub (Rt.envOf P hp g fo iU3 tab) fo → Rt.HearPub P hp g fo ztF iU3 tab laid := by
  unfold hearPB at h
  rw [Bool.and_eq_true] at h
  obtain ⟨iU3, tab, laid, n, hu, h0, ht, h1, h2, h3⟩ := hearB_parts h.1
  have hp' := h.2
  rw [ht] at hp'
  exact ⟨iU3, tab, laid, n, hu, ht, fun fo Z ztF hz hk hZ hzt hc hj =>
    { unit := hu, funOpen := h0, tables := tables_at ht h1, stack := stack_of_B h2 hj,
      claims := hearPub_claims h3 hk fo hz iU3 tab, points := Rt.points_pay hp' hZ hzt hc }⟩

/-- **The hearing returns**, from the two tests and what stays a premise. -/
theorem hear_returns_of_PB {P : Pub} {hp : HPlan2} {g : Nat} (hB : hearPB P hp g = true)
    (hk : tokensFit P g = true) :
    ∃ iU3 tab laid n, hp.tl.ix.U.getD 2 none = some iU3 ∧ tablesAt P g = some (tab, laid, n) ∧
      ∀ (fo : Forest.Heard) {F : Fork} {k : Nat} {t : Tape} {Z ztF : Array E}
      {ends : Array (Array E)}, covers P = true → shapeFits P fo = true →
      Room F (Rt.k4Takes P hp g + k) → TapeOf (rounds P hp g) t → Rt.PlanNums P hp g →
      Rt.K3Hands P fo F Z ztF ends → zkFits P fo.zk = true →
      (Forest.planeCols fo.shape P.y.h.lmb).toBool = true →
      Rt.JoinPub (Rt.envOf P hp g fo iU3 tab) fo → ends.all (· == Z) = true →
      (∀ t₁ s0 eps t₂, TapeOf (rowsNorms P g) t₁ →
        t = t₁ ++ ⟨some RoundName.pscEpsilon.name, 0, 0, s0, [eps]⟩ :: t₂ →
        isZeroE eps = false) →
      ∃ o G, hearFl P hp g fo F t = some (o, G, []) ∧ Room G k ∧ Below F G ∧
        G.next = F.next + Rt.k4Takes P hp g ∧ Rt.HearLeft P hp g fo iU3 tab F G o := by
  obtain ⟨iU3, tab, laid, n, hu, ht, h⟩ := hearPub_of_PB hB
  exact ⟨iU3, tab, laid, n, hu, ht, fun fo _ _ _ Z ztF _ hc hs hR hT hN hK hz hpc hj vM vE =>
    Rt.hear_returns P hp g fo hc hs hR hT hN hK
      (h fo Z ztF hz hk hK.z hK.ztSize hpc hj) vM vE⟩

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.hearPub_of_PB
#print axioms OnBytes.Desc.First.K4.RtPub.hear_returns_of_PB
