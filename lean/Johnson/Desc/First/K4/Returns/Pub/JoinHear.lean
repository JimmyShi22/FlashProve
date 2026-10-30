-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K4/Returns/Pub/JoinHear.lean: CONDITIONAL: HearPub
(Johnson/Desc/First/K4/Returns/Whole.lean) FROM THE PUBLIC TEST hearB AND WHAT STAYS A PREMISE. Lean
compares each of the six fields' texts with the end of the law that is laid in.

Limits. NO FILE OF THIS FOLDER PROVES hearB TRUE AT ANY PLAN (under the head, at each of the twelve
groups' plans: `hearPB_head`, Johnson/Desc/ProofFile/Honest/K4/Law/DearX.lean: hearPB is hearB and
more). Four premises stay. (1) The sizes of the points that the lookup hands over (zkFits, a test on
sizes): neither shapeFits nor K3Hands gives it, and it is not shown in this folder. (2) The
request's tokens (tokensFit). (3) JoinPub: that weighedOf, joinPart and laidOf return, two
comparisons with what the lookup leaves, and that no part of the join names a slot. (4) PointsRet,
the readings of the points and of the tables' weights. The last two are asked at the lookup's own
values, at the number and the places that the two equations name. PointsRet is shown in
JoinPoints.lean from a further test and three premises on what the lookup hands over (the last
coordinates of its point, the size of the token point, the planes' columns at its shape); JoinPub is
shown nowhere in this folder. The law hear_returns asks more beside HearPub: covers, shapeFits,
Room, TapeOf, PlanNums, K3Hands and two tests on sampled values (JoinTop.lean lists them in Lean).
No property is claimed.

  PointsRet      the field "points" of HearPub, as a proposition of its own.
  hearPub_of_B   the plan names the array of the reads, layTables returns, and at that number and
                 these places HearPub holds at every state of the lookup that meets the four
                 premises.
-/
import Johnson.Desc.First.K4.Returns.Pub.Hear
import Johnson.Desc.First.K4.Returns.Pub.JoinPans
import Johnson.Desc.First.K4.Returns.Pub.JoinClaims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.RtPub
open OnBytes OnBytes.Model OnBytes.Model.Layer

/-- The field "points" of HearPub. -/
def PointsRet (P : Pub) (g : Nat) (fo : Forest.Heard) (ztF : Array E)
    (laid : List (TableAsk × List (Nat × Nat))) : Prop :=
  ∀ (H : Heard) (hd hd2 : Level) (tT : Tsc), H.fo = fo → H.ztF = ztF → H.tT = some tT →
    tT.r.size = P.y.h.lt → H.PV.size = P.y.h.lt →
    H.ZE.size = (if (g == 0) = true then P.y.ls + P.y.h.lt else 0) → H.wpl.r.size = P.rd.muV →
    H.tV.r.size = P.y.h.lt → hd.r.size = P.rd.muH → hd2.r.size = P.rd.muH2 →
    ∃ pts funs, pointsOf P.y H hd (some hd2) = some pts ∧ funsOf P.y fo pts laid = some funs

/-- **HearPub from the public test**, at every state of the lookup that meets the four premises. The
two equations say at which number and places the premises are asked. -/
theorem hearPub_of_B {P : Pub} {hp : HPlan2} {g : Nat} (h : hearB P hp g = true) :
    ∃ iU3 tab laid n, hp.tl.ix.U.getD 2 none = some iU3 ∧ tablesAt P g = some (tab, laid, n) ∧
      ∀ (fo : Forest.Heard) (ztF : Array E), zkFits P fo.zk = true → tokensFit P g = true →
        Rt.JoinPub (Rt.envOf P hp g fo iU3 tab) fo → PointsRet P g fo ztF laid →
        Rt.HearPub P hp g fo ztF iU3 tab laid := by
  obtain ⟨iU3, tab, laid, n, hu, h0, ht, h1, h2, h3⟩ := hearB_parts h
  exact ⟨iU3, tab, laid, n, hu, ht, fun fo ztF hz hk hj hq =>
    { unit := hu, funOpen := h0, tables := tables_at ht h1, stack := stack_of_B h2 hj,
      claims := hearPub_claims h3 hk fo hz iU3 tab, points := hq }⟩

end OnBytes.Desc.First.K4.RtPub

#print axioms OnBytes.Desc.First.K4.RtPub.hearPub_of_B
