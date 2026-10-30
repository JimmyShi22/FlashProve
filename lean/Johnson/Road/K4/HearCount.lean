-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HearCount.lean: THE SLOTS THAT K4's HEARING TAKES ARE AS MANY AS THE MODEL's OWN
COUNT SAYS, and what the merge's record holds as shown is what the ledger shows. Statements and
proofs. It goes on where HearSlotsEnd.lean ends.

  `hear_count`: where the hearing `hear` returns over the plain engine, from a ledger F with arrays
    of the right sizes, at a plan whose lamS and NCL are `lamSOf` and `nclOf` of the layout: the
    next slot of the ledger G that it leaves satisfies, for every number small,
      G.next + Forest.elems P.y.fo + small = F.next + slotsOf P.y P.rd g P.wsLay.lk small.
    `slotsOf` (OnBytes/Model/LayerPlan.lean) is the function by which the plan counts a layer
    sub-proof's slots: the lookup's (Forest.elems), the own rounds', the smallness test's (small).
    The number small stands on both sides and cancels: it is idle.
    So the own rounds take just the slots that the plan counts for them, in the first group and in
    a later one. By the closed form `slotsOf_eq` (OnBytes/Tie/Pv/Lay/Slots.lean).
  `fork_shown`: where the merge's text `flatForkEnd` returns: the slot wo.sFv is below the number of
    slots of the ledger that it leaves, and every ledger later than that one shows, under wo.sFv,
    the element wo.fvp that the record holds.
  `hear_room`: where the hearing returns from such a ledger F: the next slot of the ledger that it
    leaves is at most F's number of slots. So every slot that the hearing took is a slot of the
    ledger's arrays.

Limits. A count: nothing on what lies under a slot beyond `fork_shown`. That F.next is
Forest.elems P.y.fo where the lookup has run, and that the plan's number of slots is `slotsOf` at
its smallness test's number, are not said here. That routed experts and terms are present comes
from the text's own test `covers`. One direction: from a return. The reading ρ is an idle letter.

-/
import Johnson.Road.K4.HearSlotsEnd
import OnBytes.Desc.First.K4.HearGrows
import OnBytes.Tie.Pv.Lay.Slots

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled)
open OnBytes.Desc.First.P1 (bind_some pure_some)
open OnBytes.Tie.Pv.Lay (slotsOf_eq)

variable {K : Type} [Field K] (ρ : Reading K)

include ρ in
/-- **The own rounds take just the slots that the plan counts for them.** -/
theorem hear_count {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u))
    (hl : hp.lamS = lamSOf P.y) (hn : hp.NCL = nclOf P.y g) (small : Nat) :
    G.next + Forest.elems P.y.fo + small = F.next + slotsOf P.y P.rd g P.wsLay.lk small := by
  have hc : covers P = true := by
    by_cases hg : (g == 0) = true
    · exact (hear_parts_first h hg).1
    · exact (hear_parts_later h (Bool.eq_false_iff.2 hg)).1
  unfold covers at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨-, p3⟩, -⟩, -⟩, c5⟩ := hc
  have tsc : P.rd.tscCalls.isEmpty = false := by
    cases e : P.rd.tscCalls.isEmpty with
    | false => rfl
    | true =>
      rw [e] at c5
      exact absurd c5 Bool.false_ne_true
  rw [slotsOf_eq]
  by_cases hg : (g == 0) = true
  · obtain ⟨_, _, _, _, n⟩ := hear_end_first ρ hF h hg
    rw [n]
    simp only [k4Slots, hPAt, kPAt, tClAt, sClAt, sPvAt, shownByTerms, nEndT, nclOf, hl, hn, p3,
      tsc, hg, if_true, Bool.false_eq_true, if_false]
    omega
  · have hg' : (g == 0) = false := Bool.eq_false_iff.2 hg
    obtain ⟨_, _, _, _, n⟩ := hear_end_later ρ hF h hg'
    rw [n]
    simp only [k4Slots, hPAt, kPAt, tClAt, sClAt, sPvAt, shownByTerms, nEndT, nclOf, hl, hn, p3,
      tsc, hg', if_true, Bool.false_eq_true, if_false]
    omega

/-- **What the merge's record holds as shown is what every later ledger shows.** -/
theorem fork_shown {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork} {t u : Tape}
    {wo : WsForkOut} (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.sFv < G.ns ∧ ∀ Hl : Fork, Fo.Later G Hl → Hl.vp.getD wo.sFv zeroE = wo.fvp := by
  unfold flatForkEnd at h
  obtain ⟨_, A1, a1, c1, k1⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c2
  obtain ⟨_, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp c3
  obtain ⟨x, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨m, rho⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k4
  unfold Fl.wsForkMerge at c4
  obtain ⟨rho', B1, b1, d1, j1⟩ := bind_some.mp c4
  obtain ⟨p0, B2, b2, d2, j2⟩ := bind_some.mp j1
  obtain ⟨x, B3, b3, d3, j3⟩ := bind_some.mp j2
  obtain ⟨rm, p1⟩ := x
  obtain ⟨x, B4, b4, d4, j4⟩ := bind_some.mp j3
  obtain ⟨sFv, p2⟩ := x
  obtain ⟨fvp, B5, b5, d5, j5⟩ := bind_some.mp j4
  obtain ⟨hs, rfl, rfl⟩ := P1.ask_some.mp d5
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp j5
  injection he with e1 e2
  subst e1
  obtain ⟨hlt, hfill, hy⟩ := P1.shown_some hs
  refine ⟨hlt, fun Hl hL => ?_⟩
  show Hl.vp.getD sFv zeroE = fvp
  rw [(hL.keep sFv hfill).2.1, hy]

include ρ in
/-- **Every slot that the hearing took is a slot of the ledger's arrays**: where it returns over the
plain engine from a ledger F with arrays of the right sizes. -/
theorem hear_room {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    G.next ≤ F.ns := by
  have hL : OnBytes.PscRun.Later F G := hearFl_later h
  rw [← hL.ns]
  by_cases hg : (g == 0) = true
  · obtain ⟨_, _, s, _, n⟩ := hear_end_first ρ hF h hg
    obtain ⟨_, _, _, _, H1, hd2, TS, cP, cE, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, _, _, _, _, _,
      _, _, _, _, _, hM⟩ := hear_parts_first h hg
    have := (fork_shown hM).1
    omega
  · have hg' : (g == 0) = false := Bool.eq_false_iff.2 hg
    obtain ⟨_, _, s, _, n⟩ := hear_end_later ρ hF h hg'
    obtain ⟨_, _, _, _, _, H1, hd2, TS, cP, G1, G2, G3, G4, u1, u2, u3, u4, _, _, _, _, _, _, _, _,
      hM⟩ := hear_parts_later h hg'
    have := (fork_shown hM).1
    omega

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hear_count
#print axioms OnBytes.Desc.First.K4.fork_shown
#print axioms OnBytes.Desc.First.K4.hear_room
