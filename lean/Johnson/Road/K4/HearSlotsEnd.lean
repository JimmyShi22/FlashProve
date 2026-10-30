-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HearSlotsEnd.lean: the slots' numbers at the end of the layers' own rounds: the
ledger behind the two gated layers, the slot of the embedding's hidden value, the merge's slots,
the ledger that the hearing leaves. Statements and proofs. It goes on where HearSlots.lean ends,
over the one chain of ledgers of OnBytes/Desc/First/K4/HearParts.lean. "Arrays of the right sizes"
is `Sized` (OnBytes/Tie/Pv/Psc/PscFork.lean): three of a ledger's arrays have one entry a slot.

  `gated_next`: from the four calls, the first from a ledger with arrays of the right sizes, each
    further one from the ledger that the one in front has left: the ledger behind the two gated
    layers has its arrays of the right sizes, and its next slot is the number nx of `k4Slots`.
  `wsForkRounds_next`: the merge's plain rounds keep the record's first slot and take two slots
    each.
  `first_ended`: the last round of a sumcheck keeps the record's first slot.
  `flatForkEnd_slots`: where the merge's text `flatForkEnd` (OnBytes/K/Kc/QuietLink.lean) returns
    from a ledger with arrays of the right sizes and next slot n: its sumcheck's first own slot is
    n, its end value's slot is n + 1 + 2 lk + 1, and the ledger that it leaves has arrays of the
    right sizes and n + 1 + 2 lk + 2 as its next slot. lk is the field of the layout handed in.
  `hear_end_first`: where the hearing returns in the first group from such a ledger: the field for
    the slot of the embedding's hidden value holds nx, and the merge's numbers are those at
    n = nx + 1.
  `hear_end_later`: in a later group: that field holds 0, and the merge's numbers are those at
    n = nx.

The walk through the ledgers in `gated_next` is that of `hear_slots`' proof, typed a second time
with the four calls as premises. One direction: from a return. Numbers of slots alone: nothing on
what lies under a slot. That every slot taken is below the ledger's number of slots, and that the
sum of these numbers is the model's own count of a sub-proof's slots, stands in
Johnson/Road/K4/HearCount.lean (`hear_room`, `hear_count`). The reading ρ is an idle letter.

-/
import Johnson.Road.K4.HearSlots
import OnBytes.Desc.First.K4.HearParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.PscRun (Sized Filled hideRun_ok)
open OnBytes.Desc.First.P1 (level_world tsc_world levelIn_heard tscIn_heard pscRow_spec
  claimsIn_spec bind_some pure_some need_some)

variable {K : Type} [Field K] (ρ : Reading K)

include ρ in
/-- **The ledger behind the two gated layers.** -/
theorem gated_next {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {v : Env}
    {H1 H : Heard} {S : HeardStack} {hd hd2 : Level} {F G1 G2 G3 G4 : Fork}
    {t u1 u2 u3 u4 : Tape} (hF : Sized F)
    (hN : hearNorms engFl P g fo F t = some (H1, G1, u1))
    (hT : hearTerms engFl P H1 G1 u1 = some (H, G2, u2))
    (hK : hearStack engFl P v H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2 u2 =
      some (S, G3, u3))
    (hG : hearGated engFl P H S G3 u3 = some ((hd, hd2), G4, u4)) :
    Sized G4 ∧ G4.next = (k4Slots P hp g F.next).nx := by
  obtain ⟨tT, G1', u1', row, p', cT, _, cR, hH⟩ := hearTerms_calls hT
  -- the norms' stretch
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := norms_slots ρ hF hN hH
  obtain ⟨F7, F8, _, _, _, hS8, _, _, c10⟩ := norms_chain ρ hF hN hH
  obtain ⟨_, hSG1, _, _, n1, _⟩ := tsc_world ρ (fun _ => 0) (fun _ _ _ => 0) hS8 c10
  -- the terms' sumcheck
  obtain ⟨hlt, _, _, _, _, _, _, _, _, _, tCl, _⟩ := tscIn_heard cT
  obtain ⟨_, hSG1', tP, tEnd, n2, _⟩ := tsc_world ρ (fun _ => 0) (fun _ _ _ => 0) hSG1 cT
  have hlenT : (H1.ztF.toList.take P.y.h.lt).length = P.y.h.lt := by
    rw [List.length_take, Array.length_toList, Nat.min_eq_left hlt]
  obtain ⟨_, _, hR⟩ := pscRow_spec cR
  have hp' := pscRow_rec cR
  obtain ⟨hSameR, hSG2, _, _⟩ := hideRun_ok _ G2 _ _ _ hSG1' hR
  have n2' : G2.next = G1'.next := hSameR.next
  -- the batched sumcheck
  obtain ⟨x, mu0, eps, beta, T, rs, sentY, vals, w1, wY, wV, C, Gs, ms, y, p, _, _, _, _, _,
    _, _, _, _, _, _, _, hsA0, hsH1, hsB0, hsV, _, hGs, _, hG3⟩ := hearStack_tape hK
  have hF2' : Sized ({ G2 with next := G2.next + 1 + 2 * hp.lamS + 2 + (2 + (1 + P.y.LamM) +
      (hp.NCL - (if (g == 0) = true then 1 else 0))) } : Fork) := hSG2
  obtain ⟨hSameS, hSGs, _, _⟩ := hideRun_ok _ Gs _ _ _ hF2' hGs
  obtain ⟨hSame3, hSG3, _, _⟩ := hideRun_ok _ G3 _ _ _ hSGs hG3
  have n3 : G3.next = G2.next + 1 + 2 * hp.lamS + 2 + (2 + (1 + P.y.LamM) +
      (hp.NCL - (if (g == 0) = true then 1 else 0))) := hSame3.next.trans hSameS.next
  -- the two gated layers
  obtain ⟨_, _, _, _, _, _, Ga, ua, ub, cA, cB⟩ := hearGated_parts hG
  obtain ⟨_, hSGa, nA, _⟩ := level_world ρ (fun _ => 0) (fun _ _ _ => 0) hSG3 cA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hLA, _⟩ := levelIn_heard cA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hLB, _⟩ := levelIn_heard cB
  -- the numbers
  have m1 : G1.next = tClAt P F.next := by
    unfold tClAt
    rw [n1, a6]
  have m2 : G2.next = kPAt P F.next := by
    unfold kPAt
    rw [n2', n2, tEnd, hlenT, m1]
  have m3 : G3.next = hPAt P hp g F.next := by
    unfold hPAt
    rw [n3, m2]
  obtain ⟨_, hSG4, nB, _⟩ := level_world ρ (fun _ => 0) (fun _ _ _ => 0) hSGa cB
  refine ⟨hSG4, ?_⟩
  show G4.next = hPAt P hp g F.next + 1 + 2 * P.rd.muH + 2 + 2 + 1 + 2 * P.rd.muH2 + 2 + 2
  rw [nB, nA, m3]

/-- The merge's plain rounds: the record's first slot stays, and each round takes two slots. -/
theorem wsForkRounds_next : ∀ {n : Nat} {rm rm' : Array E} {p p' : Psc} {F G : Fork} {t u : Tape},
    Fl.wsForkRounds n rm p F t = some ((rm', p'), G, u) →
    p'.first = p.first ∧ G = { F with next := F.next + 2 * n }
  | 0, rm, rm', p, p', F, G, t, u, h => by
    unfold Fl.wsForkRounds at h
    obtain ⟨he, rfl, rfl⟩ := pure_some.mp h
    injection he with e1 e2
    exact ⟨by rw [e2], rfl⟩
  | n + 1, rm, rm', p, p', F, G, t, u, h => by
    unfold Fl.wsForkRounds at h
    obtain ⟨x, G1, u1, h1, k1⟩ := bind_some.mp h
    obtain ⟨r, q⟩ := x
    obtain ⟨_, sent, k, _, rfl, rfl, _⟩ := P1.roundIn_sum2_tape h1
    obtain ⟨a1, a2⟩ := wsForkRounds_next k1
    refine ⟨a1, ?_⟩
    rw [a2]
    show ({ F with next := F.next + 2 + 2 * n } : Fork) = _
    have : F.next + 2 + 2 * n = F.next + 2 * (n + 1) := by omega
    rw [this]

/-- The record behind the last round holds the first slot that it held in front. -/
theorem first_ended (p : Psc) (m : P1.Rnd) :
    ({ P1.stepP p m with ended := true } : Psc).first = p.first := rfl

/-- **The merge's slots**, where its text returns from a ledger with arrays of the right sizes. -/
theorem flatForkEnd_slots {lay : WsLay} {cl : Array WsClaim} {sv : Array Nat} {F G : Fork}
    {t u : Tape} {wo : WsForkOut} (hF : Sized F)
    (h : flatForkEnd lay cl sv F t = some (wo, G, u)) :
    wo.p.first = F.next ∧ wo.sFv = F.next + 1 + 2 * lay.lk + 1 ∧ Sized G ∧
      G.next = F.next + 1 + 2 * lay.lk + 2 := by
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
  obtain ⟨_, rfl, _⟩ := P1.batch_spec d1
  obtain ⟨p0, B2, b2, d2, j2⟩ := bind_some.mp j1
  obtain ⟨T, mu, eps, _, rfl, rfl⟩ := P1.pscBegin_spec d2
  obtain ⟨x, B3, b3, d3, j3⟩ := bind_some.mp j2
  obtain ⟨rm, p1⟩ := x
  obtain ⟨f1, rfl⟩ := wsForkRounds_next d3
  obtain ⟨x, B4, b4, d4, j4⟩ := bind_some.mp j3
  obtain ⟨sFv, p2⟩ := x
  obtain ⟨_, sentY, beta, v, _, _, rfl, rfl, hG⟩ := P1.pscEnds_spec d4
  obtain ⟨fvp, B5, b5, d5, j5⟩ := bind_some.mp j4
  obtain ⟨_, rfl, rfl⟩ := P1.ask_some.mp d5
  obtain ⟨he, rfl, rfl⟩ := pure_some.mp j5
  injection he with e1 e2
  subst e1
  have hG' : ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork).hideRun
      (F.next + 1 + 2 * lay.lk + 1) v beta = some _ := hG
  have hF' : Sized ({ F with next := F.next + 1 + 2 * lay.lk + 2 } : Fork) := hF
  obtain ⟨hSame, hS, _, _⟩ := hideRun_ok _ _ _ _ _ hF' hG'
  refine ⟨?_, rfl, hS, hSame.next⟩
  exact (first_ended p1 _).trans f1

include ρ in
/-- **The end of the hearing in the first group**, from a ledger with arrays of the right sizes:
the slot of the embedding's hidden value, the merge's two slots, the ledger that is left. -/
theorem hear_end_first {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u))
    (hg : (g == 0) = true) :
    o.sVE = (k4Slots P hp g F.next).nx ∧ o.wo.p.first = (k4Slots P hp g F.next).nx + 1 ∧
      o.wo.sFv = (k4Slots P hp g F.next).nx + 1 + 1 + 2 * P.wsLay.lk + 1 ∧ Sized G ∧
      G.next = (k4Slots P hp g F.next).nx + 1 + 1 + 2 * P.wsLay.lk + 2 := by
  obtain ⟨_, _, _, _, H1, hd2, TS, claimsP, cE, G1, G2, G3, G4, G5, u1, u2, u3, u4, u5, hN, hT, hK,
    hG, _, _, _, _, _, hC, hM⟩ := hear_parts_first h hg
  have hK' : hearStack engFl P o.v o.H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2
      u2 = some (o.K, G3, u3) := by
    rw [if_pos hg]
    exact hK
  obtain ⟨hS4, n4⟩ := gated_next ρ hF hN hT hK' hG
  obtain ⟨e1, v, _, _, _, hR⟩ := claimsIn_spec hC
  have hS4' : Sized ({ G4 with next := G4.next + 1 } : Fork) := hS4
  obtain ⟨hSame, hS5, _, _⟩ := hideRun_ok _ G5 _ _ _ hS4' hR
  have n5 : G5.next = G4.next + 1 := hSame.next
  obtain ⟨m1, m2, m3, m4⟩ := flatForkEnd_slots hS5 hM
  exact ⟨by rw [e1, n4], by rw [m1, n5, n4], by rw [m2, n5, n4], m3, by rw [m4, n5, n4]⟩

include ρ in
/-- **The end of the hearing in a later group**, from a ledger with arrays of the right sizes: the
field for the embedding's slot holds 0; the merge's two slots, the ledger that is left. -/
theorem hear_end_later {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u))
    (hg : (g == 0) = false) :
    o.sVE = 0 ∧ o.wo.p.first = (k4Slots P hp g F.next).nx ∧
      o.wo.sFv = (k4Slots P hp g F.next).nx + 1 + 2 * P.wsLay.lk + 1 ∧ Sized G ∧
      G.next = (k4Slots P hp g F.next).nx + 1 + 2 * P.wsLay.lk + 2 := by
  obtain ⟨_, _, _, _, e0, H1, hd2, TS, claimsP, G1, G2, G3, G4, u1, u2, u3, u4, hN, hT, hK, hG, _,
    _, _, _, hM⟩ := hear_parts_later h hg
  have hK' : hearStack engFl P o.v o.H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2
      u2 = some (o.K, G3, u3) := by
    rw [if_neg fun e => Bool.false_ne_true (hg.symm.trans e)]
    exact hK
  obtain ⟨hS4, n4⟩ := gated_next ρ hF hN hT hK' hG
  obtain ⟨m1, m2, m3, m4⟩ := flatForkEnd_slots hS4 hM
  exact ⟨e0, by rw [m1, n4], by rw [m2, n4], m3, by rw [m4, n4]⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.gated_next
#print axioms OnBytes.Desc.First.K4.flatForkEnd_slots
#print axioms OnBytes.Desc.First.K4.hear_end_first
#print axioms OnBytes.Desc.First.K4.hear_end_later
