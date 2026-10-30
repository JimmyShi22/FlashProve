-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/HearSlots.lean: SLOT NUMBERS OF THE LAYERS' OWN ROUNDS AS FORMULAS: where the
hearing `hear` (OnBytes/Desc/First/K4/Hear.lean) returns over the plain engine, from a ledger whose
three arrays have the right sizes (`Sized`), eighteen slot-valued fields of its record, up to the
two gated product layers, are the ledger's next slot in front plus a formula in P, hp and g. Five
definitions, four statements and their proofs.

  `K4Slots`, `k4Slots P hp g n0` (with `tClAt`, `kPAt`, `hPAt`): the numbers, n0 the ledger's next
    slot in front: sW, the hidden sums; sS, the squares' sumcheck's own slots; sL, its two end
    values; sPv, the hidden products; sCl, their claimed sum; sP, their sumcheck's own slots; sEnd,
    its end values; tCl, tP, tEnd: the like of the terms' sumcheck; kP, the batched sumcheck's own
    slots; sA0, sH1, sB0, sV: its end values; hP, hL: the gated layer's own slots and end values;
    h2P, h2L: the routed gated layer's; nx: the ledger's next slot behind these.
  `pscRow_rec`: the making of a row turns the record's mark alone.
  `hearGated_parts`: the two gated layers' calls, as far as the ledgers go: the second starts from
    the ledger that the first has left. The points, the forms, the orders and the second call's
    tape stand under "there are", tied to nothing: enough for numbers of slots, for nothing else.
  `hear_slots`: fifteen slot-valued fields of the record are these numbers.
  `hear_slots_right`: three more: the slot of the right end value of each of the three product
    layers is the left one's plus 1.
    The numbers sS, kP, hP and h2P stand in no field of the record: of them nothing is said; they
    are names for sums in the formulas. nx stands in no field up to the gated layers.

Not here: the slot of the embedding's hidden value and the merge's slots
(Johnson/Road/K4/HearSlotsEnd.lean); the lookup's own slots, which the record copies in with fo; the
slot numbers inside forms (the rows, the start forms, KT, the batched sumcheck's end forms). That
the ledger's next slot in front is public is not said here. One direction: from a return. The
reading ρ is an idle letter (lemmas that are used are stated with one). It lies under Johnson/
since it imports NormsWorld.lean.
-/
import Johnson.Road.K4.NormsWorld
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.StackTape

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
open OnBytes.Desc.First.P1 (level_world tsc_world levelIn_heard tscIn_heard bind_some pure_some
  need_some onTape_some pscRow_spec)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The slots' numbers. -/
structure K4Slots where
  sW : Nat
  sS : Nat
  sL : Nat
  sPv : Nat
  sCl : Nat
  sP : Nat
  sEnd : Nat
  tCl : Nat
  tP : Nat
  tEnd : Nat
  kP : Nat
  sA0 : Nat
  sH1 : Nat
  sB0 : Nat
  sV : Nat
  hP : Nat
  hL : Nat
  h2P : Nat
  h2L : Nat
  nx : Nat

/-- The terms' claimed sum's slot. -/
def tClAt (P : Pub) (n0 : Nat) : Nat :=
  sClAt P n0 + 1 + 1 + 2 * P.y.h.lt + 2 + ledNO P.y.h.xl * P.y.NI

/-- The batched sumcheck's first own slot. -/
def kPAt (P : Pub) (n0 : Nat) : Nat := tClAt P n0 + 1 + 1 + 2 * P.y.h.lt + 1 + nEndT P.y

/-- The gated layer's first own slot. -/
def hPAt (P : Pub) (hp : HPlan2) (g n0 : Nat) : Nat :=
  kPAt P n0 + 1 + 2 * hp.lamS + 2 +
    (2 + (1 + P.y.LamM) + (hp.NCL - (if (g == 0) = true then 1 else 0)))

/-- The numbers, n0 the ledger's next slot in front. -/
def k4Slots (P : Pub) (hp : HPlan2) (g n0 : Nat) : K4Slots where
  sW := n0
  sS := n0 + ledNS P.y.h.xl * P.y.NI
  sL := n0 + ledNS P.y.h.xl * P.y.NI + 1 + 2 * P.rd.muV + 2
  sPv := sPvAt P n0
  sCl := sClAt P n0
  sP := sClAt P n0 + 1
  sEnd := sClAt P n0 + 1 + 1 + 2 * P.y.h.lt + 2
  tCl := tClAt P n0
  tP := tClAt P n0 + 1
  tEnd := tClAt P n0 + 1 + 1 + 2 * P.y.h.lt + 1
  kP := kPAt P n0
  sA0 := kPAt P n0 + 1 + 2 * hp.lamS + 2
  sH1 := kPAt P n0 + 1 + 2 * hp.lamS + 2 + 1
  sB0 := kPAt P n0 + 1 + 2 * hp.lamS + 2 + 1 + (1 + P.y.LamM)
  sV := kPAt P n0 + 1 + 2 * hp.lamS + 2 + 1 + (1 + P.y.LamM) + 1
  hP := hPAt P hp g n0
  hL := hPAt P hp g n0 + 1 + 2 * P.rd.muH + 2
  h2P := hPAt P hp g n0 + 1 + 2 * P.rd.muH + 2 + 2
  h2L := hPAt P hp g n0 + 1 + 2 * P.rd.muH + 2 + 2 + 1 + 2 * P.rd.muH2 + 2
  nx := hPAt P hp g n0 + 1 + 2 * P.rd.muH + 2 + 2 + 1 + 2 * P.rd.muH2 + 2 + 2

/-- The record behind the making of a row: the mark alone turns. -/
theorem pscRow_rec {p p' : Psc} {S0 : E} {kept f : Aff} {F G : Fork} {t u : Tape}
    (h : Fl.pscRow p S0 kept F t = some ((f, p'), G, u)) : p' = { p with rowMade := true } := by
  unfold Fl.pscRow at h
  obtain ⟨_, G1, u1, h1, k20⟩ := bind_some.mp h
  obtain ⟨_, rfl, rfl⟩ := P1.must_some.mp h1
  obtain ⟨_, G2, u2, h2, k21⟩ := bind_some.mp k20
  obtain ⟨_, rfl⟩ := P1.change_some.mp h2
  obtain ⟨he, _, _⟩ := pure_some.mp k21
  injection he with e1 e2
  exact e2.symm

/-- The two gated layers' calls, as far as the ledgers go: the second from the ledger that the first
has left. All other letters stand under "there are", tied to nothing. -/
theorem hearGated_parts {P : Pub} {H : Heard} {S : HeardStack} {F G : Fork} {t u : Tape}
    {hd hd2 : Level} (h : hearGated engFl P H S F t = some ((hd, hd2), G, u)) :
    ∃ (rho1 rho2 : Array E) (C1 C2 : Aff) (o1 o2 : List Nat) (Ga : Fork) (ua ub : Tape),
      Fl.levelIn P.rd.muH rho1 C1 o1 F t = some (hd, Ga, ua) ∧
      Fl.levelIn P.rd.muH2 rho2 C2 o2 Ga ub = some (hd2, G, u) := by
  unfold hearGated at h
  obtain ⟨x1, A1, a1, c1, k1⟩ := bind_some.mp h
  obtain ⟨x2, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨x3, A3, a3, c3, k3⟩ := bind_some.mp k2
  have c3' : Fl.point _ _ A1 a1 = some (x3, A3, a3) := c3
  obtain ⟨_, rfl⟩ := onTape_some.mp c3'
  obtain ⟨x4, A4, a4, c4, k4⟩ := bind_some.mp k3
  obtain ⟨e, rfl, rfl⟩ := pure_some.mp k4
  have e1 : x1 = hd := congrArg Prod.fst e
  have e2 : x4 = hd2 := congrArg Prod.snd e
  subst e1
  subst e2
  exact ⟨_, _, _, _, _, _, A1, a1, a3, c1, c4⟩

include ρ in
/-- **Fifteen slot-valued fields of the hearing's record**, where it returns over the plain engine
from a ledger with arrays of the right sizes. -/
theorem hear_slots {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.H.sW = (k4Slots P hp g F.next).sW ∧ o.H.wpl.sL = (k4Slots P hp g F.next).sL ∧
      o.H.sPv = (k4Slots P hp g F.next).sPv ∧ o.H.tV.sCl = (k4Slots P hp g F.next).sCl ∧
      o.H.tV.p.first = (k4Slots P hp g F.next).sP ∧
      o.H.tV.sEnd = (k4Slots P hp g F.next).sEnd ∧
      (∃ tT, o.H.tT = some tT ∧ tT.sCl = (k4Slots P hp g F.next).tCl ∧
        tT.p.first = (k4Slots P hp g F.next).tP ∧ tT.sEnd = (k4Slots P hp g F.next).tEnd) ∧
      o.K.sA0 = (k4Slots P hp g F.next).sA0 ∧ o.K.sH1 = (k4Slots P hp g F.next).sH1 ∧
      o.K.sB0 = (k4Slots P hp g F.next).sB0 ∧ o.K.sV = (k4Slots P hp g F.next).sV ∧
      o.hd.sL = (k4Slots P hp g F.next).hL ∧
      ∃ hd2, o.hd2 = some hd2 ∧ hd2.sL = (k4Slots P hp g F.next).h2L := by
  obtain ⟨_, H1, G1, u1, G2, u2, hN, hT, G3, u3, hK, hd2, G4, u4, hG, hd2e⟩ := hear_calls h
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
  have hTT : o.H.tT = some { tT with p := p' } := by rw [hH]
  refine ⟨a1, a2, a3, a4, a5, a6, ⟨_, hTT, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, hd2, hd2e, ?_⟩
  · show tT.sCl = tClAt P F.next
    rw [tCl, m1]
  · show p'.first = tClAt P F.next + 1
    rw [hp']
    show tT.p.first = _
    rw [tP, m1]
  · show tT.sEnd = tClAt P F.next + 1 + 1 + 2 * P.y.h.lt + 1
    rw [tEnd, hlenT, m1]
  · show o.K.sA0 = kPAt P F.next + 1 + 2 * hp.lamS + 2
    rw [hsA0, m2]
  · show o.K.sH1 = kPAt P F.next + 1 + 2 * hp.lamS + 2 + 1
    rw [hsH1, hsA0, m2]
  · show o.K.sB0 = kPAt P F.next + 1 + 2 * hp.lamS + 2 + 1 + (1 + P.y.LamM)
    rw [hsB0, hsH1, hsA0, m2]
  · show o.K.sV = kPAt P F.next + 1 + 2 * hp.lamS + 2 + 1 + (1 + P.y.LamM) + 1
    rw [hsV, hsB0, hsH1, hsA0, m2]
  · show o.hd.sL = hPAt P hp g F.next + 1 + 2 * P.rd.muH + 2
    rw [hLA, m3]
  · show hd2.sL = hPAt P hp g F.next + 1 + 2 * P.rd.muH + 2 + 2 + 1 + 2 * P.rd.muH2 + 2
    rw [hLB, nA, m3]

include ρ in
/-- **Three more**, under the same premises: the right end values' slots of the three product
layers. -/
theorem hear_slots_right {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (hF : Sized F) (h : hear engFl P hp g fo F t = some (o, G, u)) :
    o.H.wpl.sR = (k4Slots P hp g F.next).sL + 1 ∧ o.hd.sR = (k4Slots P hp g F.next).hL + 1 ∧
      ∃ hd2, o.hd2 = some hd2 ∧ hd2.sR = (k4Slots P hp g F.next).h2L + 1 := by
  obtain ⟨_, a2, _, _, _, _, _, _, _, _, _, a12, hd2, e2, a13⟩ := hear_slots ρ hF h
  obtain ⟨_, H1, G1, u1, G2, u2, hN, hT, G3, u3, hK, hd2', G4, u4, hG, hd2e⟩ := hear_calls h
  have e : hd2 = hd2' := Option.some.inj (e2.symm.trans hd2e)
  subst e
  obtain ⟨tT, G1', u1', row, p', cT, _, cR, hH⟩ := hearTerms_calls hT
  obtain ⟨F7, F8, _, _, c7, _⟩ := norms_chain ρ hF hN hH
  obtain ⟨_, _, _, _, _, _, Ga, ua, ub, cA, cB⟩ := hearGated_parts hG
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, r7, _⟩ := levelIn_heard c7
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rA, _⟩ := levelIn_heard cA
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rB, _⟩ := levelIn_heard cB
  exact ⟨by rw [r7, a2], by rw [rA, a12], hd2, e2, by rw [rB, a13]⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hear_slots
#print axioms OnBytes.Desc.First.K4.hear_slots_right
