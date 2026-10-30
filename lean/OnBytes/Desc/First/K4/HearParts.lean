-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/HearParts.lean: THE HEARING OF THE LAYERS' OWN ROUNDS, `hear`
(OnBytes/Desc/First/K4/Hear.lean), over the plain engine `engFl`, WHERE IT RETURNS: ITS CALLS THAT
HEAR, AS ONE CHAIN OF LEDGERS AND TAPES from what it was handed to what it leaves. A definition and
two statements with their proofs.

Why. `hear_calls` (HearCalls.lean) names the calls up to the two gated layers; the merge's call was
named apart; each said "there is a ledger" of its own, so nothing said that the ledger which the
gated layers leave is the one that the merge is handed.

  `envOf`: the environment of claims that the text makes of what it has heard.
  `hear_parts_first` (the first group), `hear_parts_later` (a later group): the text covers the
    public record; three fields of the environment that the text makes (y, sc, g); then, each from
    the ledger and the tape that the one in front has left: the norms' stretch, the terms'
    sumcheck, the batched sumcheck, the two gated layers; the weight claims (public steps, which
    leave ledger and tape as they are) and that they are as many as the plan says; in the first
    group the embedding's claim and its hidden value; the merge, which leaves what the hearing
    leaves. In a later group the field for the embedding's slot holds 0.

Not here: the text's other public steps, which leave ledger and tape as they are: that the lookup's
numbers are the layout's, the number of the reads' array, that the functions are open, the tables'
layout and its length, the points and the functions at the end; so the fields iU3, K3, tab, zk of
the environment and the record's funs go unsaid. `hear_public` (HearPublic.lean) says these. The
proofs walk the text line for line. One direction: from a return. What the parts mean is not said.

-/
import OnBytes.Desc.First.K4.Plain
import OnBytes.Desc.First.P1.FlSpec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
open OnBytes.Desc.First.P1 (bind_some pure_some must_some need_some)

/-- The environment of claims that the text makes of what it has heard. -/
def envOf (P : Pub) (o : Own) : ClaimEnv :=
  { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := (o.H.tT.map (·.r)).getD #[] }

/-- **The hearing's chain of calls, in the first group**, where it returns. -/
theorem hear_parts_first {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u))
    (hg : (g == 0) = true) :
    covers P = true ∧ o.v.y = P.y ∧ o.v.sc = P.sc ∧ o.v.g = g ∧
      ∃ (H1 : Heard) (hd2 : Level) (TS : List Nat) (claimsP : List WsClaim) (cE : WsClaim)
        (G1 G2 G3 G4 G5 : Fork) (u1 u2 u3 u4 u5 : Tape),
        hearNorms engFl P g fo F t = some (H1, G1, u1) ∧
        hearTerms engFl P H1 G1 u1 = some (o.H, G2, u2) ∧
        hearStack engFl P o.v o.H hp.lamS (hp.NCL - 1) G2 u2 = some (o.K, G3, u3) ∧
        hearGated engFl P o.H o.K G3 u3 = some ((o.hd, hd2), G4, u4) ∧ o.hd2 = some hd2 ∧
        callsTS P = some TS ∧ (envOf P o).weightClaims TS = some claimsP ∧
        (envOf P o).claimE o.H.ZE o.H.tkh P.V P.tokv = some cE ∧
        (claimsP ++ [cE]).toArray.size = hp.NCL ∧
        Fl.claimsIn 1 G4 u4 = some (o.sVE, G5, u5) ∧
        flatForkEnd P.wsLay (claimsP ++ [cE]).toArray
          ((Array.range (hp.NCL - 1)).map (o.K.sV + ·) ++ #[o.sVE]) G5 u5 = some (o.wo, G, u) := by
  unfold hear at h
  simp only [hg, if_true] at h
  obtain ⟨_, A1, a1, c1, k1⟩ := bind_some.mp h
  obtain ⟨hcov, rfl, rfl⟩ := must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c2
  obtain ⟨iU3, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c3
  obtain ⟨H1, G1, u1, h1, k4⟩ := bind_some.mp k3
  obtain ⟨H, G2, u2, h2, k5⟩ := bind_some.mp k4
  obtain ⟨_, A4, a4, c4, k6⟩ := bind_some.mp k5
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c4
  obtain ⟨x, A5, a5, c5, k7⟩ := bind_some.mp k6
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c5
  obtain ⟨tab, laid, nU3⟩ := x
  obtain ⟨_, A6, a6, c6, k8⟩ := bind_some.mp k7
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c6
  obtain ⟨K, G3, u3, h3, k9⟩ := bind_some.mp k8
  obtain ⟨x2, G4, u4, h4, k10⟩ := bind_some.mp k9
  obtain ⟨hd, hd2⟩ := x2
  obtain ⟨TS, A7, a7, c7, k11⟩ := bind_some.mp k10
  obtain ⟨e7, rfl, rfl⟩ := need_some.mp c7
  obtain ⟨claimsP, A8, a8, c8, k12⟩ := bind_some.mp k11
  obtain ⟨e8, rfl, rfl⟩ := need_some.mp c8
  obtain ⟨claimsE, A9, a9, c9, k13⟩ := bind_some.mp k12
  obtain ⟨e9, rfl, rfl⟩ := need_some.mp c9
  obtain ⟨cE, hcE, rfl⟩ := Option.map_eq_some_iff.mp e9
  obtain ⟨_, B1, b1, d1, k14⟩ := bind_some.mp k13
  obtain ⟨e10, rfl, rfl⟩ := must_some.mp d1
  obtain ⟨sVE, B2, b2, d2, k15⟩ := bind_some.mp k14
  obtain ⟨wo, B3, b3, d3, k16⟩ := bind_some.mp k15
  obtain ⟨pts, B4, b4, d4, k17⟩ := bind_some.mp k16
  obtain ⟨_, rfl, rfl⟩ := need_some.mp d4
  obtain ⟨funs, B5, b5, d5, k18⟩ := bind_some.mp k17
  obtain ⟨_, rfl, rfl⟩ := need_some.mp d5
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k18
  exact ⟨by simpa using hcov, rfl, rfl, rfl, H1, hd2, TS, claimsP, cE, G1, G2, G3, G4, _, u1, u2,
    u3, u4, _, h1, h2, h3, h4, rfl, e7, e8, hcE, beq_iff_eq.mp e10, d2, d3⟩

/-- **The hearing's chain of calls, in a later group**, where it returns. -/
theorem hear_parts_later {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u))
    (hg : (g == 0) = false) :
    covers P = true ∧ o.v.y = P.y ∧ o.v.sc = P.sc ∧ o.v.g = g ∧ o.sVE = 0 ∧
      ∃ (H1 : Heard) (hd2 : Level) (TS : List Nat) (claimsP : List WsClaim)
        (G1 G2 G3 G4 : Fork) (u1 u2 u3 u4 : Tape),
        hearNorms engFl P g fo F t = some (H1, G1, u1) ∧
        hearTerms engFl P H1 G1 u1 = some (o.H, G2, u2) ∧
        hearStack engFl P o.v o.H hp.lamS (hp.NCL - 0) G2 u2 = some (o.K, G3, u3) ∧
        hearGated engFl P o.H o.K G3 u3 = some ((o.hd, hd2), G4, u4) ∧ o.hd2 = some hd2 ∧
        callsTS P = some TS ∧ (envOf P o).weightClaims TS = some claimsP ∧
        (claimsP ++ []).toArray.size = hp.NCL ∧
        flatForkEnd P.wsLay (claimsP ++ []).toArray
          ((Array.range (hp.NCL - 0)).map (o.K.sV + ·) ++ #[]) G4 u4 = some (o.wo, G, u) := by
  unfold hear at h
  simp only [hg, Bool.false_eq_true, if_false] at h
  obtain ⟨_, A1, a1, c1, k1⟩ := bind_some.mp h
  obtain ⟨hcov, rfl, rfl⟩ := must_some.mp c1
  obtain ⟨_, A2, a2, c2, k2⟩ := bind_some.mp k1
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c2
  obtain ⟨iU3, A3, a3, c3, k3⟩ := bind_some.mp k2
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c3
  obtain ⟨H1, G1, u1, h1, k4⟩ := bind_some.mp k3
  obtain ⟨H, G2, u2, h2, k5⟩ := bind_some.mp k4
  obtain ⟨_, A4, a4, c4, k6⟩ := bind_some.mp k5
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c4
  obtain ⟨x, A5, a5, c5, k7⟩ := bind_some.mp k6
  obtain ⟨_, rfl, rfl⟩ := need_some.mp c5
  obtain ⟨tab, laid, nU3⟩ := x
  obtain ⟨_, A6, a6, c6, k8⟩ := bind_some.mp k7
  obtain ⟨_, rfl, rfl⟩ := must_some.mp c6
  obtain ⟨K, G3, u3, h3, k9⟩ := bind_some.mp k8
  obtain ⟨x2, G4, u4, h4, k10⟩ := bind_some.mp k9
  obtain ⟨hd, hd2⟩ := x2
  obtain ⟨TS, A7, a7, c7, k11⟩ := bind_some.mp k10
  obtain ⟨e7, rfl, rfl⟩ := need_some.mp c7
  obtain ⟨claimsP, A8, a8, c8, k12⟩ := bind_some.mp k11
  obtain ⟨e8, rfl, rfl⟩ := need_some.mp c8
  obtain ⟨claimsE, A9, a9, c9, k13⟩ := bind_some.mp k12
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp c9
  obtain ⟨_, B1, b1, d1, k14⟩ := bind_some.mp k13
  obtain ⟨e10, rfl, rfl⟩ := must_some.mp d1
  obtain ⟨sVE, B2, b2, d2, k15⟩ := bind_some.mp k14
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp d2
  obtain ⟨wo, B3, b3, d3, k16⟩ := bind_some.mp k15
  obtain ⟨pts, B4, b4, d4, k17⟩ := bind_some.mp k16
  obtain ⟨_, rfl, rfl⟩ := need_some.mp d4
  obtain ⟨funs, B5, b5, d5, k18⟩ := bind_some.mp k17
  obtain ⟨_, rfl, rfl⟩ := need_some.mp d5
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k18
  exact ⟨by simpa using hcov, rfl, rfl, rfl, rfl, H1, hd2, TS, claimsP, G1, G2, G3, G4, u1, u2, u3,
    u4, h1, h2, h3, h4, rfl, e7, e8, beq_iff_eq.mp e10, d3⟩

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hear_parts_first
#print axioms OnBytes.Desc.First.K4.hear_parts_later
