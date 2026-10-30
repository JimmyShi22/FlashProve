-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/HearPublic.lean: what a return of the layers' own rounds says of the PUBLIC
values that the text fetches on its way.

`hear` (OnBytes/Desc/First/K4/Hear.lean) fetches, between its stretches of rounds, values that hang
on public numbers and on what was heard alone: the number of the array of reads, the places of the
tables, the calls with terms, the panels' weight claims, the points by name, the list of all tables.
The library's theorems on what K4's forms are worth (Johnson/Road/) take each of these as a
hypothesis "the function returns this value". Here they are concluded from a return of K4's own text
over the plain engine.

  `hear_public`: if `hear engFl P hp g fo F t` returns o: the two guards hold; the environment o.v
      is the record that the text writes (the plan's layout and scales, the group, the array of
      reads and its columns, the tables' places, the lookup's points); `layTables`, `callsTS`,
      `weightClaims`, `pointsOf`, `funsOf` return, the last one o.funs.

Limits. One direction: from a return. An identity on data: nothing on what anything is worth, on a
draw, on soundness. Beside OnBytes/Desc/First/K4/HearCalls.lean, which takes the same text apart
into its stretches of rounds.
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

theorem hear_public {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    covers P = true ∧ shapeFits P fo = true ∧
    ∃ (iU3 : Nat) (tab : List TableAt) (laid : List (TableAsk × List (Nat × Nat))) (nU3 : Nat)
      (TS : List Nat) (claimsP : List WsClaim) (pts : List (String × Array E)) (hd2 : Level),
      hp.tl.ix.U.getD 2 none = some iU3 ∧ hp.tl.funOpen = true ∧
      layTables ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) (tableAsks P.y P.rd g) 0 =
        some (tab, laid, nU3) ∧
      (nU3 == hp.nU.getD 2 0) = true ∧
      o.v = { y := P.y, sc := P.sc, g := g, iU3 := iU3,
              K3 := ((hp.Fp.trees[iU3]?).map (·.K)).getD 0, tab := tab, zk := fo.zk } ∧
      callsTS P = some TS ∧
      ({ v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs,
         rt := (o.H.tT.map (·.r)).getD #[] } : ClaimEnv).weightClaims TS = some claimsP ∧
      o.hd2 = some hd2 ∧ pointsOf P.y o.H o.hd (some hd2) = some pts ∧
      funsOf P.y fo pts laid = some o.funs := by
  unfold hear at h
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true] at h ⊢
    obtain ⟨_, A1, a1, c1, k1⟩ := bind_some.mp h
    obtain ⟨hcov, rfl, rfl⟩ := must_some.mp c1
    obtain ⟨_, A2, a2, c2, k2⟩ := bind_some.mp k1
    obtain ⟨hfit, rfl, rfl⟩ := must_some.mp c2
    obtain ⟨iU3, A3, a3, c3, k3⟩ := bind_some.mp k2
    obtain ⟨e3, rfl, rfl⟩ := need_some.mp c3
    obtain ⟨H1, G1, u1, h1, k4⟩ := bind_some.mp k3
    obtain ⟨H, G2, u2, h2, k5⟩ := bind_some.mp k4
    obtain ⟨_, A4, a4, c4, k6⟩ := bind_some.mp k5
    obtain ⟨e4, rfl, rfl⟩ := must_some.mp c4
    obtain ⟨x, A5, a5, c5, k7⟩ := bind_some.mp k6
    obtain ⟨e5, rfl, rfl⟩ := need_some.mp c5
    obtain ⟨tab, laid, nU3⟩ := x
    obtain ⟨_, A6, a6, c6, k8⟩ := bind_some.mp k7
    obtain ⟨e6, rfl, rfl⟩ := must_some.mp c6
    obtain ⟨K, G3, u3, h3, k9⟩ := bind_some.mp k8
    obtain ⟨x2, G4, u4, h4, k10⟩ := bind_some.mp k9
    obtain ⟨hd, hd2⟩ := x2
    obtain ⟨TS, A7, a7, c7, k11⟩ := bind_some.mp k10
    obtain ⟨e7, rfl, rfl⟩ := need_some.mp c7
    obtain ⟨claimsP, A8, a8, c8, k12⟩ := bind_some.mp k11
    obtain ⟨e8, rfl, rfl⟩ := need_some.mp c8
    obtain ⟨claimsE, A9, a9, c9, k13⟩ := bind_some.mp k12
    obtain ⟨_, B1, b1, d1, k14⟩ := bind_some.mp k13
    obtain ⟨sVE, B2, b2, d2, k15⟩ := bind_some.mp k14
    obtain ⟨wo, B3, b3, d3, k16⟩ := bind_some.mp k15
    obtain ⟨pts, B4, b4, d4, k17⟩ := bind_some.mp k16
    obtain ⟨e9, rfl, rfl⟩ := need_some.mp d4
    obtain ⟨funs, B5, b5, d5, k18⟩ := bind_some.mp k17
    obtain ⟨e10, rfl, rfl⟩ := need_some.mp d5
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k18
    exact ⟨by simpa using hcov, by simpa using hfit, iU3, tab, laid, nU3, TS, claimsP, pts, hd2,
      e3, e4, e5, e6, rfl, e7, e8, rfl, e9, e10⟩
  · have hg' : (g == 0) = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, if_false] at h ⊢
    obtain ⟨_, A1, a1, c1, k1⟩ := bind_some.mp h
    obtain ⟨hcov, rfl, rfl⟩ := must_some.mp c1
    obtain ⟨_, A2, a2, c2, k2⟩ := bind_some.mp k1
    obtain ⟨hfit, rfl, rfl⟩ := must_some.mp c2
    obtain ⟨iU3, A3, a3, c3, k3⟩ := bind_some.mp k2
    obtain ⟨e3, rfl, rfl⟩ := need_some.mp c3
    obtain ⟨H1, G1, u1, h1, k4⟩ := bind_some.mp k3
    obtain ⟨H, G2, u2, h2, k5⟩ := bind_some.mp k4
    obtain ⟨_, A4, a4, c4, k6⟩ := bind_some.mp k5
    obtain ⟨e4, rfl, rfl⟩ := must_some.mp c4
    obtain ⟨x, A5, a5, c5, k7⟩ := bind_some.mp k6
    obtain ⟨e5, rfl, rfl⟩ := need_some.mp c5
    obtain ⟨tab, laid, nU3⟩ := x
    obtain ⟨_, A6, a6, c6, k8⟩ := bind_some.mp k7
    obtain ⟨e6, rfl, rfl⟩ := must_some.mp c6
    obtain ⟨K, G3, u3, h3, k9⟩ := bind_some.mp k8
    obtain ⟨x2, G4, u4, h4, k10⟩ := bind_some.mp k9
    obtain ⟨hd, hd2⟩ := x2
    obtain ⟨TS, A7, a7, c7, k11⟩ := bind_some.mp k10
    obtain ⟨e7, rfl, rfl⟩ := need_some.mp c7
    obtain ⟨claimsP, A8, a8, c8, k12⟩ := bind_some.mp k11
    obtain ⟨e8, rfl, rfl⟩ := need_some.mp c8
    obtain ⟨claimsE, A9, a9, c9, k13⟩ := bind_some.mp k12
    obtain ⟨_, B1, b1, d1, k14⟩ := bind_some.mp k13
    obtain ⟨sVE, B2, b2, d2, k15⟩ := bind_some.mp k14
    obtain ⟨wo, B3, b3, d3, k16⟩ := bind_some.mp k15
    obtain ⟨pts, B4, b4, d4, k17⟩ := bind_some.mp k16
    obtain ⟨e9, rfl, rfl⟩ := need_some.mp d4
    obtain ⟨funs, B5, b5, d5, k18⟩ := bind_some.mp k17
    obtain ⟨e10, rfl, rfl⟩ := need_some.mp d5
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k18
    exact ⟨by simpa using hcov, by simpa using hfit, iU3, tab, laid, nU3, TS, claimsP, pts, hd2,
      e3, e4, e5, e6, rfl, e7, e8, rfl, e9, e10⟩

#print axioms hear_public

end OnBytes.Desc.First.K4
