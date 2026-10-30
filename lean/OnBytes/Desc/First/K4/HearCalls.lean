-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/HearCalls.lean: the layers' own rounds, `hear`
(OnBytes/Desc/First/K4/Hear.lean), over the plain engine `engFl` (K4/Plain.lean), TAKEN APART INTO
ITS STRETCHES WHERE IT RETURNS; and the second stretch, `hearTerms`, into its calls. Statements and
proofs.

  `hear_calls`: if `hear engFl P hp g fo F t` returns (o, G, u), then `covers P` holds and, one
    behind the other, each on its own ledger and tape: `hearNorms` returned some H1; `hearTerms`
    returned o.H at H1; `hearStack` returned o.K at o.v and o.H; `hearGated` returned (o.hd, hd2)
    with o.hd2 = some hd2. (What follows, the merge of the weight claims, is not taken apart here.)
  `hearTerms_calls`: if `hearTerms engFl P H F t` returns (H', G, u): `Fl.tscIn` returned tT at
    H.ztF with degreeInY = 1; tT's eps is not the zero word; `Fl.pscRow` made the row WITHOUT a
    summand; H' is H with tT (its record behind the row) and KT := the row scaled by -(1 / eps).
  `hearTerms_keeps`: so H' has H's fields of the first stretch.

One direction: from a return. Nothing is said of what the calls mean.
-/
import OnBytes.Desc.First.K4.NormsCalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
open OnBytes.Desc.First.P1 (bind_some pure_some must_some need_some)

/-- **Where the second stretch returns.** -/
theorem hearTerms_calls {P : Pub} {H H' : Heard} {F G : Fork} {t u : Tape}
    (h : hearTerms engFl P H F t = some (H', G, u)) :
    ∃ (tT : Tsc) (G1 : Fork) (u1 : Tape) (row : Aff) (p' : Psc),
      Fl.tscIn H.ztF P.y.h.lt (nEndT P.y) 1 F t = some (tT, G1, u1) ∧
      isZeroE tT.p.eps = false ∧
      Fl.pscRow tT.p zeroE {} G1 u1 = some ((row, p'), G, u) ∧
      H' = { H with tT := some { tT with p := p' },
                    KT := row.scale (negE (invE tT.p.eps)) } := by
  unfold hearTerms at h
  obtain ⟨tT, G1, u1, h1, k1⟩ := bind_some.mp h
  obtain ⟨_, A1, a1, c1, k2⟩ := bind_some.mp k1
  obtain ⟨hz, rfl, rfl⟩ := must_some.mp c1
  obtain ⟨x, G2, u2, h2, k3⟩ := bind_some.mp k2
  obtain ⟨row, p'⟩ := x
  obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k3
  exact ⟨tT, G1, u1, row, p', h1, by simpa using hz, h2, rfl⟩

/-- The second stretch keeps what the first has heard. -/
theorem hearTerms_keeps {P : Pub} {H H' : Heard} {F G : Fork} {t u : Tape}
    (h : hearTerms engFl P H F t = some (H', G, u)) :
    H'.fo = H.fo ∧ H'.PV = H.PV ∧ H'.ZE = H.ZE ∧ H'.tkh = H.tkh ∧ H'.ztF = H.ztF ∧ H'.sW = H.sW ∧
      H'.gp = H.gp ∧ H'.wpl = H.wpl ∧ H'.sPv = H.sPv ∧ H'.omV = H.omV ∧ H'.tV = H.tV := by
  obtain ⟨tT, G1, u1, row, p', _, _, _, rfl⟩ := hearTerms_calls h
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Where the layers' own rounds return: the stretches.** -/
theorem hear_calls {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) :
    covers P = true ∧ ∃ (H1 : Heard) (G1 : Fork) (u1 : Tape) (G2 : Fork) (u2 : Tape),
      hearNorms engFl P g fo F t = some (H1, G1, u1) ∧
      hearTerms engFl P H1 G1 u1 = some (o.H, G2, u2) ∧
      ∃ (G3 : Fork) (u3 : Tape),
        hearStack engFl P o.v o.H hp.lamS (hp.NCL - (if (g == 0) = true then 1 else 0)) G2 u2 =
          some (o.K, G3, u3) ∧
        ∃ (hd2 : Level) (G4 : Fork) (u4 : Tape),
          hearGated engFl P o.H o.K G3 u3 = some ((o.hd, hd2), G4, u4) ∧ o.hd2 = some hd2 := by
  unfold hear at h
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true] at h ⊢
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
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c7
    obtain ⟨claimsP, A8, a8, c8, k12⟩ := bind_some.mp k11
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c8
    obtain ⟨claimsE, A9, a9, c9, k13⟩ := bind_some.mp k12
    obtain ⟨_, B1, b1, d1, k14⟩ := bind_some.mp k13
    obtain ⟨sVE, B2, b2, d2, k15⟩ := bind_some.mp k14
    obtain ⟨wo, B3, b3, d3, k16⟩ := bind_some.mp k15
    obtain ⟨pts, B4, b4, d4, k17⟩ := bind_some.mp k16
    obtain ⟨funs, B5, b5, d5, k18⟩ := bind_some.mp k17
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k18
    exact ⟨by simpa using hcov, H1, G1, u1, G2, u2, h1, h2, G3, u3, h3, hd2, G4, u4, h4, rfl⟩
  · have hg' : (g == 0) = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, if_false] at h ⊢
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
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c7
    obtain ⟨claimsP, A8, a8, c8, k12⟩ := bind_some.mp k11
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c8
    obtain ⟨claimsE, A9, a9, c9, k13⟩ := bind_some.mp k12
    obtain ⟨_, B1, b1, d1, k14⟩ := bind_some.mp k13
    obtain ⟨sVE, B2, b2, d2, k15⟩ := bind_some.mp k14
    obtain ⟨wo, B3, b3, d3, k16⟩ := bind_some.mp k15
    obtain ⟨pts, B4, b4, d4, k17⟩ := bind_some.mp k16
    obtain ⟨funs, B5, b5, d5, k18⟩ := bind_some.mp k17
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k18
    exact ⟨by simpa using hcov, H1, G1, u1, G2, u2, h1, h2, G3, u3, h3, hd2, G4, u4, h4, rfl⟩

end OnBytes.Desc.First.K4
