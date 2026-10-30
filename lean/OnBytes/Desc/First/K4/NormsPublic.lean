-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Desc/First/K4/NormsPublic.lean: what a return of the first stretch of the layers' own rounds
says of the lookup's points.

`hearNorms` (OnBytes/Desc/First/K4/Hear.lean) tests, before it hears anything of its own, that the
last la coordinates of every call's point are the last la of the lookup's point, and takes the last
lt of these as the lookup's token point. The library's record of public hypotheses
(Johnson/Road/Rows/LayerEnds34.lean, Pub34: hZ, hm, ha, hzt) takes these four lines as hypotheses.
Here they are concluded from a return of K4's own text over the plain engine.
OnBytes/Desc/First/K4/NormsCalls.lean takes the same text apart into its calls; this file keeps
what that one leaves out.

  `hearNorms_public`: if `hearNorms engFl P g fo F t` returns H: la is at most the lookup's depth;
      the last la coordinates Z of fo.zx are there; so are those of every call's point, and each is
      Z; H.ztF is the last lt coordinates of fo.zx; H.fo is fo.

Limits. One direction: from a return. An identity on data: no draw, no soundness.
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

theorem hearNorms_public {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard} (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    ∃ (Z : Array E) (ends : Array (Array E)),
      P.y.h.la ≤ fo.shape.dT ∧ (lastOf fo.zx P.y.h.la).toOption = some Z ∧
      (fo.zk.mapM fun zk => (lastOf zk P.y.h.la).toOption) = some ends ∧
      ends.all (· == Z) = true ∧ (lastOf fo.zx P.y.h.lt).toOption = some H.ztF ∧ H.fo = fo := by
  unfold hearNorms at h
  obtain ⟨PV, F1, t1, h1, k1⟩ := bind_some.mp h
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true] at k1
    obtain ⟨ZE, F2, t2, h2, k2⟩ := bind_some.mp k1
    obtain ⟨tkh, F3, t3, h3, k3⟩ := bind_some.mp k2
    obtain ⟨_, A1, a1, c1, k4⟩ := bind_some.mp k3
    obtain ⟨q1, rfl, rfl⟩ := must_some.mp c1
    obtain ⟨Z, A2, a2, c2, k5⟩ := bind_some.mp k4
    obtain ⟨q2, rfl, rfl⟩ := need_some.mp c2
    obtain ⟨ends, A3, a3, c3, k6⟩ := bind_some.mp k5
    obtain ⟨q3, rfl, rfl⟩ := need_some.mp c3
    obtain ⟨_, A4, a4, c4, k7⟩ := bind_some.mp k6
    obtain ⟨q4, rfl, rfl⟩ := must_some.mp c4
    obtain ⟨ztF, A5, a5, c5, k8⟩ := bind_some.mp k7
    obtain ⟨q5, rfl, rfl⟩ := need_some.mp c5
    obtain ⟨sW, F4, t4, h4, k9⟩ := bind_some.mp k8
    obtain ⟨gp, F5, t5, h5, k10⟩ := bind_some.mp k9
    obtain ⟨rhoI, F6, t6, h6, k11⟩ := bind_some.mp k10
    obtain ⟨wpl, F7, t7, h7, k12⟩ := bind_some.mp k11
    obtain ⟨sPv, F8, t8, h8, k13⟩ := bind_some.mp k12
    obtain ⟨omV, F9, t9, h9, k14⟩ := bind_some.mp k13
    obtain ⟨tV, F10, t10, h10, k15⟩ := bind_some.mp k14
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k15
    exact ⟨Z, ends, by simpa using q1, q2, q3, q4, q5, rfl⟩
  · have hg' : (g == 0) = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, if_false] at k1
    obtain ⟨ZE, F2, t2, h2, k2⟩ := bind_some.mp k1
    obtain ⟨tkh, F3, t3, h3, k3⟩ := bind_some.mp k2
    obtain ⟨_, A1, a1, c1, k4⟩ := bind_some.mp k3
    obtain ⟨q1, rfl, rfl⟩ := must_some.mp c1
    obtain ⟨Z, A2, a2, c2, k5⟩ := bind_some.mp k4
    obtain ⟨q2, rfl, rfl⟩ := need_some.mp c2
    obtain ⟨ends, A3, a3, c3, k6⟩ := bind_some.mp k5
    obtain ⟨q3, rfl, rfl⟩ := need_some.mp c3
    obtain ⟨_, A4, a4, c4, k7⟩ := bind_some.mp k6
    obtain ⟨q4, rfl, rfl⟩ := must_some.mp c4
    obtain ⟨ztF, A5, a5, c5, k8⟩ := bind_some.mp k7
    obtain ⟨q5, rfl, rfl⟩ := need_some.mp c5
    obtain ⟨sW, F4, t4, h4, k9⟩ := bind_some.mp k8
    obtain ⟨gp, F5, t5, h5, k10⟩ := bind_some.mp k9
    obtain ⟨rhoI, F6, t6, h6, k11⟩ := bind_some.mp k10
    obtain ⟨wpl, F7, t7, h7, k12⟩ := bind_some.mp k11
    obtain ⟨sPv, F8, t8, h8, k13⟩ := bind_some.mp k12
    obtain ⟨omV, F9, t9, h9, k14⟩ := bind_some.mp k13
    obtain ⟨tV, F10, t10, h10, k15⟩ := bind_some.mp k14
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k15
    exact ⟨Z, ends, by simpa using q1, q2, q3, q4, q5, rfl⟩

#print axioms hearNorms_public

end OnBytes.Desc.First.K4
