-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/NormsCalls.lean: the first stretch of the layers' own rounds, `hearNorms`
(OnBytes/Desc/First/K4/Hear.lean), over the plain engine `engFl` (K4/Plain.lean), TAKEN APART WHERE
IT RETURNS: which calls it has made, in which order, on which ledgers and tapes, and what it hands
back. Statement and proof.

  `hearNorms_calls`: if `hearNorms engFl P g fo F t` returns (H, G, u), then, one behind the other:
    the norms' point PV was drawn; (in the first group) two points more; the sums of each norm (nine
    at five limbs) were received under slots from sW on; gp are the powers of a drawn element; the
    point rhoI was drawn; `Fl.levelIn` returned H.wpl at the start form and the point that the
    `normsStart` makes of these; the products of each norm (seven at five limbs) were
    received from sPv on; omV are the powers of a drawn element; `Fl.tscIn` returned H.tV at PV.
    Each call stands as an equation on its own ledger and tape, so that the laws of the calls can be
    laid on them one by one. It also gives H.ztF (the last lt coordinates of the lookup's point) and
    H.fo = fo. The stretch's two tests (the depth; that the calls' points end alike) are not retold.

One direction: from a return. Nothing is said of what the calls mean.
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

/-- **Where the norms' stretch returns.** -/
theorem hearNorms_calls {P : Pub} {g : Nat} {fo : Forest.Heard} {F G : Fork} {t u : Tape}
    {H : Heard} (h : hearNorms engFl P g fo F t = some (H, G, u)) :
    ∃ (F1 F2 F3 F4 F5 F6 F7 F8 F9 : Fork) (t1 t2 t3 t4 t5 t6 t7 t8 t9 : Tape),
      engFl.point .zero P.y.h.lt F t = some (H.PV, F1, t1) ∧
      (if g == 0 then engFl.point .zero (P.y.ls + P.y.h.lt) else pure #[]) F1 t1 =
        some (H.ZE, F2, t2) ∧
      (if g == 0 then engFl.point .zero (P.y.lPd - P.y.ls) else pure #[]) F2 t2 =
        some (H.tkh, F3, t3) ∧
      (lastOf fo.zx P.y.h.lt).toOption = some H.ztF ∧
      Fl.claimsIn (ledNS P.y.h.xl * P.y.NI) F3 t3 = some (H.sW, F4, t4) ∧
      Fl.batch (ledNS P.y.h.xl) F4 t4 = some (H.gp, F5, t5) ∧
      ∃ rhoI : Array E, engFl.point .join P.rd.lNI F5 t5 = some (rhoI, F6, t6) ∧
      Fl.levelIn P.rd.muV (normsStart P.y H.sW H.gp rhoI H.PV).2
          (normsStart P.y H.sW H.gp rhoI H.PV).1 (orderDefault P.rd.muV) F6 t6 =
        some (H.wpl, F7, t7) ∧
      Fl.claimsIn (ledNP P.y.h.xl * P.y.NI) F7 t7 = some (H.sPv, F8, t8) ∧
      Fl.batch (ledNP P.y.h.xl * P.y.NI) F8 t8 = some (H.omV, F9, t9) ∧
      Fl.tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F9 t9 = some (H.tV, G, u) ∧
      H.fo = fo := by
  unfold hearNorms at h
  obtain ⟨PV, F1, t1, h1, k1⟩ := bind_some.mp h
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true] at k1 ⊢
    obtain ⟨ZE, F2, t2, h2, k2⟩ := bind_some.mp k1
    obtain ⟨tkh, F3, t3, h3, k3⟩ := bind_some.mp k2
    obtain ⟨_, A1, a1, c1, k4⟩ := bind_some.mp k3
    obtain ⟨_, rfl, rfl⟩ := must_some.mp c1
    obtain ⟨Z, A2, a2, c2, k5⟩ := bind_some.mp k4
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c2
    obtain ⟨ends, A3, a3, c3, k6⟩ := bind_some.mp k5
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c3
    obtain ⟨_, A4, a4, c4, k7⟩ := bind_some.mp k6
    obtain ⟨_, rfl, rfl⟩ := must_some.mp c4
    obtain ⟨ztF, A5, a5, c5, k8⟩ := bind_some.mp k7
    obtain ⟨hzt, rfl, rfl⟩ := need_some.mp c5
    obtain ⟨sW, F4, t4, h4, k9⟩ := bind_some.mp k8
    obtain ⟨gp, F5, t5, h5, k10⟩ := bind_some.mp k9
    obtain ⟨rhoI, F6, t6, h6, k11⟩ := bind_some.mp k10
    obtain ⟨wpl, F7, t7, h7, k12⟩ := bind_some.mp k11
    obtain ⟨sPv, F8, t8, h8, k13⟩ := bind_some.mp k12
    obtain ⟨omV, F9, t9, h9, k14⟩ := bind_some.mp k13
    obtain ⟨tV, F10, t10, h10, k15⟩ := bind_some.mp k14
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k15
    exact ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, h1,
      h2, h3, hzt, h4, h5, rhoI, h6, h7, h8, h9, h10, rfl⟩
  · have hg' : (g == 0) = false := by simpa using hg
    simp only [hg', Bool.false_eq_true, if_false] at k1 ⊢
    obtain ⟨ZE, F2, t2, h2, k2⟩ := bind_some.mp k1
    obtain ⟨tkh, F3, t3, h3, k3⟩ := bind_some.mp k2
    obtain ⟨_, A1, a1, c1, k4⟩ := bind_some.mp k3
    obtain ⟨_, rfl, rfl⟩ := must_some.mp c1
    obtain ⟨Z, A2, a2, c2, k5⟩ := bind_some.mp k4
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c2
    obtain ⟨ends, A3, a3, c3, k6⟩ := bind_some.mp k5
    obtain ⟨_, rfl, rfl⟩ := need_some.mp c3
    obtain ⟨_, A4, a4, c4, k7⟩ := bind_some.mp k6
    obtain ⟨_, rfl, rfl⟩ := must_some.mp c4
    obtain ⟨ztF, A5, a5, c5, k8⟩ := bind_some.mp k7
    obtain ⟨hzt, rfl, rfl⟩ := need_some.mp c5
    obtain ⟨sW, F4, t4, h4, k9⟩ := bind_some.mp k8
    obtain ⟨gp, F5, t5, h5, k10⟩ := bind_some.mp k9
    obtain ⟨rhoI, F6, t6, h6, k11⟩ := bind_some.mp k10
    obtain ⟨wpl, F7, t7, h7, k12⟩ := bind_some.mp k11
    obtain ⟨sPv, F8, t8, h8, k13⟩ := bind_some.mp k12
    obtain ⟨omV, F9, t9, h9, k14⟩ := bind_some.mp k13
    obtain ⟨tV, F10, t10, h10, k15⟩ := bind_some.mp k14
    obtain ⟨rfl, rfl, rfl⟩ := pure_some.mp k15
    exact ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, t1, t2, t3, t4, t5, t6, t7, t8, t9, h1,
      h2, h3, hzt, h4, h5, rhoI, h6, h7, h8, h9, h10, rfl⟩

end OnBytes.Desc.First.K4
