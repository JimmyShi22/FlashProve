-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/GatedTape.lean: the stretch `hearGated` of the layers' own rounds
(OnBytes/Desc/First/K4/Hear.lean:153-165), over the plain engine `engFl`, TAKEN APART WHERE IT
RETURNS: which calls it has made, and WHERE ON THE TAPE each stands. One statement and its proof.

  `hearGated_tape`: if `hearGated engFl P H K F t` returns ((hd, hd2), G, u): H.tT is some tT; from
    round 0 on, P.rd.muH + 4 rounds: the first product layer, as a return of `Fl.levelIn` at the
    point `downFrom K.rs K.fin.wD ++ H.ztF` and the start form `Aff.slot K.sH1`; ROUND P.rd.muH + 4
    DRAWS THE POINT rhoM, of P.y.h.ll - 1 elements: here it is `(drawnAt t (P.rd.muH + 4)).toArray`,
    a function of the tape; from round P.rd.muH + 5 on: the second product layer, as a return of
    `Fl.levelIn` at the point `rhoM ++ downFrom K.rs P.y.lfe ++ tT.r` and the start form `start2
    P.y.LamM K.sH1 rhoM` (Johnson/Road/Rows/GatedEnds.lean: the text's Hear.lean:160-162,
    in the verifier's own letters), on the ledger that the first layer left.

No new argument: `point_spec` (OnBytes/Desc/First/P1/BatchPoint.lean), `levelIn_rest`, `drop_next`
(OnBytes/Desc/First/K4/NormsTape.lean), `drawnAt` (OnBytes/Desc/First/K4/EmbTape.lean). One
direction: from a return. Nothing is said of what the calls mean. tT is pinned by H.tT; the ledger
G1 between the two layers stands under "there is", pinned by the first layer's return.
-/
import OnBytes.Desc.First.K4.EmbTape
import Johnson.Road.Rows.GatedEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes OnBytes.K.Kc
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
open OnBytes.Desc.First.P1 (bind_some pure_some need_some point_spec)

/-- **Where the gated products' stretch returns, and where on the tape it stands.** -/
theorem hearGated_tape {P : Pub} {H : Heard} {K : HeardStack} {F G : Fork} {t u : Tape}
    {hd hd2 : Level} (h : hearGated engFl P H K F t = some ((hd, hd2), G, u)) :
    ∃ (tT : Tsc) (G1 : Fork),
      H.tT = some tT ∧
      Fl.levelIn P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1)
        (orderRange P.rd.muH) F t = some (hd, G1, t.drop (P.rd.muH + 4)) ∧
      (drawnAt t (P.rd.muH + 4)).length = P.y.h.ll - 1 ∧
      Fl.levelIn P.rd.muH2
        ((drawnAt t (P.rd.muH + 4)).toArray ++ downFrom K.rs P.y.lfe ++ tT.r)
        (Road.Rows.start2 P.y.LamM K.sH1 (drawnAt t (P.rd.muH + 4)).toArray) (orderRange P.rd.muH2)
        G1
        (t.drop (P.rd.muH + 4 + 1)) = some (hd2, G, u) := by
  unfold hearGated at h
  obtain ⟨hd', G1, u1, c1, k1⟩ := bind_some.mp h
  obtain ⟨tT, A1, a1, c2, k2⟩ := bind_some.mp k1
  obtain ⟨e2, rfl, rfl⟩ := need_some.mp c2
  obtain ⟨rhoM, G2, u2, c3, k3⟩ := bind_some.mp k2
  obtain ⟨hd2', G3, u3, c4, k4⟩ := bind_some.mp k3
  obtain ⟨e5, rfl, rfl⟩ := pure_some.mp k4
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e5
  have c1' : Fl.levelIn P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1)
      (orderRange P.rd.muH) F t = some (hd', G1, u1) := c1
  have p1 : u1 = t.drop (P.rd.muH + 4) := levelIn_rest c1'
  have c3' : Fl.point .join (P.y.h.ll - 1) G1 u1 = some (rhoM, G2, u2) := c3
  obtain ⟨rfl, w, d, e3, l3, hr⟩ := point_spec c3'
  have p2 : u2 = t.drop (P.rd.muH + 4 + 1) := drop_next p1 e3
  have q : drawnAt t (P.rd.muH + 4) = d := drawnAt_cons (u := u2) (by rw [← p1]; exact e3)
  refine ⟨tT, G1, e2, ?_, ?_, ?_⟩
  · rw [← p1]
    exact c1'
  · rw [q]
    exact l3
  · rw [q, ← hr, ← p2]
    exact c4

end OnBytes.Desc.First.K4

#print axioms OnBytes.Desc.First.K4.hearGated_tape
