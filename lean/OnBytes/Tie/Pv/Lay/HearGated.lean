-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearGated.lean: the verifier's routine for the two product layers of the gated
products in a layers' sub-proof (hearGated, OnBytes/Model/Layer.lean): what it has heard where it
succeeds.

Main names:
  `routedStart`: the start form of the second layer: the routed layers' never-sent values under the
    equality weights of the join's point.
  `GatedSaid`: with routed experts: the token sumcheck of the terms was run; the two layers'
    records.
  `gated_heard`: with routed experts and more than one layer bit: seven stages: the first layer's
    sumcheck and its LINE; an idle step; the join's point; the second layer's sumcheck and its LINE;
    an idle step.
  `gated_heard_plain`: without routed experts: the first three of them.

Limits: those of OnBytes/Tie/Pv/Lay/HearL.lean. A group with routed experts and a single layer bit
draws no point: that case is not stated.
-/
import OnBytes.Tie.Pv.Lay.HearL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH)

/-- The start form of the second layer. -/
def routedStart (y : Lay) (sH1 : Nat) (rhoM : Array E) : Aff :=
  (List.range y.LamM).foldl
    (fun (C : Aff) lm => C.addMul (Aff.slot (sH1 + 1 + lm)) ((eqTab rhoM).getD lm zeroE)) aff0

/-- Without routed experts. -/
theorem gated_heard_plain (P : Pub) (H : Heard) (K : HeardStack) (F G : Fork) (c c' : Ctx)
    (hd : Level) (hd2 : Option Level) (hp : P.y.h.p3 = false)
    (h : hearGated P H K F c = .ok (((hd, hd2), G), c')) (hs : Sized F) :
    hd2 = none ∧ ∃ H5 : PscH,
      HeardL [.sum [] (levelWeights P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF)
        (orderRange P.rd.muH)) 2 H5, .line hd.tau, .idle] c c' ∧
      LevelSaid P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1) (orderRange P.rd.muH)
        F G hd H5 := by
  simp only [hearGated, hp, Bool.not_false, if_true] at h
  obtain ⟨o, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k2
  obtain ⟨a1, s1⟩ := note_still _ _ _ _ _ _ _ h2
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain ⟨H5, b1, b2⟩ := level_heard _ _ _ _ F F1 c c1 _ h1 hs
  rw [e2, a1, e3]
  exact ⟨rfl, H5, HeardL.append [_, _] [_] c c1 c2 b1 s1.heard, b2⟩

/-- With routed experts: the records. -/
structure GatedSaid (P : Pub) (H : Heard) (K : HeardStack) (F G : Fork) (hd hd2 : Level)
    (H5 H6 : PscH) (d : Fmt.Drawn) : Prop where
  said : ∃ (tT : Tsc) (F1 : Fork), H.tT = some tT ∧
    LevelSaid P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF) (Aff.slot K.sH1) (orderRange P.rd.muH)
      F F1 hd H5 ∧
    LevelSaid P.rd.muH2
      ((d.elems.map E.ofTriple).toArray ++ downFrom K.rs P.y.lfe ++ tT.r)
      (routedStart P.y K.sH1 (d.elems.map E.ofTriple).toArray) (orderRange P.rd.muH2) F1 G hd2 H6
  /-- the join's point has one coordinate for each layer bit but one -/
  join : d.elems.length = P.y.h.ll - 1

/-- With routed experts and more than one layer bit. -/
theorem gated_heard (P : Pub) (H : Heard) (K : HeardStack) (F G : Fork) (c c' : Ctx)
    (hd : Level) (o2 : Option Level) (hp : P.y.h.p3 = true) (hl : P.y.h.ll > 1)
    (h : hearGated P H K F c = .ok (((hd, o2), G), c')) (hs : Sized F) :
    ∃ (hd2 : Level) (tT : Tsc) (H5 H6 : PscH) (d : Fmt.Drawn), o2 = some hd2 ∧ H.tT = some tT ∧
      HeardL [.sum [] (levelWeights P.rd.muH (downFrom K.rs K.fin.wD ++ H.ztF)
          (orderRange P.rd.muH)) 2 H5, .line hd.tau, .idle, .point .join d,
        .sum [] (levelWeights P.rd.muH2
          ((d.elems.map E.ofTriple).toArray ++ downFrom K.rs P.y.lfe ++ tT.r)
          (orderRange P.rd.muH2)) 2 H6, .line hd2.tau, .idle] c c' ∧
      GatedSaid P H K F G hd hd2 H5 H6 d := by
  simp only [hearGated, hp, hl, Bool.not_true, if_true, if_false, Bool.false_eq_true] at h
  obtain ⟨o, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨_, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨tT, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨rhoM, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨p2, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨_, F6, c6, h6, k6⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 k6
  obtain ⟨a2, s2⟩ := note_still _ _ _ _ _ _ _ h2
  obtain ⟨t3, a3, a3'⟩ := (getS_ok _ _ _ _ _ _).1 h3
  obtain ⟨a4, d, p4, r4, n4⟩ := pointR_ok _ _ _ _ _ _ _ h4
  obtain ⟨a6, s6⟩ := note_still _ _ _ _ _ _ _ h6
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e1
  obtain ⟨H5, b1, b2⟩ := level_heard _ _ _ _ F F1 c c1 _ h1 hs
  have hF4 : F4 = F1 := by rw [a4, a3, a2]
  rw [hF4, r4] at h5
  obtain ⟨H6, b3, b4⟩ := level_heard _ _ _ _ F1 F5 c4 c5 _ h5 b2.sized
  rw [a3'] at p4
  refine ⟨p2, tT, H5, H6, d, rfl, t3, ?_, ⟨⟨tT, F1, t3, b2, ?_⟩, n4⟩⟩
  · rw [e3]
    exact HeardL.append [_, _] _ c c1 c6 b1 (HeardL.append [_] _ c1 c2 c6 s2.heard
      (HeardL.append [_] _ c2 c4 c6 p4 (HeardL.append [_, _] [_] c4 c5 c6 b3 s6.heard)))
  · rw [e2, a6]
    exact b4

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.gated_heard_plain
#print axioms OnBytes.Tie.Pv.Lay.gated_heard
