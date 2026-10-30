-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Att/HearStages.lean: what the port's routines for an attention sub-proof's own
messages have heard where they succeed, stage by stage, in the order of the chain of
Cb/Pv/Att/Own.lean.

Main names:
  PscH: what one masked sumcheck has heard behind its riders: mu, eps, for each variable's round the
    scalars and the challenge, the scalars and the challenge of the round of the further variable,
    the end values.
  StageH: one stage: a sumcheck with its riders, its weights and its degree in the further variable;
    a round that batches rows, with an empty message of its own or with scalars; the round that
    draws a point.
  HeardAs stages c c': the stages were heard one after the other from the context c to c', each by
    the block's own listeners (Parts, OnBytes/Tie/Pv/Psc/Run/PscSeam.lean; Blk.recvEs, Blk.closeOne,
    Blk.close, Blk.requireRows, OnBytes/Iop/Ground.lean).
  pair_heard: a sumcheck of products with its row (Pair, OnBytes/Tie/Pv/Att/HearRan.lean), behind
    scalars that are still open, is one stage whose riders are these scalars.
  planes_open: the hidden values of the plane units are received and nothing is closed.
  units_heard: the score units: one stage each; the first has the scalars that were open before it
    among its riders, before its own seven.
  divide_heard, attain_heard: the four stages of divide and the seven of attain.
  own_heard: scores, divide and attain, one after the other.

Limits: one direction: from the routines' success, from a state whose arrays on slots have their
length. The statements are on what was heard; what the records hold, and the typed side, are said in
OnBytes/Tie/Pv/Att/Sc3Top.lean and ScdTop.lean for each sumcheck. The order of the scalars inside a
first message is: what was received first stands first; mu stands last. How many elements the round
that draws the point has drawn, and what the records hold of what was heard, is said in
OnBytes/Tie/Pv/Att/HearPoint.lean and HearSaid.lean.
-/
import OnBytes.Tie.Pv.Att.HearRan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Att
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Attention
open OnBytes.Psc (Weight hearMany hearOne)

/-- What one masked sumcheck has heard behind its riders. -/
structure PscH where
  mu : E
  eps : E
  rs : List (List E × E)
  sentY : List E
  beta : E
  v : List E

/-- One stage. -/
inductive StageH where
  | sum (riders : List E) (ws : List Weight) (dY : Nat) (H : PscH)
  | bat (sent : List E) (rows : Nat) (x : E)
  | point (d : Fmt.Drawn)

/-- The stages were heard one after the other. -/
def HeardAs : List StageH → Ctx → Ctx → Prop
  | [], c, c' => c' = c
  | .sum riders ws dY H :: l, c, c' =>
    ∃ c1 c2, Parts c c1 c2 riders H.mu H.eps ws H.rs dY H.sentY H.beta H.v ∧ HeardAs l c2 c'
  | .bat sent rows x :: l, c, c' =>
    ∃ c1 c2 c3, (Blk.recvEs sent.length).Yields c sent c1 ∧
      (Blk.closeOne RoundName.batSigma.name .elems 0).Yields c1 x c2 ∧
      (Blk.requireRows rows).Yields c2 () c3 ∧ HeardAs l c3 c'
  | .point d :: l, c, c' =>
    ∃ c1, (Blk.close RoundName.zero.name .elems 0).Yields c d c1 ∧ HeardAs l c1 c'

theorem HeardAs.append : ∀ (l l' : List StageH) (c c1 c' : Ctx), HeardAs l c c1 →
    HeardAs l' c1 c' → HeardAs (l ++ l') c c'
  | [], _, _, _, _, h, h' => by
    rw [show _ = _ from h] at h'
    exact h'
  | .sum _ _ _ _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, b, h1, h2⟩ := h
    exact ⟨a, b, h1, HeardAs.append l l' _ c1 c' h2 h'⟩
  | .bat _ _ _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, b, d, h1, h2, h3, h4⟩ := h
    exact ⟨a, b, d, h1, h2, h3, HeardAs.append l l' _ c1 c' h4 h'⟩
  | .point _ :: l, l', _, c1, c', h, h' => by
    obtain ⟨a, h1, h2⟩ := h
    exact ⟨a, h1, HeardAs.append l l' _ c1 c' h2 h'⟩

/-- The weights of a sumcheck of products. -/
abbrev ws3 (nv : Nat) : List Weight := List.replicate nv (Weight.plain 4)

/-- A sumcheck of products behind scalars that are still open. -/
theorem pair_heard {nv nb : Nat} {C : Aff} {W : Array E → Array E} {o : Attention.Sc3}
    {F G : Fork} {c c' : Ctx} (h : Pair nv nb C W o F c G c') (hz : Sized F) (pre : List E)
    (c0 : Ctx) (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    ∃ H : PscH, HeardAs [.sum pre (ws3 nv) 2 H] c0 c' ∧ H.eps = o.p.eps ∧
      o.r.toList = H.rs.map (·.2) ∧ H.rs.map (·.1.length) = List.replicate nv 3 ∧
      H.sentY.length = 2 ∧ H.v.length = 2 * nb := by
  obtain ⟨o1, F2, c2, h1, h2⟩ := h
  obtain ⟨τ, mu, rs, sentY, beta, v, _, a2, _, a4, a5, a6, a7, _, _, _, a12⟩ :=
    sc3In_seam _ _ _ o1 F F2 c c2 h1 hz
  obtain ⟨b1, _, _, b3, b4, _, _, _⟩ := sc3Row_ok o1 o _ F2 G c2 c' h2 a12.sized
  refine ⟨⟨mu, o1.p.eps, rs, sentY, beta, v⟩, ⟨c, c', ?_, rfl⟩, by rw [b3], by rw [b4]; exact a4,
    a5, a6, a7⟩
  rw [b1]
  exact Parts.ride h0 a2

/-- The plane units' hidden values are received and nothing is closed. -/
theorem planes_open : ∀ (n : Nat) (F G : Fork) (c c' : Ctx), PlanesRan n F c G c' → Sized F →
    ∃ v : List E, (Blk.recvEs v.length).Yields c v c' ∧ v.length = 3 * n ∧ Sized G
  | 0, F, G, c, c', h, hz => by
    obtain ⟨e1, e2⟩ := h
    rw [e1, e2]
    exact ⟨[], recvEs_zero c, rfl, hz⟩
  | n + 1, F, G, c, c', h, hz => by
    obtain ⟨j, F1, c1, h1, h2⟩ := h
    obtain ⟨v, a1, a2, _, _, a5⟩ := claimsIn_said 3 F F1 c c1 j h1 hz
    obtain ⟨w, b1, b2, b3⟩ := planes_open n F1 G c1 c' h2 a5
    refine ⟨v ++ w, ?_, by rw [List.length_append, a2, b2]; omega, b3⟩
    rw [List.length_append, a2]
    exact recvEs_add 3 w.length v w c c1 c' a1 b1

/-- The forms of the score units' stages. pre: the scalars that were open before the first. -/
def UnitsForm (S : Shape) : List (Nat × ACall × Seg) → List Score → List E → List StageH → Prop
  | [], [], _, [] => True
  | u :: us, k :: ks, pre, .sum riders ws dY H :: l =>
    (∃ v7 : List E, v7.length = 7 ∧ riders = pre ++ v7) ∧ ws = ws3 (S.nvKF u.2.2) ∧ dY = 2 ∧
      H.eps = k.sc.p.eps ∧ k.sc.r.toList = H.rs.map (·.2) ∧
      H.rs.map (·.1.length) = List.replicate (S.nvKF u.2.2) 3 ∧ H.sentY.length = 2 ∧
      UnitsForm S us ks [] l
  | _, _, _, _ => False

/-- The score units. left: the scalars that are still open behind them. -/
theorem units_heard (S : Shape) (zk : Array (Array E)) :
    ∀ (us : List (Nat × ACall × Seg)) (ks : List Score) (F G : Fork) (c c' : Ctx) (pre : List E)
      (c0 : Ctx), UnitsRan S zk us ks F c G c' → Sized F →
      (Blk.recvEs pre.length).Yields c0 pre c →
      ∃ (st : List StageH) (left : List E) (cm : Ctx), HeardAs st c0 cm ∧
        (Blk.recvEs left.length).Yields cm left c' ∧ Sized G ∧ UnitsForm S us ks pre st ∧
        left = (if us = [] then pre else [])
  | [], [], F, G, c, c', pre, c0, h, hz, h0 => by
    obtain ⟨e1, e2⟩ := h
    rw [e1, e2]
    exact ⟨[], pre, c0, rfl, h0, hz, trivial, rfl⟩
  | u :: us, k :: ks, F, G, c, c', pre, c0, h, hz, h0 => by
    obtain ⟨F1, c1, ⟨Fa, ca, ha, hp⟩, hr⟩ := h
    obtain ⟨v7, a1, a2, _, _, a5⟩ := claimsIn_said 7 F Fa c ca k.s0 ha hz
    have hj : (Blk.recvEs (pre ++ v7).length).Yields c0 (pre ++ v7) ca := by
      rw [List.length_append, a2]
      exact recvEs_add pre.length 7 pre v7 c0 c ca h0 a1
    obtain ⟨H, b1, b2, b3, b4, b5, _⟩ := pair_heard hp a5 (pre ++ v7) c0 hj
    obtain ⟨st, left, cm, d1, d2, d3, d4, d5⟩ :=
      units_heard S zk us ks F1 G c1 c' [] c1 hr (hp.sized a5) (recvEs_zero c1)
    refine ⟨.sum (pre ++ v7) (ws3 (S.nvKF u.2.2)) 2 H :: st, left, cm,
      HeardAs.append [_] st c0 c1 cm b1 d1, d2, d3,
      ⟨⟨v7, a2, rfl⟩, rfl, rfl, b2, b3, b4, b5, d4⟩, ?_⟩
    rw [d5]
    simp
  | [], _ :: _, _, _, _, _, _, _, h, _, _ => h.elim
  | _ :: _, [], _, _, _, _, _, _, h, _, _ => h.elim

/-- A round that batches rows, behind scalars that are still open. -/
theorem batch_heard (n : Nat) (F G : Fork) (c c' : Ctx) (w : Array E)
    (h : SubM.batch n F c = .ok ((w, G), c')) (pre : List E) (c0 : Ctx)
    (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    G = F ∧ ∃ x : E, HeardAs [.bat pre n x] c0 c' ∧ w = powers x n := by
  obtain ⟨_, e, x, c1, a1, a2, a3⟩ := batch_ok n F G c c' w h
  exact ⟨e, x, ⟨c, c1, c', h0, a1, a2, rfl⟩, a3⟩

/-- The four stages of divide. pre: the scalars that were open before it. -/
theorem divide_heard (S : Shape) (d : Divide) (F G : Fork) (c c' : Ctx)
    (h : DivideRan S d F G c c') (hz : Sized F) (pre : List E) (c0 : Ctx)
    (h0 : (Blk.recvEs pre.length).Yields c0 pre c) :
    ∃ (v5 vI v2 vC : List E) (x : E) (HE HM HD : PscH),
      HeardAs [.sum (pre ++ (v5 ++ (vI ++ v2))) (ws3 S.nvE) 2 HE, .bat [] 2 x,
        .sum vC (ws3 S.nvVM) 2 HM, .sum [] (ws3 S.nvVD) 2 HD] c0 c' ∧ Sized G ∧
      v5.length = 5 ∧ vI.length = S.cf.lt ∧ v2.length = 2 ∧ vC.length = 2 ∧
      d.gam = (powers x 2).getD 1 zeroE ∧
      (HE.eps = d.scE.p.eps ∧ d.scE.r.toList = HE.rs.map (·.2)) ∧
      (HM.eps = d.vpm.p.eps ∧ d.vpm.r.toList = HM.rs.map (·.2)) ∧
      (HD.eps = d.vpd.p.eps ∧ d.vpd.r.toList = HD.rs.map (·.2)) := by
  obtain ⟨F1, c1, F2, c2, F3, c3, F4, c4, gamP, F5, c5, F6, c6, F7, c7, h1, h2, h3, pE, hb, hg, h6,
    pM, pD⟩ := h.ran
  obtain ⟨v5, a1, a2, _, _, a5⟩ := claimsIn_said 5 F F1 c c1 _ h1 hz
  obtain ⟨vI, b1, b2, _, _, b5⟩ := claimsIn_said _ F1 F2 c1 c2 _ h2 a5
  obtain ⟨v2, d1, d2, _, _, d5⟩ := claimsIn_said 2 F2 F3 c2 c3 _ h3 b5
  have hj : (Blk.recvEs (pre ++ (v5 ++ (vI ++ v2))).length).Yields c0 (pre ++ (v5 ++ (vI ++ v2)))
      c3 := by
    simp only [List.length_append]
    rw [a2, b2, d2]
    exact recvEs_add _ _ _ _ c0 c c3 h0 (recvEs_add _ _ _ _ c c1 c3 a1
      (recvEs_add _ _ _ _ c1 c2 c3 b1 d1))
  obtain ⟨HE, e1, e2, e3, _⟩ := pair_heard pE d5 _ c0 hj
  have s4 := pE.sized d5
  obtain ⟨eF, x, f1, f2⟩ := batch_heard 2 F4 F5 c4 c5 gamP hb [] c4 (recvEs_zero c4)
  rw [eF] at h6
  obtain ⟨vC, g1, g2, _, _, g5⟩ := claimsIn_said 2 F4 F6 c5 c6 _ h6 s4
  obtain ⟨HM, m1, m2, m3, _⟩ := pair_heard pM g5 vC c5 (by rw [g2]; exact g1)
  have s7 := pM.sized g5
  obtain ⟨HD, n1, n2, n3, _⟩ := pair_heard pD s7 [] c7 (recvEs_zero c7)
  exact ⟨v5, vI, v2, vC, x, HE, HM, HD,
    HeardAs.append [_] _ c0 c4 c' e1 (HeardAs.append [_] _ c4 c5 c' f1
      (HeardAs.append [_] _ c5 c7 c' m1 n1)), pD.sized s7, a2, b2, d2, g2, by rw [hg, f2],
    ⟨e2, e3⟩, ⟨m2, m3⟩, ⟨n2, n3⟩⟩

/-- The sumcheck by degrees with the round that batches its pairs. -/
theorem key_heard (S : Shape) (scF : Attention.Sc3) (o : Attention.Scd) (F G : Fork) (c c' : Ctx)
    (h : keyAtIndexIn S scF F c = .ok ((o, G), c')) (hz : Sized F) :
    ∃ (x : E) (H : PscH),
      HeardAs [.bat [] S.NP x,
        .sum [] (S.scdDegrees.map fun d => Weight.plain (d + 1)) (S.cf.lt + 1) H] c c' ∧ Sized G ∧
      H.eps = o.p.eps ∧ o.r.toList = H.rs.map (·.2) := by
  obtain ⟨om4, F1, c1, o1, F2, c2, h1, h2, h3⟩ := keyAtIndexIn_flat S scF o F G c c' h
  obtain ⟨eF, x, f1, _⟩ := batch_heard S.NP F F1 c c1 om4 h1 [] c (recvEs_zero c)
  rw [eF] at h2
  obtain ⟨τ, mu, rs, sentY, beta, v, _, a2, _, a4, _, _, _, _, _, _, _, a12⟩ :=
    scdIn_seam _ _ _ _ o1 F F2 c1 c2 h2 hz
  obtain ⟨b1, _, b3, b4, _, b6⟩ := scdRow_ok o1 o _ F2 G c2 c' h3 a12.sized
  refine ⟨x, ⟨mu, o1.p.eps, rs, sentY, beta, v⟩,
    HeardAs.append [_] _ c c1 c' f1 ⟨c1, c', ?_, rfl⟩, b6.sized, by rw [b3], by rw [b4]; exact a4⟩
  rw [b1]
  exact a2

/-- The seven stages of attain. -/
theorem attain_heard (S : Shape) (x : Attain) (F G : Fork) (c c' : Ctx)
    (h : AttainRan S x F G c c') (hz : Sized F) :
    ∃ (d : Fmt.Drawn) (vM : List E) (xF xD xH : E) (HF HD HH : PscH),
      HeardAs [.point d, .bat vM S.NP xF, .sum [] (ws3 S.nvF) 2 HF, .bat [] S.NP xD,
        .sum [] (S.scdDegrees.map fun d => Weight.plain (d + 1)) (S.cf.lt + 1) HD,
        .bat [] S.NP xH, .sum [] (ws3 S.nvH) 2 HH] c c' ∧ Sized G ∧ vM.length = S.NP ∧
      x.tg = (d.elems.map E.ofTriple).toArray.extract 0 S.cf.lgk ∧
      x.ti = (d.elems.map E.ofTriple).toArray.extract S.cf.lgk (S.cf.lgk + S.cf.lt) ∧
      (HF.eps = x.scF.p.eps ∧ x.scF.r.toList = HF.rs.map (·.2)) ∧
      (HD.eps = x.scd.p.eps ∧ x.scd.r.toList = HD.rs.map (·.2)) ∧
      (HH.eps = x.scH.p.eps ∧ x.scH.r.toList = HH.rs.map (·.2)) := by
  obtain ⟨pts, Fp, cp, F0, c0, om, F1, c1, F2, c2, F3, c3, om5, F4, c4, hp, t1, t2, hM, hb, pF, hK,
    hb5, pH⟩ := h.ran
  obtain ⟨eP, d, p1, p2⟩ := point_ok _ F Fp c cp pts hp
  rw [eP] at hM
  obtain ⟨vM, a1, a2, _, _, a5⟩ := claimsIn_said _ F F0 cp c0 _ hM hz
  obtain ⟨eF, xF, f1, _⟩ := batch_heard S.NP F0 F1 c0 c1 om hb vM cp (by rw [a2]; exact a1)
  rw [eF] at pF
  obtain ⟨HF, g1, g2, g3, _⟩ := pair_heard pF a5 [] c1 (recvEs_zero c1)
  have s2 := pF.sized a5
  obtain ⟨xD, HD, k1, k2, k3, k4⟩ := key_heard S x.scF x.scd F2 F3 c2 c3 hK s2
  obtain ⟨e5, xH, m1, _⟩ := batch_heard S.NP F3 F4 c3 c4 om5 hb5 [] c3 (recvEs_zero c3)
  rw [e5] at pH
  obtain ⟨HH, n1, n2, n3, _⟩ := pair_heard pH k2 [] c4 (recvEs_zero c4)
  exact ⟨d, vM, xF, xD, xH, HF, HD, HH,
    HeardAs.append [_] _ c cp c' ⟨cp, p1, rfl⟩ (HeardAs.append [_] _ cp c1 c' f1
      (HeardAs.append [_] _ c1 c2 c' g1 (HeardAs.append [_, _] _ c2 c3 c' k1
        (HeardAs.append [_] _ c3 c4 c' m1 n1)))), pH.sized k2, a2, by rw [t1, p2], by rw [t2, p2],
    ⟨g2, g3⟩, ⟨k3, k4⟩, ⟨n2, n3⟩⟩

/-- scores, divide and attain, one after the other: the stages of the own rounds. -/
theorem own_heard (S : Shape) (zk : Array (Array E)) (sc : Array PlaneClaim × Array Score)
    (d : Divide) (x : Attain) (F F1 F2 G : Fork) (c c1 c2 c' : Ctx)
    (hs : scores S zk F c = .ok ((sc, F1), c1)) (hd : divide S zk F1 c1 = .ok ((d, F2), c2))
    (hx : attain S F2 c2 = .ok ((x, G), c')) (hz : Sized F) :
    ∃ (ks : List Score) (planes : List E) (units : List StageH) (v5 vI v2 vC : List E) (xV : E)
      (HE HM HVD : PscH) (dr : Fmt.Drawn) (vM : List E) (xF xD xH : E) (HF HD HH : PscH),
      sc.2 = ks.toArray ∧ planes.length = 3 * (unitsOf S Table.kr [Seg.rm, Seg.rd]).length ∧
      UnitsForm S (unitsOf S Table.kfd [Seg.fm, Seg.fd]) ks planes units ∧
      HeardAs (units ++ ([.sum ((if unitsOf S Table.kfd [Seg.fm, Seg.fd] = [] then planes else [])
            ++ (v5 ++ (vI ++ v2))) (ws3 S.nvE) 2 HE, .bat [] 2 xV,
          .sum vC (ws3 S.nvVM) 2 HM, .sum [] (ws3 S.nvVD) 2 HVD] ++
        [.point dr, .bat vM S.NP xF, .sum [] (ws3 S.nvF) 2 HF, .bat [] S.NP xD,
          .sum [] (S.scdDegrees.map fun d => Weight.plain (d + 1)) (S.cf.lt + 1) HD,
          .bat [] S.NP xH, .sum [] (ws3 S.nvH) 2 HH])) c c' ∧
      Sized G ∧ v5.length = 5 ∧ vI.length = S.cf.lt ∧ v2.length = 2 ∧ vC.length = 2 ∧
      vM.length = S.NP ∧ d.gam = (powers xV 2).getD 1 zeroE := by
  obtain ⟨Fa, ca, ks, p1, p2, p3⟩ := scores_ran S zk sc F F1 c c1 hs
  obtain ⟨planes, a1, a2, a3⟩ := planes_open _ F Fa c ca p1 hz
  obtain ⟨units, left, cm, b1, b2, b3, b4, b5⟩ :=
    units_heard S zk _ ks Fa F1 ca c1 planes c p3 a3 a1
  obtain ⟨v5, vI, v2, vC, xV, HE, HM, HVD, d1, d2, d3, d4, d5, d6, d7, _⟩ :=
    divide_heard S d F1 F2 c1 c2 (divide_ran S zk d F1 F2 c1 c2 hd) b3 left cm b2
  obtain ⟨dr, vM, xF, xD, xH, HF, HD, HH, e1, e2, e3, _⟩ :=
    attain_heard S x F2 G c2 c' (attain_ran S x F2 G c2 c' hx) d2
  rw [b5] at d1
  exact ⟨ks, planes, units, v5, vI, v2, vC, xV, HE, HM, HVD, dr, vM, xF, xD, xH, HF, HD, HH, p2, a2,
    b4, HeardAs.append _ _ c cm c' b1 (HeardAs.append _ _ cm c2 c' d1 e1), e2, d3, d4, d5, d6, e3,
    d7⟩

end OnBytes.Tie.Pv.Att

#print axioms OnBytes.Tie.Pv.Att.units_heard
#print axioms OnBytes.Tie.Pv.Att.divide_heard
#print axioms OnBytes.Tie.Pv.Att.key_heard
#print axioms OnBytes.Tie.Pv.Att.attain_heard
#print axioms OnBytes.Tie.Pv.Att.own_heard
#print axioms OnBytes.Tie.Pv.Att.HeardAs.append
#print axioms OnBytes.Tie.Pv.Att.pair_heard
#print axioms OnBytes.Tie.Pv.Att.planes_open
