-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearAll.lean: what the verifier's routine for all own messages of a layers'
sub-proof (hearOwn, OnBytes/Model/Layer.lean) has heard where it succeeds: all stages, in the order
of the chain of Cb/Pv/Lay/Own.lean, with each sumcheck's record.

The parts are proved in OnBytes/Tie/Pv/Lay/HearNorms.lean (the points, the limbs' scalars, the
norms' join, the sums of squares), HearMid.lean (the row products, the terms, the batched inner
products) and HearFoot.lean (the gated products, the routed ones, the merge of the weight claims).
Here they are put together over `hearOwn_ran` (HearOwn.lean).

Main names:
  `OwnH`: all that was heard: the points drawn, the scalars sent, the elements drawn, and for each
    of the seven sumchecks what it has heard.
  `OwnH.stages`: the stages, in order. Idle steps stand where the routine keeps a value or marks a
    test.
  `OwnSaidL`: the numbers of elements of the points drawn, and the records: for each stage what its
    routine hands on, in the words of the parts' files.
  `own_heardL`: if hearOwn succeeds from a state whose arrays on slots have their length, in a
    sub-proof with terms, with routed experts and with more than one layer bit: there is such an
    `OwnH`, its stages were heard from the first context to the last, and the records hold.
  `own_coin`: on a view, if no mark of a failed test stands behind hearOwn, the coefficient drawn in
    the sumcheck of the terms is not 0: "no mark" is carried back along the later stages
    (OnBytes/Tie/Pv/Lay/HearMark.lean), "on a view" forward along the earlier ones
    (OnBytes/Tie/Pv/Lay/HearViewL.lean).

Limits: where there is a single norm (lNI = 0) the routine draws no point for the norms' join and
the list has no stage for it, while the chain of Cb/Pv/Lay/Own.lean always has that round:
`own_heardL` does not shut that case out, and whoever ties the list to the chain has to. For the
rest those of OnBytes/Tie/Pv/Lay/HearL.lean: one direction, from the routine's success; a routine's
success does not say that its tests on values held. The lookup's messages before, and the reads'
root behind, are not in hearOwn. The typed side is in OnBytes/Tie/Pv/Lay/OwnTieL.lean; it is not
named here.
-/
import OnBytes.Tie.Pv.Lay.HearNorms
import OnBytes.Tie.Pv.Lay.HearMid
import OnBytes.Tie.Pv.Lay.HearFoot
import OnBytes.Tie.Pv.Lay.HearViewL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH)

/-- All that was heard. -/
structure OwnH where
  /-- the token point; the first group's two points; the norms' join; the routed layers' join -/
  dV : Fmt.Drawn
  dE : Fmt.Drawn
  dK : Fmt.Drawn
  dI : Fmt.Drawn
  dM : Fmt.Drawn
  /-- the limbs' scalars, the products' scalars, the embedding's scalar (or none) -/
  vW : List E
  vP : List E
  vE : List E
  /-- the elements of the four rounds that batch -/
  xL : E
  xP : E
  x4 : E
  xW : E
  /-- the sums that the two token sumchecks' first messages name -/
  cl2 : E
  cl3 : E
  /-- the seven sumchecks -/
  H1 : PscH
  H2 : PscH
  H3 : PscH
  H4 : PscH
  H5 : PscH
  H6 : PscH
  H7 : PscH

/-- The norms' join's point. -/
def OwnH.rhoI (D : OwnH) (P : Pub) : Array E :=
  if P.rd.lNI != 0 then (D.dI.elems.map E.ofTriple).toArray else #[]

/-- The stages, in order. H0: what hearNorms returns; tT: the record of the terms' sumcheck; rows:
the number of the claims on the weights. -/
def OwnH.stages (D : OwnH) (P : Pub) (hp : HPlan2) (g : Nat) (H0 : Heard) (O : Own) (tT : Tsc)
    (hd2 : Level) (rows : Nat) : List StageL :=
  ([.point .zero D.dV] ++ firstStages g D.dE ++ firstStages g D.dK ++ [.idle] ++
    [.bat D.vW (ledNS P.y.h.xl) D.xL] ++ joinStages P.rd.lNI D.dI ++
    [.sum [] (levelWeights P.rd.muV (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).2
      (orderDefault P.rd.muV)) 2 D.H1, .line H0.wpl.tau]) ++
  ([.bat D.vP (ledNP P.y.h.xl * P.y.NI) D.xP,
    .sum [D.cl2] (tokenWeights H0.PV P.y.h.lt) 2 D.H2] ++ [.idle]) ++
  [.sum [D.cl3] (tokenWeights H0.ztF P.y.h.lt) 1 D.H3, .idle] ++
  [.bat [] 2 D.x4, .sum [] (List.replicate hp.lamS (Weight.plain 3)) 2 D.H4, .idle] ++
  footStages P O.H O.K tT O.hd hd2 D.H5 D.H6 D.H7 D.dM D.vE rows D.xW

/-- The number of the claims on the weights without the embedding's. -/
def nclp (hp : HPlan2) (g : Nat) : Nat := hp.NCL - (if g == 0 then 1 else 0)

/-- The records. -/
structure OwnSaidL (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (D : OwnH) (H0 : Heard) (tT : Tsc) (hd2 : Level) (claims : Array WsClaim) : Prop where
  PV : H0.PV = (D.dV.elems.map E.ofTriple).toArray
  ZE : H0.ZE = (if g == 0 then (D.dE.elems.map E.ofTriple).toArray else #[])
  tkh : H0.tkh = (if g == 0 then (D.dK.elems.map E.ofTriple).toArray else #[])
  ztF : (lastOf fo.zx P.y.h.lt).toOption = some H0.ztF
  /-- the points have as many elements as the routine asks for -/
  nV : D.dV.elems.length = P.y.h.lt
  nE : (g == 0) = true → D.dE.elems.length = P.y.ls + P.y.h.lt
  nK : (g == 0) = true → D.dK.elems.length = P.y.lPd - P.y.ls
  nI : (P.rd.lNI != 0) = true → D.dI.elems.length = P.rd.lNI
  nM : D.dM.elems.length = P.y.h.ll - 1
  lenW : D.vW.length = ledNS P.y.h.xl * P.y.NI
  sW : H0.sW = F.next
  gp : H0.gp = powers D.xL (ledNS P.y.h.xl)
  lenP : D.vP.length = ledNP P.y.h.xl * P.y.NI
  omV : H0.omV = powers D.xP (ledNP P.y.h.xl * P.y.NI)
  lenE : D.vE.length = (if g == 0 then 1 else 0)
  count : claims.size = hp.NCL
  hasHd2 : O.hd2 = some hd2
  hasT : O.H.tT = some tT
  /-- the states between the stages, with the seven records -/
  recs : ∃ (F4 F7 F8 F1 F1' F2 F3 F3' F5 F6 : Fork) (t3 : Tsc) (C : Aff) (p4 : Psc) (c1 c5 : Ctx),
    Filled (taken F (ledNS P.y.h.xl * P.y.NI)) F4 F.next D.vW oneE ∧
    LevelSaid P.rd.muV (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).2
      (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).1 (orderDefault P.rd.muV) F4 F7 H0.wpl D.H1 ∧
    H0.sPv = F7.next ∧ Filled (taken F7 (ledNP P.y.h.xl * P.y.NI)) F8 F7.next D.vP oneE ∧
    TokSaid H0.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F8 F1 H0.tV D.cl2 D.H2 ∧
    TokSaid H0.ztF P.y.h.lt (nEndT P.y) 1 F1 F1' t3 D.cl3 D.H3 ∧
    tT = { t3 with p := { t3.p with rowMade := true } } ∧
    O.H = { H0 with tT := some tT, KT := (t3.p.rowForm zeroE {}).scale (negE (invE t3.p.eps)) } ∧
    Filled F1' F2 t3.p.first (List.replicate t3.p.walk.1.length zeroE) (subE zeroE oneE) ∧
    joinStart O.v O.H (powers D.x4 2) F2 c1 = .ok ((C, F2), c1) ∧
    StackSaid hp.lamS (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + nclp hp g) C F2 F3 O.K p4
      D.H4 ∧
    Filled (taken F2 (1 + 2 * hp.lamS +
      (2 + (2 + (1 + (if P.y.h.p3 then P.y.LamM else 0)) + nclp hp g)))) F3' O.K.sA0 D.H4.v
      D.H4.beta ∧
    Filled F3' F3 p4.first (List.replicate p4.walk.1.length zeroE) (subE zeroE oneE) ∧
    StackFin P O.v O.H hp.lamS (nclp hp g) tT O.K (powers D.x4 2) F2 F3' c1 c5 ∧
    GatedSaid P O.H O.K F3 F5 O.hd hd2 D.H5 D.H6 D.dM ∧
    ((g == 0) = true → O.sVE = F5.next ∧ Filled (taken F5 1) F6 F5.next D.vE oneE) ∧
    ((g == 0) = false → F6 = F5) ∧
    MergeSaid P.wsLay claims (claimSlots g (nclp hp g) O.K.sV O.sVE) F6 G O.wo D.xW D.H7

/-- All own messages of a layers' sub-proof. -/
theorem own_heardL (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) (h : hearOwn P hp g fo F c = .ok ((O, G), c')) (hs : Sized F)
    (hne : P.rd.tscCalls.isEmpty = false) (hp3 : P.y.h.p3 = true) (hl : P.y.h.ll > 1) :
    ∃ (D : OwnH) (H0 : Heard) (tT : Tsc) (hd2 : Level) (claims : Array WsClaim),
      HeardL (D.stages P hp g H0 O tT hd2 (claimSlots g (nclp hp g) O.K.sV O.sVE).size) c c' ∧
      OwnSaidL P hp g fo O F G D H0 tT hd2 claims := by
  obtain ⟨H0, claims, F1, F2, F3, F4, F5, c1, c2, c3, c4, c5, c6, h1, h2, h3, h4, hN, h5, h6, s6,
    _⟩ :=
    (hearOwn_ran P hp g fo O F G c c' h).ran
  obtain ⟨dV, dE, dK, dI, vW, xL, H1, rhoI, Fa, Fb, Fc, Fd, c7, c8, c9, c10, p1, nn, r1, r2, r3, r4,
    r5, r6, r7, r8, r9, q1, e1, e2, e3, s10, _, _⟩ := norms_heard P g fo H0 F F1 c c1 h1 hs
  obtain ⟨vP, xP, cl2, H2, p2, t1, t2, t3, t4, q2⟩ :=
    rows_heard _ _ _ _ Fb Fc Fd F1 c7 c8 c9 c10 _ _ _ e1 e2 e3 q1.sized
  obtain ⟨u3, F1', cl3, H3, pp, p3, q3, u1, u2, u4⟩ :=
    terms_heard P H0 O.H F1 F2 c1 c2 hne h2 q2.sized
  have hT : O.H.tT = some { u3 with p := pp } := by rw [u4]
  obtain ⟨x4, C, p4, H4, F3', cj, ck, p5, v1, q4, v2, v3, v4⟩ :=
    stack_heard P O.v O.H hp.lamS _ _ hT O.K F2 F3 c2 c3 h3 u2.sized
  obtain ⟨hd2, tT, H5, H6, H7, dM, vE, xW, w1, w2, p6, q5, w3, w4, w5, q6⟩ :=
    foot_heard P O.H O.K (g == 0) claims (fun s => claimSlots g (nclp hp g) O.K.sV s) O.hd O.hd2
        O.sVE
      O.wo F3 F4 F5 G c3 c4 c5 c6 c' hp3 hl h4 h5 h6 s6 v3.sized
  have htT : tT = { u3 with p := { u3.p with rowMade := true } } := by
    rw [hT, u1] at w2
    exact (Option.some.inj w2).symm
  refine ⟨⟨dV, dE, dK, dI, dM, vW, vP, vE, xL, xP, x4, xW, cl2, cl3, H1, H2, H3, H4, H5, H6, H7⟩,
      H0,
    tT, hd2, claims, ?_, ?_⟩
  · rw [r9] at p1
    exact HeardL.append _ _ c c3 c' (HeardL.append _ _ c c2 c3 (HeardL.append _ _ c c1 c2
      (HeardL.append _ _ c c7 c1 p1 (HeardL.append _ _ c7 c10 c1 p2 s10.heard)) p3) p5) p6
  · rw [r9] at q1
    refine ⟨r1, r2, r3, r4, nn.1, nn.2.1, nn.2.2.1, nn.2.2.2, q5.join, r5, r6, r8, t1, t4, w3, hN,
      w1, w2, Fa, Fb, Fc, F1, F1', F2, F3, F3', F4, F5, u3, C, p4, cj, ck, r7, q1, t2, t3, q2, q3,
          htT, ?_, u2, v1, q4, v2, v3, ?_, q5, w4, w5,
      q6⟩
    · rw [u4, htT, u1]
    · rw [htT, ← u1]
      exact v4

/-- On a view: if no mark of a failed test stands behind hearOwn, the coefficient that was drawn in
the sumcheck of the terms is not 0. -/
theorem own_coin (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) (h : hearOwn P hp g fo F c = .ok ((O, G), c')) (hs : Sized F)
    (hne : P.rd.tscCalls.isEmpty = false) (hp3 : P.y.h.p3 = true) (hl : P.y.h.ll > 1)
    (hv : c.ch.dry = false) (hm : c'.failed = none) :
    ∃ tT : Tsc, O.H.tT = some tT ∧ isZeroE tT.p.eps = false := by
  obtain ⟨H0, claims, F1, F2, F3, F4, F5, c1, c2, c3, c4, c5, c6, h1, h2, h3, h4, _, h5, h6, s6,
    _⟩ := (hearOwn_ran P hp g fo O F G c c' h).ran
  obtain ⟨_, _, _, _, _, _, _, _, _, Fb, Fc, Fd, c7, c8, c9, c10, p1, _, _, _, _, _, _, _, _, _, _,
    q1, e1, e2, e3, s10, _, _⟩ := norms_heard P g fo H0 F F1 c c1 h1 hs
  obtain ⟨_, _, _, _, p2, _, _, _, _, q2⟩ :=
    rows_heard _ _ _ _ Fb Fc Fd F1 c7 c8 c9 c10 _ _ _ e1 e2 e3 q1.sized
  obtain ⟨u3, _, _, _, pp, p3, _, _, u2, u4⟩ := terms_heard P H0 O.H F1 F2 c1 c2 hne h2 q2.sized
  have hT : O.H.tT = some { u3 with p := pp } := by rw [u4]
  obtain ⟨_, _, _, _, _, _, _, p5, _, _, _, v3, _⟩ :=
    stack_heard P O.v O.H hp.lamS _ _ hT O.K F2 F3 c2 c3 h3 u2.sized
  obtain ⟨_, _, _, _, _, _, _, _, _, _, p6, _⟩ :=
    foot_heard P O.H O.K (g == 0) claims (fun s => claimSlots g (nclp hp g) O.K.sV s) O.hd O.hd2
      O.sVE O.wo F3 F4 F5 G c3 c4 c5 c6 c' hp3 hl h4 h5 h6 s6 v3.sized
  have m2 : c2.failed = none := (heardL_mark_split _ _ c2 c3 c' p5 p6 hm).2
  obtain ⟨_, _, _, d7, _⟩ := heardL_view _ c c7 hv p1
  obtain ⟨_, _, _, d10, _⟩ := heardL_view _ c7 c10 d7 p2
  have d1 : c1.ch.dry = false := by
    rw [s10.ch]
    exact d10
  obtain ⟨_, _, _, d2, _⟩ := heardL_view _ c1 c2 d1 p3
  exact terms_coin P H0 O.H F1 F2 c1 c2 hne h2 m2 d2

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.own_heardL
#print axioms OnBytes.Tie.Pv.Lay.own_coin
