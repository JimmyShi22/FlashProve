-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Keeps/LayerCut.lean: the run of the verifier program on an accepted proof file, cut
at the borders of the routines that receive a layers' sub-proof's own messages.

A block of the verifier program decides a chain whole. Whoever ties a routine inside it to a typed
block needs the routine's own success, from its own state and context. This file gives it for the
lookup's routine and for hearOwn of a layers' link (OnBytes/Model/Layer.lean, runForkHidG2), from
the verdict on the file. It does for the layers what OnBytes/Tie/Pv/Att/HearCut.lean does for
attention.

Main names:
  `LayCut`: of one run of Layer.runForkHidG2: the two public tests at its start; the state F0 in
    which the sub-proof's slots are laid; the number of the reads' array; the success of Forest.pad
    from F0 and the context in which the link's routine began; the test on the lookup's numbers; the
    success of hearOwn from what Forest.pad has left; the success of rootInH behind it; F0 and the
    state behind Forest.pad have their arrays on slots at their length (`Sized`,
    OnBytes/Tie/Pv/Psc/Run/PscHide.lean).
  `layer_cut`: from a success of Layer.runForkHidG2 on a view: `LayCut`; the contexts between are
    views; and if the last context has no mark of a failed named test, they have none.
  `accepted_cutL`: from the verdict: if Proof.check accepts a file and the link at place j of the
    chain is the layers' link of a plan, then: the record of the whole first chain's run; the chain
    over the links before it; the link's step; the chain over the links behind it
    (OnBytes/Tie/Pv/Keeps/KeepsChain.lean); and inside the step `LayCut`, from the link's own first
    state, the plan's state of the link's record and the context in which the link's routine began;
    its contexts are views without a mark.

Limits: one direction: from the verdict. Premises: every link's routine keeps (`AllKeep`);
Forest.pad, where it succeeds, keeps `Sized`, which is proved nowhere here. The calls of
runForkHidG2 behind rootInH (the closing part, the list of claims, the counts) are not written out.
-/
import OnBytes.Tie.Pv.Keeps.KeepsChain
import OnBytes.Tie.Pv.Keeps.KeepsKinds
import OnBytes.Tie.Pv.Keeps.KeepsPeel
import OnBytes.Tie.Pv.Keeps.KeepsModel
import OnBytes.Tie.Pv.Psc.Run.PscHide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5.LayerCut
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Model.Road OnBytes.L5

/-- The cut of one run of Layer.runForkHidG2. L F c: where the run began. -/
structure LayCut (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) (L : LinkCtx) (F : Fork) (c : Ctx)
    (iU3 : Nat) (fo : Forest.Heard) (o : Layer.Own) (F0 F1 F2 F3 : Fork) (L3 : LinkCtx)
    (c1 c2 c3 : Ctx) : Prop where
  link : (L.link == if P.y.h.p4 = true then 2 * g else g) = true
  sizes : (L.list.nt == hp.Tp.nt &&
    (F.trees.map fun X => (X.R, X.K)) == hp.Fp.trees.map fun X => (X.R, X.K)) = true
  start : F0 = F.fillL.slots hp.ns
  reads : hp.tl.ix.U.getD 2 none = some iU3
  pad : Forest.pad P.y.cl P.y.fo.pub P.y.h.lidb F0 c = .ok ((fo, F1), c1)
  look : (fo.shape.dT == P.y.fo.dT && fo.shape.kT == P.y.fo.kT && fo.shape.NT == P.y.fo.NT &&
    fo.shape.rK == P.y.fo.rK && fo.shape.first == P.y.fo.first && fo.shape.iota == P.y.fo.iota &&
    fo.shape.callOf == P.y.fo.callOf) = true
  own : Layer.hearOwn P hp g fo F1 c1 = .ok ((o, F2), c2)
  root : rootInH [iU3] L F2 c2 = .ok ((((), L3), F3), c3)
  sized0 : Sized F0
  sized : Sized F1

set_option maxRecDepth 4000 in
theorem layer_cut
    (hpad : ∀ (calls : Array Model.Call) (pub : Array Nat) (lid : Nat) (F G : Fork) (c c' : Ctx)
      (g : Forest.Heard), Forest.pad calls pub lid F c = .ok ((g, G), c') → Sized F → Sized G)
    (P : Layer.Pub) (hp : Layer.HPlan2) (g : Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    {wo : WsForkOut} (hd : c.ch.dry = false)
    (h0 : Layer.runForkHidG2 P hp g L F c = .ok (((wo, L'), F'), c')) :
    ∃ iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3,
      LayCut P hp g L F c iU3 fo o F0 F1 F2 F3 L3 c1 c2 c3 ∧ wo = o.wo ∧
      c1.ch.dry = false ∧ c2.ch.dry = false ∧ c3.ch.dry = false ∧
      (c'.failed = none → c1.failed = none ∧ c2.failed = none ∧ c3.failed = none) := by
  have h : Runs (Layer.runForkHidG2 P hp g) (L, F, c) wo (L', F', c') := h0
  clear h0
  have d : View (m := LinkM) (L, F, c) := hd
  unfold Layer.runForkHidG2 at h
  peel3 h d
  all_goals
    obtain ⟨t1, e⟩ := runs_get r1
    cases e
    obtain ⟨t2, e⟩ := mustAs_L r2
    cases e
    obtain ⟨t3, e⟩ := fork_L r3
    cases e
    obtain ⟨t4, e⟩ := linkMust_L r4
    cases e
    down_sub r5
    down_sub r6
    down_sub r7
    dsimp only at t1 t3 r5 r6 r7
    have t1' := t1.symm
    subst t1'
    have t3' := t3.symm
    subst t3'
    obtain ⟨q1, q2⟩ := runs_change r5
    have q1' : F.fillL.slots hp.ns = F5 := Option.some.inj q1
    dsimp only at q2
    subst q2
    unfold Layer.form SubM.get at r6
    obtain ⟨k1, k2⟩ := runs_lift (σ := Fork) r6
    obtain ⟨k3, k4⟩ := runs_blkGet k1
    dsimp only at k2 k4
    subst k2
    subst k4
    obtain ⟨fo, ⟨G1, e1⟩, h1, h2⟩ := HasRuns.runs_bind (m := SubM) r7
    have v1 : View (m := SubM) (G1, e1) := runs_view h1 d6
    have m1 : Clean (m := SubM) (F7, c7) → Clean (m := SubM) (G1, e1) := runs_clean h2
    unfold Layer.hearLook at h1
    obtain ⟨fo', ⟨G0, e0⟩, p1, p2⟩ := HasRuns.runs_bind (m := SubM) h1
    obtain ⟨u, ⟨G2, e2⟩, p3, p4⟩ := HasRuns.runs_bind (m := SubM) p2
    obtain ⟨p5, p6⟩ := HasRuns.runs_pure p4
    obtain ⟨p7, p8⟩ := runs_up p3
    obtain ⟨pk, p9⟩ := runs_mustAs p7
    have eG : G1 = G0 := (congrArg Prod.fst p6).trans p8
    have eE : e1 = e0 := (congrArg Prod.snd p6).trans p9
    subst p5
    subst eG
    subst eE
    obtain ⟨w1, _⟩ := HasRuns.runs_pure h
    have z0 : Sized F6 := q1' ▸ sized_slots _ _
    exact ⟨a6, fo, a7, F6, G1, F7, F8, L8, e1, c7, c8,
      ⟨t2, t4, q1'.symm, k3, p1, pk, h2, r8, z0, hpad _ _ _ _ _ _ _ _ p1 z0⟩, w1, v1, d7, d8,
      fun k => ⟨m1 (b7 k), b7 k, b8 k⟩⟩

/-- From the verdict on a proof file: the cut at the borders of a layers' link's routines, in its
place in the file's own run. -/
theorem accepted_cutL
    (hpad : ∀ (calls : Array Model.Call) (pub : Array Nat) (lid : Nat) (F G : Fork) (c c' : Ctx)
      (g : Forest.Heard), Forest.pad calls pub lid F c = .ok ((g, G), c') → Sized F → Sized G)
    (Z : Array LinkH) (hk : AllKeep Z) {c : Params.ProofChains} {table : Params.TableName}
    {copy : Nat} {request words : ByteArray} {reply : E} {wsLay : WsLay} {file : ByteArray}
    (h : Proof.check c table copy request words reply (runLinksH Z c.first wsLay) file = .accepted)
    (j : Nat) (Y : LinkH) (hj : Z.toList[j]? = some Y) (X : Verify.Public) (tokv : Array Nat)
    (g : Nat) (hp : Layer.HPlan2) (hY : Y.run = (Verify.layersPlanOf X tokv g hp).run) :
    ∃ r fin cE check0 ca rN cb cc lin cd checkJ outJ cJ r1 cm chk o C' F' k1 k2 iU3 fo own F0 F1
      F2 F3 L3 c1 c2 c3,
      FileRan Z c table copy request words reply wsLay file r fin cE check0 ca rN cb cc lin cd ∧
      LinksChain Z c.first wsLay cE (Z.toList.take j) 0 check0 {} ca (checkJ, outJ) cJ ∧
      LinkStep Z c.first wsLay cE j Y checkJ outJ cJ r1 cm chk o C' F' k1 k2 ∧
      LinksChain Z c.first wsLay cE (Z.toList.drop (j + 1)) (j + 1) r1.1 r1.2 cm rN cb ∧
      LayCut { X.layers with tokv := tokv } hp g
        { check := chk, link := j, arrayOf := Y.arrayOf, list := Y.Tp } Y.Fp k1 iU3 fo own F0 F1 F2
        F3 L3 c1 c2 c3 ∧
      o = some own.wo ∧
      c1.ch.dry = false ∧ c2.ch.dry = false ∧ c3.ch.dry = false ∧
      c1.failed = none ∧ c2.failed = none ∧ c3.failed = none := by
  obtain ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, R⟩ := accepted_file Z hk h
  obtain ⟨checkJ, outJ, cJ, r1, cm, chk, o, C', F', k1, k2, A1, S, _, _, B⟩ :=
    LinksChain.split R.links j Y hj
  rw [Nat.zero_add] at S B
  have hr := S.run
  rw [hY] at hr
  obtain ⟨wo, hw, ho⟩ := layers_of_link hr
  obtain ⟨iU3, fo, own, F0, F1, F2, F3, L3, c1, c2, c3, a0, a1, a2, a3, a4, a5⟩ :=
    layer_cut hpad _ hp g S.v1 hw
  obtain ⟨m1, m2, m3⟩ := a5 (S.m2 R.noMark)
  exact ⟨r, fin, cE, check0, ca, rN, cb, cc, lin, cd, checkJ, outJ, cJ, r1, cm, chk, o, C', F', k1,
    k2, iU3, fo, own, F0, F1, F2, F3, L3, c1, c2, c3, R, A1, S, B, a0, by rw [ho, a1], a2, a3,
    a4, m1, m2, m3⟩

end OnBytes.L5.LayerCut

#print axioms OnBytes.L5.LayerCut.layer_cut
#print axioms OnBytes.L5.LayerCut.accepted_cutL
