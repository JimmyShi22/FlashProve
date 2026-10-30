-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearNorms.lean: the verifier's routine for the first messages of a layers'
sub-proof (hearNorms, OnBytes/Model/Layer.lean), taken apart into its calls where it succeeds, and
what its first calls have heard.

hearNorms draws three of its points only under a condition (two in the first group alone; the norms'
join unless there is a single norm). Here each such draw is one call (`firstPoint`, `joinPoint`),
and the routine is shown to be the same calls in a row (`hearNorms_eq`).

Main names:
  `firstPoint`, `joinPoint`: a point that is drawn under a condition; else the empty array.
  `normsCalls`, `hearNorms_eq`: the routine as calls in a row; it is hearNorms.
  `NormsRan`, `hearNorms_ran`: the calls' successes, in order, with the states and contexts between
    them, and the fields of what is returned.
  `firstPoint_heard`, `joinPoint_heard`: one stage, or none.
  `norms_heard`: from the token point to the product layer of the squares: the stages heard, in
    order, with the sizes and the layer's record; the three calls that follow (the products'
    scalars, their batching round, the first token sumcheck) stay as successes at named states.

Limits: those of OnBytes/Tie/Pv/Lay/HearL.lean. Of the test that all calls' points end alike (a test
on values) nothing is kept but that the step is idle.
-/
import OnBytes.Tie.Pv.Lay.HearL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open OnBytes.Psc (Weight hearMany hearOne)
open OnBytes.Tie.Pv.Att (PscH claimsIn_said)

/-- A point that only the first group draws. -/
def firstPoint (g n : Nat) : SubM (Array E) := if g == 0 then SubM.point .zero n else pure #[]

/-- The point of a join, unless it has no coordinate. -/
def joinPoint (n : Nat) : SubM (Array E) := if n != 0 then SubM.point .join n else pure #[]

/-- hearNorms as calls in a row. -/
def normsCalls (P : Pub) (g : Nat) (fo : Forest.Heard) : SubM Heard := do
  let y := P.y
  let h := y.h
  let xl := h.xl
  let s := fo.shape
  let PV ← SubM.point .zero h.lt
  let ZE ← firstPoint g (y.ls + h.lt)
  let tkh ← firstPoint g (y.lPd - y.ls)
  mustAs "forest-depth-G" (h.la ≤ s.dT)
  let Z ← form (lastOf fo.zx h.la).toOption
  let ends ← form (fo.zk.mapM fun zk => (lastOf zk h.la).toOption)
  Blk.check (ofGroup g "internal-g-merged-point") (ends.all (· == Z))
  let ztF ← form (lastOf fo.zx h.lt).toOption
  let sW ← SubM.claimsIn (ledNS xl * y.NI)
  let gp ← SubM.batch (ledNS xl)
  let rhoI ← joinPoint P.rd.lNI
  let wpl ← levelIn P.rd.muV (normsStart y sW gp rhoI PV).2 (normsStart y sW gp rhoI PV).1
    (orderDefault P.rd.muV)
  let sPv ← SubM.claimsIn (ledNP xl * y.NI)
  let omV ← SubM.batch (ledNP xl * y.NI)
  let tV ← tscIn PV h.lt (ledNO xl * y.NI) 2
  note "alpha" fo.alpha
  note "theta" fo.theta
  note "zx[0]" (fo.zx.getD 0 zeroE)
  note "P_V[0]" (PV.getD 0 zeroE)
  note "gam" (gp.getD 1 zeroE)
  note "wpl.r[0]" (wpl.r.getD 0 zeroE)
  note "omV[1]" (omV.getD 1 zeroE)
  note "tV.r[0]" (tV.r.getD 0 zeroE)
  pure { fo, PV, ZE, tkh, ztF, sW, gp, wpl, sPv, omV, tV }

theorem hearNorms_eq (P : Pub) (g : Nat) (fo : Forest.Heard) :
    hearNorms P g fo = normsCalls P g fo := by
  unfold hearNorms normsCalls firstPoint joinPoint
  by_cases hg : (g == 0) = true <;> by_cases hl : (P.rd.lNI != 0) = true <;>
    simp only [hg, hl, if_true, if_false, pure_bind, Bool.false_eq_true]

/-- The calls of hearNorms, in order. -/
structure NormsRan (P : Pub) (g : Nat) (fo : Forest.Heard) (H : Heard) (F G : Fork) (c c' : Ctx) :
    Prop where
  ran : ∃ (F1 F2 F3 F4 F5 F6 F7 F8 F9 : Fork) (c1 c2 c3 c3' c4 c5 c6 c7 c8 c9 c10 : Ctx)
      (rhoI : Array E),
    SubM.point .zero P.y.h.lt F c = .ok ((H.PV, F1), c1) ∧
    firstPoint g (P.y.ls + P.y.h.lt) F1 c1 = .ok ((H.ZE, F2), c2) ∧
    firstPoint g (P.y.lPd - P.y.ls) F2 c2 = .ok ((H.tkh, F3), c3) ∧
    Still c3 c3' ∧ (lastOf fo.zx P.y.h.lt).toOption = some H.ztF ∧
    SubM.claimsIn (ledNS P.y.h.xl * P.y.NI) F3 c3' = .ok ((H.sW, F4), c4) ∧
    SubM.batch (ledNS P.y.h.xl) F4 c4 = .ok ((H.gp, F5), c5) ∧
    joinPoint P.rd.lNI F5 c5 = .ok ((rhoI, F6), c6) ∧
    levelIn P.rd.muV (normsStart P.y H.sW H.gp rhoI H.PV).2 (normsStart P.y H.sW H.gp rhoI H.PV).1
      (orderDefault P.rd.muV) F6 c6 = .ok ((H.wpl, F7), c7) ∧
    SubM.claimsIn (ledNP P.y.h.xl * P.y.NI) F7 c7 = .ok ((H.sPv, F8), c8) ∧
    SubM.batch (ledNP P.y.h.xl * P.y.NI) F8 c8 = .ok ((H.omV, F9), c9) ∧
    tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F9 c9 = .ok ((H.tV, G), c10) ∧
    Still c10 c' ∧ H.fo = fo ∧ H.tT = none

theorem hearNorms_ran (P : Pub) (g : Nat) (fo : Forest.Heard) (H : Heard) (F G : Fork)
    (c c' : Ctx) (h : hearNorms P g fo F c = .ok ((H, G), c')) : NormsRan P g fo H F G c c' := by
  rw [hearNorms_eq] at h
  simp only [normsCalls] at h
  obtain ⟨PV, F1, c1, h1, k1⟩ := (bind_ok _ _ _ _ _).1 h
  obtain ⟨ZE, F2, c2, h2, k2⟩ := (bind_ok _ _ _ _ _).1 k1
  obtain ⟨tkh, F3, c3, h3, k3⟩ := (bind_ok _ _ _ _ _).1 k2
  obtain ⟨_, Fa, ca, ha, ka⟩ := (bind_ok _ _ _ _ _).1 k3
  obtain ⟨ma, ea⟩ := (lift_ok _ _ _ _ _ _).1 ha
  obtain ⟨_, ea'⟩ := (mustAs_ok _ _ _ _ _).1 ma
  obtain ⟨Z, Fb, cb, hb, kb⟩ := (bind_ok _ _ _ _ _).1 ka
  obtain ⟨_, eb, eb'⟩ := (getS_ok _ _ _ _ _ _).1 hb
  obtain ⟨ends, Fd, cd, hd, kd⟩ := (bind_ok _ _ _ _ _).1 kb
  obtain ⟨_, ed, ed'⟩ := (getS_ok _ _ _ _ _ _).1 hd
  obtain ⟨_, Fe, ce, he, ke⟩ := (bind_ok _ _ _ _ _).1 kd
  obtain ⟨ee, se⟩ := check_still _ _ _ _ _ _ _ he
  obtain ⟨ztF, Ff, cf, hf, kf⟩ := (bind_ok _ _ _ _ _).1 ke
  obtain ⟨zf, ef, ef'⟩ := (getS_ok _ _ _ _ _ _).1 hf
  have hF : Ff = F3 := by rw [ef, ee, ed, eb, ea]
  have hc : Still c3 cf := by
    rw [ef']
    rw [ed', eb', ea'] at se
    exact se
  rw [hF] at kf
  obtain ⟨sW, F4, c4, h4, k4⟩ := (bind_ok _ _ _ _ _).1 kf
  obtain ⟨gp, F5, c5, h5, k5⟩ := (bind_ok _ _ _ _ _).1 k4
  obtain ⟨rhoI, F6, c6, h6, k6⟩ := (bind_ok _ _ _ _ _).1 k5
  obtain ⟨wpl, F7, c7, h7, k7⟩ := (bind_ok _ _ _ _ _).1 k6
  obtain ⟨sPv, F8, c8, h8, k8⟩ := (bind_ok _ _ _ _ _).1 k7
  obtain ⟨omV, F9, c9, h9, k9⟩ := (bind_ok _ _ _ _ _).1 k8
  obtain ⟨tV, F10, c10, h10, k10⟩ := (bind_ok _ _ _ _ _).1 k9
  obtain ⟨_, N1, d1, n1, j1⟩ := (bind_ok _ _ _ _ _).1 k10
  obtain ⟨_, N2, d2, n2, j2⟩ := (bind_ok _ _ _ _ _).1 j1
  obtain ⟨_, N3, d3, n3, j3⟩ := (bind_ok _ _ _ _ _).1 j2
  obtain ⟨_, N4, d4, n4, j4⟩ := (bind_ok _ _ _ _ _).1 j3
  obtain ⟨_, N5, d5, n5, j5⟩ := (bind_ok _ _ _ _ _).1 j4
  obtain ⟨_, N6, d6, n6, j6⟩ := (bind_ok _ _ _ _ _).1 j5
  obtain ⟨_, N7, d7, n7, j7⟩ := (bind_ok _ _ _ _ _).1 j6
  obtain ⟨_, N8, d8, n8, j8⟩ := (bind_ok _ _ _ _ _).1 j7
  obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 j8
  obtain ⟨a1, s1⟩ := note_still _ _ _ _ _ _ _ n1
  obtain ⟨a2, s2⟩ := note_still _ _ _ _ _ _ _ n2
  obtain ⟨a3, s3⟩ := note_still _ _ _ _ _ _ _ n3
  obtain ⟨a4, s4⟩ := note_still _ _ _ _ _ _ _ n4
  obtain ⟨a5, s5⟩ := note_still _ _ _ _ _ _ _ n5
  obtain ⟨a6, s6⟩ := note_still _ _ _ _ _ _ _ n6
  obtain ⟨a7, s7⟩ := note_still _ _ _ _ _ _ _ n7
  obtain ⟨a8, s8⟩ := note_still _ _ _ _ _ _ _ n8
  have hG : G = F10 := by rw [e2, a8, a7, a6, a5, a4, a3, a2, a1]
  have hS : Still c10 c' := by
    rw [e3]
    exact ((((((s1.trans s2).trans s3).trans s4).trans s5).trans s6).trans s7).trans s8
  rw [e1, hG]
  exact ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, c1, c2, c3, cf, c4, c5, c6, c7, c8, c9, c10, rhoI,
    h1, h2, h3, hc, zf, h4, h5, h6, h7, h8, h9, h10, hS, rfl, rfl⟩

/-! ### What the first calls have heard -/

/-- The stages of a point that only the first group draws. -/
def firstStages (g : Nat) (d : Fmt.Drawn) : List StageL := if g == 0 then [.point .zero d] else []

theorem firstPoint_heard (g n : Nat) (F G : Fork) (c c' : Ctx) (pts : Array E)
    (h : firstPoint g n F c = .ok ((pts, G), c')) :
    G = F ∧ ∃ d : Fmt.Drawn, HeardL (firstStages g d) c c' ∧
      (pts = if g == 0 then (d.elems.map E.ofTriple).toArray else #[]) ∧
      ((g == 0) = true → d.elems.length = n) := by
  unfold firstPoint at h
  unfold firstStages
  by_cases hg : (g == 0) = true
  · simp only [hg, if_true] at h ⊢
    obtain ⟨a1, d, a2, a3, a4⟩ := pointR_ok _ _ _ _ _ _ _ h
    exact ⟨a1, d, a2, a3, fun _ => a4⟩
  · simp only [hg, if_false, Bool.false_eq_true] at h ⊢
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    exact ⟨e2, ⟨[], [], [], none⟩, e3, e1, fun x => x.elim⟩

/-- The stages of a join's point. -/
def joinStages (n : Nat) (d : Fmt.Drawn) : List StageL := if n != 0 then [.point .join d] else []

theorem joinPoint_heard (n : Nat) (F G : Fork) (c c' : Ctx) (pts : Array E)
    (h : joinPoint n F c = .ok ((pts, G), c')) :
    G = F ∧ ∃ d : Fmt.Drawn, HeardL (joinStages n d) c c' ∧
      (pts = if n != 0 then (d.elems.map E.ofTriple).toArray else #[]) ∧
      ((n != 0) = true → d.elems.length = n) := by
  unfold joinPoint at h
  unfold joinStages
  by_cases hn : (n != 0) = true
  · simp only [hn, if_true] at h ⊢
    obtain ⟨a1, d, a2, a3, a4⟩ := pointR_ok _ _ _ _ _ _ _ h
    exact ⟨a1, d, a2, a3, fun _ => a4⟩
  · simp only [hn, if_false, Bool.false_eq_true] at h ⊢
    obtain ⟨e1, e2, e3⟩ := (pure_ok _ _ _ _ _ _).1 h
    exact ⟨e2, ⟨[], [], [], none⟩, e3, e1, fun x => x.elim⟩

/-- From the token point to the product layer of the squares; the three calls that follow. -/
theorem norms_heard (P : Pub) (g : Nat) (fo : Forest.Heard) (H : Heard) (F G : Fork) (c c' : Ctx)
    (h : hearNorms P g fo F c = .ok ((H, G), c')) (hs : Sized F) :
    ∃ (dV dE dK dI : Fmt.Drawn) (vW : List E) (x : E) (H1 : PscH) (rhoI : Array E)
      (F4 F7 F8 F9 : Fork) (c7 c8 c9 c10 : Ctx),
      HeardL ([.point .zero dV] ++ firstStages g dE ++ firstStages g dK ++ [.idle] ++
        [.bat vW (ledNS P.y.h.xl) x] ++ joinStages P.rd.lNI dI ++
        [.sum [] (levelWeights P.rd.muV (normsStart P.y H.sW H.gp rhoI H.PV).2
          (orderDefault P.rd.muV)) 2 H1, .line H.wpl.tau]) c c7 ∧
      (dV.elems.length = P.y.h.lt ∧ ((g == 0) = true → dE.elems.length = P.y.ls + P.y.h.lt) ∧
        ((g == 0) = true → dK.elems.length = P.y.lPd - P.y.ls) ∧
        ((P.rd.lNI != 0) = true → dI.elems.length = P.rd.lNI)) ∧
      H.PV = (dV.elems.map E.ofTriple).toArray ∧
      H.ZE = (if g == 0 then (dE.elems.map E.ofTriple).toArray else #[]) ∧
      H.tkh = (if g == 0 then (dK.elems.map E.ofTriple).toArray else #[]) ∧
      (lastOf fo.zx P.y.h.lt).toOption = some H.ztF ∧
      vW.length = ledNS P.y.h.xl * P.y.NI ∧ H.sW = F.next ∧
      Filled (taken F (ledNS P.y.h.xl * P.y.NI)) F4 F.next vW oneE ∧
      H.gp = powers x (ledNS P.y.h.xl) ∧
      rhoI = (if P.rd.lNI != 0 then (dI.elems.map E.ofTriple).toArray else #[]) ∧
      LevelSaid P.rd.muV (normsStart P.y H.sW H.gp rhoI H.PV).2
        (normsStart P.y H.sW H.gp rhoI H.PV).1 (orderDefault P.rd.muV) F4 F7 H.wpl H1 ∧
      SubM.claimsIn (ledNP P.y.h.xl * P.y.NI) F7 c7 = .ok ((H.sPv, F8), c8) ∧
      SubM.batch (ledNP P.y.h.xl * P.y.NI) F8 c8 = .ok ((H.omV, F9), c9) ∧
      tscIn H.PV P.y.h.lt (ledNO P.y.h.xl * P.y.NI) 2 F9 c9 = .ok ((H.tV, G), c10) ∧
      Still c10 c' ∧ H.fo = fo ∧ H.tT = none := by
  obtain ⟨F1, F2, F3, F4, F5, F6, F7, F8, F9, c1, c2, c3, c3', c4, c5, c6, c7, c8, c9, c10, rhoI,
    h1, h2, h3, s3, z3, h4, h5, h6, h7, h8, h9, h10, s10, e1, e2⟩ :=
    (hearNorms_ran P g fo H F G c c' h).ran
  obtain ⟨a1, dV, p1, r1, n1⟩ := pointR_ok _ _ _ _ _ _ _ h1
  obtain ⟨a2, dE, p2, r2, n2⟩ := firstPoint_heard _ _ _ _ _ _ _ h2
  obtain ⟨a3, dK, p3, r3, n3⟩ := firstPoint_heard _ _ _ _ _ _ _ h3
  have hF3 : F3 = F := by rw [a3, a2, a1]
  rw [hF3] at h4
  obtain ⟨vW, b1, b2, b3, b4, b5⟩ := claimsIn_said _ F F4 c3' c4 _ h4 hs
  rw [← b2] at b1
  obtain ⟨a5, x, p5, r5⟩ := batch_heardL _ _ _ _ _ _ h5 vW c3' b1
  obtain ⟨a6, dI, p6, r6, n6⟩ := joinPoint_heard _ _ _ _ _ _ h6
  have hF6 : F6 = F4 := by rw [a6, a5]
  rw [hF6] at h7
  obtain ⟨H1, p7, q7⟩ := level_heard _ _ _ _ F4 F7 c6 c7 _ h7 b5
  refine ⟨dV, dE, dK, dI, vW, x, H1, rhoI, F4, F7, F8, F9, c7, c8, c9, c10, ?_, ⟨n1, n2, n3, n6⟩,
      r1, r2, r3, z3,
    b2,
    b3, b4, r5, r6, q7, h8, h9, h10, s10, e1, e2⟩
  exact HeardL.append _ _ c c6 c7 (HeardL.append _ _ c c5 c6 (HeardL.append _ _ c c3' c5
    (HeardL.append _ _ c c3 c3' (HeardL.append _ _ c c2 c3 (HeardL.append _ _ c c1 c2 p1 p2) p3)
      s3.heard) p5) p6) p7

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.hearNorms_eq
#print axioms OnBytes.Tie.Pv.Lay.hearNorms_ran
#print axioms OnBytes.Tie.Pv.Lay.norms_heard
