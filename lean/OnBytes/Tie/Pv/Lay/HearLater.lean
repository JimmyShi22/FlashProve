-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/HearLater.lean: the bridge from what the routines for a layers' sub-proof heard
to the chain's own run, as far as it stands; what is left of it, by name.

OnBytes/Tie/Pv/Lay/HearCanon.lean brings the letters' claims down to five equations of targets,
and HearShown.lean shows one. Here the port's side of one more is shown, the rest is gathered in
two named premises, and the whole is stated from the success of hearOwn
(OnBytes/Model/Layer.lean).

Main names:
  `taken_kept`, `LevelSaid.kept`: what lies under a slot stays through a product layer's routine
    (`Lies`, `Kept`, OnBytes/Tie/Pv/Att/HearSaid.lean).
  `routedStart_eq`: the start form of the routed experts' layer is a weighted sum of slots.
  `RoutedTg`, `own_recs4`: the records of HearShown.lean (`own_recs3`) with one target more: that
    of the routed experts' sumcheck reads as the sum, over the experts' places, of the equality
    table of the join's point times the end values of the batched sumcheck from the third on.
  `XIs`: what of the bridge reads the first statement: the batched sumcheck's target, and the fit
    of the weights at the three sumchecks whose points hold coordinates of the lookup's end point.
  `OwnIs`: what else is not shown yet: three targets (the sums of squares, the routed experts'
    products, the merge) and the fit of the weights at the four other sumchecks.
  `hear_bridge`: from hearOwn's success and `NzCtx` at its start, at all records `LayV` and the
    data `tailC`: under `XIs`, `OwnIs` and the two premises of `t5_of`: `TailH.Claims`, and all
    seven `OutIs`.

Limits: `XIs` and `OwnIs` are premises, shown of no value here. `XIs` is meant to be paid where
the lookup's last statement is tied to what its routine returned; nothing here says that it can be
met. `RoutedTg` is the port's side alone: that a record's target at a value is that sum, read, is
the field t6 of `OwnIs`. `hear_bridge` is stated for a sub-proof that is not the first (`LayV`);
for the first (`LayVF`) `layVF_claims` stands and the like theorem is not written. The limits of
HearAll.lean, HearTieAll.lean and HearCanon.lean hold here too.
-/
import OnBytes.Tie.Pv.Lay.HearShown
import OnBytes.Tie.Pv.Att.HearSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay OnBytes.Tie.Pv.Lay.Eng
open OnBytes.Psc (Weight hearMany hearOne hidingEntries)
open OnBytes.Tie.Pv.Att (PscH Lies Kept filled_kept filled_lies sum_read SumRead)

/-! ### What lies under the batched sumcheck's end slots stays -/

theorem taken_kept (F : Fork) (n : Nat) : Kept F (taken F n) := fun _ _ h => h

/-- A product layer's routine keeps what lies under the slots. -/
theorem LevelSaid.kept {mu : Nat} {rho : Array E} {C : Aff} {order : List Nat} {F G : Fork}
    {o : Level} {H : PscH} (s : LevelSaid mu rho C order F G o H) : Kept F G := by
  obtain ⟨F1, n, f1, f2⟩ := s.ends
  exact ((taken_kept F _).trans (filled_kept f1)).trans (filled_kept f2)

/-- The start form of the routed experts' layer is a weighted sum of slots. -/
theorem routedStart_eq (y : Lay) (sH1 : Nat) (rhoM : Array E) :
    routedStart y sH1 rhoM =
      Attention.weightedSum y.LamM (eqTab rhoM) fun lm => Aff.slot (sH1 + 1 + lm) := rfl

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The target of the routed experts' sumcheck reads as the sum, over the experts' places, of the
equality table of the join's point times the end values of the batched sumcheck from the third
on. -/
structure RoutedTg (P : Pub) (D : OwnH) (p6 : Psc) : Prop where
  t6 : ρ.val p6.target = ∑ b : Fin P.y.LamM,
    ρ.val ((eqTab (D.dM.elems.map E.ofTriple).toArray).getD b.1 zeroE) *
      ρ.val (D.H4.v.getD (2 + b.1) zeroE)

omit [Fintype K] in
/-- `own_recs3` (OnBytes/Tie/Pv/Lay/HearShown.lean) with that target. -/
theorem own_recs4 {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {O : Own} {F G : Fork}
    {D : OwnH} {H0 : Heard} {tT : Tsc} {hd2 : Level} {claims : Array WsClaim}
    (hp3 : P.y.h.p3 = true) (s : OwnSaidL P hp g fo O F G D H0 tT hd2 claims) :
    ∃ p1 p3 p4 p5 p6 : Psc, Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 ∧ TokTg ρ D H0 p3 ∧
      GatedTg ρ D p5 ∧ RoutedTg ρ P D p6 := by
  obtain ⟨F4, F7, F8, F1, F1', F2, F3, F3', F5, F6, t3, C, p4, c1, c5, _, a2, _, _, a5, a6, a7, a8,
    _, _, a11, a12, a13, fn, a14, _, _, a17⟩ := s.recs
  obtain ⟨p1, b1, b2⟩ := a2.recAt
  obtain ⟨tT', Fm, e1, g5, g6⟩ := a14.said
  have et : tT' = tT := Option.some.inj (e1.symm.trans s.hasT)
  rw [et] at g6
  obtain ⟨τ5, p5, q1, q2, q3⟩ := g5.psc
  have b5 : RecAt D.H5 (levelWeights P.rd.muH (downFrom O.K.rs O.K.fin.wD ++ O.H.ztF)
      (orderRange P.rd.muH)) P.rd.muH 2 2 p5 := by
    refine ⟨⟨_, τ5, _, q2⟩, ?_, g5.sentY, g5.vals⟩
    refine List.eq_replicate_iff.2 ⟨by rw [List.length_map, g5.rounds], fun b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact g5.two x hx
  obtain ⟨τ6, p6, r1, r2, r3⟩ := g6.psc
  have b6 : RecAt D.H6 (levelWeights P.rd.muH2
      ((D.dM.elems.map E.ofTriple).toArray ++ downFrom O.K.rs P.y.lfe ++ tT.r)
      (orderRange P.rd.muH2)) P.rd.muH2 2 2 p6 := by
    refine ⟨⟨_, τ6, _, r2⟩, ?_, g6.sentY, g6.vals⟩
    refine List.eq_replicate_iff.2 ⟨by rw [List.length_map, g6.rounds], fun b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    exact g6.two x hx
  have sh := stack_shown a11 a12 a13 1 (by omega)
  rw [← fn.sH1] at sh
  have e5 := publicPart_slot_word F3 O.K.sH1 _ τ5 sh q1
  have hl : ∀ b, b < P.y.LamM → Lies Fm (O.K.sH1 + 1 + b) (D.H4.v.getD (2 + b) zeroE) := by
    intro b hb
    have h0 := filled_lies a12 (2 + b) (by
      rw [a11.vals]
      simp only [hp3, if_true]
      omega)
    rw [show O.K.sA0 + (2 + b) = O.K.sH1 + 1 + b by rw [fn.sH1]; omega] at h0
    exact g5.kept _ _ (filled_kept a13 _ _ h0)
  rw [routedStart_eq] at r1
  refine ⟨p1, t3.p, p4, p5, p6, ⟨b1, b2, a5.recAt, a6.recAt, by rw [a7], by rw [a8], a11.recAt,
    a11.row, b5, q3, b6, r3, a17.recAt⟩, ⟨a5.target ρ, a6.target ρ⟩, ⟨?_⟩, ⟨?_⟩⟩
  · rw [q2.target, e5, ρ.add, ρ.mul, ρ.zero, ρ.one, zero_add, one_mul]
  · rw [r2.target]
    exact sum_read hl r1 K ρ

/-! ### What is left, by name -/

/-- What of the bridge reads the first statement x: the batched sumcheck's target, and the fit of
the weights at the three sumchecks whose points hold coordinates of the lookup's end point. It is
meant to say that x is the reading of what the lookup's routine returned. -/
structure XIs {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (x : X) (P : Pub) (hp : HPlan2)
    (O : Own) (D : OwnH) (H0 : Heard) (tT : Tsc) : Prop where
  t4 : (T.s4.cl (Dt.y4 x) Dt.d4.rd).1 = ρ.val Dt.d4.t
  f3 : StgFits ρ T.s3 Dt.d3.st (tokenWeights H0.ztF P.y.h.lt) P.y.h.lt 1
  f5 : StgFits ρ T.s5 Dt.d5.st (levelWeights P.rd.muH
    (downFrom O.K.rs O.K.fin.wD ++ O.H.ztF) (orderRange P.rd.muH)) P.rd.muH 2
  f6 : StgFits ρ T.s6 Dt.d6.st (levelWeights P.rd.muH2
    ((D.dM.elems.map E.ofTriple).toArray ++ downFrom O.K.rs P.y.lfe ++ tT.r)
    (orderRange P.rd.muH2)) P.rd.muH2 2

/-- What of the bridge does not read x beyond the rounds' own messages and is not shown yet: three
targets, and the fit of the weights at the four other sumchecks. -/
structure OwnIs {M X : Type} {T : LayTail K M X} (Dt : TailH ρ T) (x : X) (P : Pub) (hp : HPlan2)
    (D : OwnH) (H0 : Heard) : Prop where
  t1 : (T.s1.cl (Dt.y1 x) Dt.d1.rd).1 = ρ.val Dt.d1.t
  t6 : (T.s6.cl (Dt.y6 x) Dt.d6.rd).1 = ρ.val Dt.d6.t
  t7 : (T.s7.cl (Dt.y7 x) Dt.d7.rd).1 = ρ.val Dt.d7.t
  f1 : StgFits ρ T.s1 Dt.d1.st (levelWeights P.rd.muV
    (normsStart P.y H0.sW H0.gp (D.rhoI P) H0.PV).2 (orderDefault P.rd.muV)) P.rd.muV 2
  f2 : StgFits ρ T.s2 Dt.d2.st (tokenWeights H0.PV P.y.h.lt) P.y.h.lt 2
  f4 : StgFits ρ T.s4 Dt.d4.st (List.replicate hp.lamS (Weight.plain 3)) hp.lamS 2
  f7 : StgFits ρ T.s7 Dt.d7.st (List.replicate P.wsLay.lk (Weight.plain 3)) P.wsLay.lk 1

/-- The bridge, as far as it stands: from the success of hearOwn, at the records of
Cb/Pv/Lay/OwnAll.lean and the data that the chain itself names: under `XIs`, `OwnIs` and the two
premises of `t5_of`, the letters' claims hold and all seven typed outputs are the records, read. -/
theorem hear_bridge (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) (O : Own) (F G : Fork)
    (c c' : Ctx) (h : hearOwn P hp g fo F c = .ok ((O, G), c')) (hs : Sized F)
    (hne : P.rd.tscCalls.isEmpty = false) (hp3 : P.y.h.p3 = true) (hl : P.y.h.ll > 1)
    (hc : NzCtx ρ c) :
    ∃ (D : OwnH) (H0 : Heard) (tT : Tsc) (hd2 : Level) (claims : Array WsClaim)
      (p1 p3 p4 p5 p6 : Psc) (nz : Nz7 ρ D),
      HeardL (D.stages P hp g H0 O tT hd2 (claimSlots g (nclp hp g) O.K.sV O.sVE).size) c c' ∧
      OwnSaidL P hp g fo O F G D H0 tT hd2 claims ∧ NzCtx ρ c' ∧
      Recs7 P hp g O D H0 tT hd2 p1 p3 p4 p5 p6 ∧ RoutedTg ρ P D p6 ∧
      ∀ {M X : Type} (V : LayV K M X) (N : Shs V.toTail) (x : X) (a₀ : V.toTail.s4.L.S.A),
        (∀ z r, (V.toTail.s5.cl z r).1 = z.2.vals a₀) →
        (∀ l, valsOf ρ N.n4 l a₀ = ρ.val (l.getD 1 zeroE)) →
        XIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) x P hp O D H0 tT →
        OwnIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) x P hp D H0 →
        (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).Claims x ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d1 p1 ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d2 H0.tV.p ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d3 p3 ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d4 p4 ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d5 p5 ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d6 p6 ∧
        OutIs ρ (tailC ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x).d7 O.wo.p := by
  obtain ⟨D, H0, tT, hd2, claims, a1, a2⟩ := own_heardL P hp g fo O F G c c' h hs hne hp3 hl
  obtain ⟨n1, n2⟩ := heardL_nz ρ _ c c' hc a1
  have nz := own_betas ρ D _ _ _ _ _ _ _ _ n2
  obtain ⟨p1, p3, p4, p5, p6, r, tt, gt, rt⟩ := own_recs4 ρ hp3 a2
  refine ⟨D, H0, tT, hd2, claims, p1, p3, p4, p5, p6, nz, a1, a2, n1, r, rt,
    fun V N x a₀ hcl hN xi oi => ⟨?_, ?_⟩⟩
  · exact layV_claims ρ V D nz H0 O hd2 p1 p3 p4 p5 p6 N x tt
      ⟨oi.t1, xi.t4, t5_of ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x a₀ hcl hN gt, oi.t6, oi.t7⟩
  · exact tail_outs ρ _ (tailC_of ρ D nz H0 O hd2 p1 p3 p4 p5 p6 N x) r oi.f1 oi.f2 xi.f3 oi.f4
      xi.f5 xi.f6 oi.f7

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.own_recs4
#print axioms OnBytes.Tie.Pv.Lay.hear_bridge
