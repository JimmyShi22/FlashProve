-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReturnsAt.lean: the gathering returns (Returns, Att/K05GatheredZero.lean)
at every hearing that Said speaks of, at key points that
follow the lookup's own rule, where the claims' dry run on the plan alone says yes (claimsOk,
Att/ClaimsOk.lean).

Main names:
  `joinF_ret`: the lookup's joinF (Johnson/Desc/First/Look/LookClaims.lean) returns where the two
    lengths fit.
  `heard_lens`: HeardLens (Claims/SameHeard.lean), and the numbers of challenges of "division" and
    "key", from Said.
  `returns_at`: there are l, i, l₁, l₂, jn, kf, xj, lk with Returns.

Used: chal_len (Att/K05HeardFive.lean); leftIs_ret, points_at (Att/K05ReturnsLeft.lean);
mergedPlanes_at, mergedTokens_at (Att/K05MergedAt.lean);
dry_gives (Claims/Returns.lean); same_pts, same_of_heard, lensOne_of (Claims/SameHeard.lean);
tablesP_of_lens (Claims/ReadsSame.lean); points_lens
(Claims/ReadsLens.lean).
Premises of returns_at: the return of shapeHid; PlanLaw; UnitsAll; MatsFit; a yes of claimsOk with
planesOk := true; K3Pts at four key points; lmS is at
most a plane family's bits; P.D = dimOf S; two plane messages; Said; the ledger is Sized; a plan
record with as many calls as the shape; a heard
record of the lookup with these key points, four calls and four values e.
Limits. The record lk that is taken has the point zx, planesOk := true and three empty weight
vectors: Returns and GatheredAllJ read of lk the point
alone. The yes of claimsOk is a premise: it is evaluated in no file of this library.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MergedAt
import Johnson.Desc.First.Att.K05HeardFive
import Johnson.Desc.First.Att.K05GatheredZero
import Johnson.Desc.First.Att.Claims.ReadsSame
import Johnson.Desc.First.Att.Claims.ReadsLens
import Johnson.Desc.First.Att.Claims.SameHeard
import Johnson.Desc.First.Att.Claims.Returns
import Johnson.Road.Lane5KvAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes.Tie.Pv.Att (PscH recOf)
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PlanLaw)

/-- The lookup's joinF returns where the two lengths fit. -/
theorem joinF_ret {g : Forest.Heard} {KF : Array Aff} (h1 : KF.size = g.shape.calls.size)
    (h2 : g.e.size = g.shape.calls.size) (F : Fork) (t : OnBytes.K.Kc.Tape) :
    ∃ x, VerifiableInference.Desc.First.Look.joinF g KF F t = some x := by
  cases hx : VerifiableInference.Desc.First.Look.joinF g KF F t with
  | some x => exact ⟨x, rfl⟩
  | none =>
    exfalso
    unfold VerifiableInference.Desc.First.Look.joinF at hx
    simp [bind, OnBytes.K.Kc.Fl.andThen, OnBytes.K.Kc.Fl.must, VerifiableInference.Desc.First.Look.joinAddedF,
      VerifiableInference.Desc.First.Look.paidF, OnBytes.K.Kc.Fl.change, pure, OnBytes.K.Kc.Fl.ret, h1, h2] at hx

section At
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {lid : ℕ} {cf : Attention.Cfg} {r1 r2 u1 u2 wl ix wh : UnitG}
variable {K M X : Type} [Field K] [Fintype K]

/-- **What was heard has the place's lengths.** -/
theorem heard_lens (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) {c0 c1 c2 c3 : Attention.ACall}
    (Pl : K5Law.PlaceIs S c0 c1 c2 c3) (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (N : OnBytes.Road.L5.Norm S)
    (hl : 1 ≤ S.lnT) {zk : Array (Array E)} (hz4 : zk.size = 4)
    (Kz : ∀ q : Fin 4, (zk.getD q.1 #[]).size = (callsOf fs).a q) (P : OwnPar K M X) (hD : P.D = dimOf S) (rows : ℕ)
    {h : Heard} {G : Fork} {L : Lists} (b2 : Said (recOf P rows) h G L) :
    K5Law.HeardLens (geoOf S) zk h ∧ (chal h.division).size = S.cf.lgk + S.cf.lt ∧
      (chal h.key).size = 2 * S.cf.lt + S.cf.lgk := by
  obtain ⟨o1, o2, _, _, _, _, hos, _, ⟨_, _, a1, _⟩, ⟨_, _, a2, _⟩⟩ := units_two b2.units
  have hlt := N.lt
  have n4 : S.calls.size = 4 := by rw [← Array.length_toList, Pl.calls]; rfl
  have k1 := chal_len a1
  have k2 := chal_len a2
  have kE := chal_len b2.sE
  have kM := chal_len b2.sM
  have kO := chal_len b2.sVD
  have kF := chal_len b2.sF
  have kK := chal_len b2.sD
  rw [List.length_replicate] at k1 k2 kE kM kO kF
  simp only [List.length_map, List.length_append, List.length_replicate] at kK
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · show zk.size = (S.calls.map callOf).size
    rw [Array.size_map, n4, hz4]
  · intro q c hc
    have hc' : (S.calls.map callOf)[q]? = some c := hc
    rw [Array.getElem?_map] at hc'
    obtain ⟨a, ha, hca⟩ := Option.map_eq_some_iff.1 hc'
    have hq : q < 4 := by
      rcases Nat.lt_or_ge q 4 with h' | h'
      · exact h'
      · rw [Array.getElem?_eq_none (by rw [n4]; exact h')] at ha; cases ha
    rw [Kz ⟨q, hq⟩]
    show ((fs.calls[q]?).map fun k => k.n).getD 0 = c.n
    rw [OnBytes.Road.L5.calls_of_hid hid, Array.getElem?_map, ha, ← hca]
    rfl
  · intro n u o hu ho
    rw [U.sco] at hu
    rw [← Array.getElem?_toList, hos] at ho
    rcases n with _ | _ | n
    · simp only [List.getElem?_cons_zero, Option.some.injEq] at hu ho
      subst hu ho
      rw [U.below, if_pos rfl, k1]
      show AttSeg.Step.s6b.g P.D = _
      rw [hD]
      show S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.ldh = S.cf.lgk + 2 * S.lnT - 1 + S.cf.ldh
      omega
    · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hu ho
      subst hu ho
      rw [U.on, k2]
      show AttSeg.Step.s6d.g P.D = _
      rw [hD]
      show S.cf.lgk + (S.lnT - 1 + 1) + S.cf.ldh = S.cf.lgk + S.lnT + S.cf.ldh
      omega
    · simp at hu
  · rw [kF]
    show AttSeg.Step.s16.g P.D = _
    rw [hD]
    show (S.lnT - 1 + 1 + S.cf.lB) + S.cf.lgk + S.cf.ldh = S.cf.lt + S.cf.lgk + S.cf.ldh
    omega
  · rw [kM]
    show AttSeg.Step.s11.g P.D = _
    rw [hD]
    show S.cf.lgk + (S.lnT - 1) + (S.lnT - 1 + 1) + S.cf.lB = S.cf.lgk + 2 * S.lnT - 1 + S.cf.lB
    omega
  · rw [kO]
    show AttSeg.Step.s12.g P.D = _
    rw [hD]
    show S.cf.lgk + (S.lnT - 1 + 1) + S.cf.lB = S.cf.lgk + S.lnT + S.cf.lB
    omega
  · rw [kE]
    show AttSeg.Step.s8.g P.D = _
    rw [hD]
    show S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) = S.cf.lgk + S.cf.lt
    omega
  · rw [kK]
    show P.D.lT + P.D.lg + P.D.lT = _
    rw [hD]
    show (S.lnT - 1 + 1 + S.cf.lB) + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) = 2 * S.cf.lt + S.cf.lgk
    omega

/-- **The gathering returns.** -/
theorem returns_at (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (tl : HTailF2) (hmf : OnBytes.Road.Rows.MatsFit S tl) (iU3 nW : ℕ) {Kc : ℕ}
    {k3 : Runs.PadIn} {nzx : ℕ} (hd : claimsOk ⟨geoOf S, iU3, nW, K5Law.matsOf tl.mats⟩ Kc k3 true nzx = true)
    {zx zy : Array E} {zk : Array (Array E)} {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z) (hz4 : zk.size = 4)
    (hlm : ∀ f : Fam, Cb.Pv.Att.End.IsPlane f → S.cf.lmS ≤ f.l (dimOf S))
    (P : OwnPar K M X) (hD : P.D = dimOf S) (hn : P.npl = 2) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (b2 : Said (recOf P rows) h G L) (b3 : Sized G) (A : Attention.Plan) (hN : A.NC = S.calls.size)
    (hu : iU3 = A.iU3)
    (gL : Forest.Heard) (hzk : gL.zk = zk) (hsh : gL.shape.calls.size = 4) (he : gL.e.size = 4) (Fj : Fork)
    (tj : OnBytes.K.Kc.Tape) :
    ∃ l i l₁ l₂ jn kf xj lk, Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk := by
  have Nn := OnBytes.Road.Rows.norm_of_hid hid
  have Zs := OnBytes.Road.Rows.sizes_of_hid hid
  have hl : 1 ≤ S.lnT := Nat.le_of_succ_le Zs.lnT
  have Kz := (keyPts_of_k3 PL.fit H3).size
  obtain ⟨l, li⟩ := leftIs_ret U Nn hl Kz P hD rows b2 b3
  obtain ⟨p, hp⟩ := points_at U Nn hl Kz PL.place P hn rows b2 li
  obtain ⟨HL, cE, cK⟩ := heard_lens hid PL.place U Nn hl hz4 Kz P hD rows b2
  obtain ⟨p0, t0, hp0, ht0, All⟩ := K5Law.dry_gives _ Kc k3 true nzx hd
  have Z1 := K5Law.lensOne_of HL
  have Sp := K5Law.same_pts hp hp0 Z1
  have PA := K5Law.points_are hp
  have PA0 := K5Law.points_are hp0
  obtain ⟨w1, _, w3, _⟩ := K5Law.points_lens hp
  obtain ⟨v1, _, v3, _⟩ := K5Law.points_lens hp0
  have LL : K5Law.LongLens p p0 := by
    refine ⟨by simpa using Sp.scores.length_eq, fun u => ?_, w1.trans v1.symm, w3.trans v3.symm, ?_, Sp.rF, ?_⟩
    · have e := K5Law.forall₂_getElem? Sp.scores u
      unfold Pts.unit
      rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, ← Array.getElem?_toList]
      cases e1 : p.scores.toList[u]? <;> cases e2 : p0.scores.toList[u]? <;> rw [e1, e2] at e
      · exact e.elim
      · exact e.elim
      · exact e.r
    · rw [PA.scE, PA0.scE]
      show (chal h.division).size = (chal (blankSum _)).size
      rw [cE, K5Law.chal_blank]
      rfl
    · rw [PA.scd, PA0.scd]
      show (chal h.key).size = (chal (blankSum _)).size
      rw [cK, K5Law.chal_blank]
      rfl
  obtain ⟨_, _, _, _, _, _, ⟨_, fD, fW, _, _⟩, _⟩ := PL.fit
  have hx1 : S.cf.lmS ≤ zx.size := by
    rw [H3.nx]
    exact le_trans (hlm .d1 trivial) fD
  have hx2 : S.cf.lt + S.cf.ldh ≤ zx.size := by
    rw [H3.nx]
    refine le_trans ?_ fW
    show _ ≤ 1 + S.cf.lgk + (S.lnT - 1 + 1 + S.cf.lB) + S.cf.ldh
    have := Nn.lt
    omega
  obtain ⟨t, ht⟩ := K5Law.tablesP_of_lens (lk := ⟨zx, true, #[], #[], #[]⟩) LL ht0 rfl
    (mergedPlanes_at U H3 Kz hlm hx1 hp) (mergedTokens_at U Nn hl H3 Kz hx2 hp)
  have Sm : K5Law.Same (⟨geoOf S, p, t, zk, iU3⟩ : Runs.In) _ :=
    K5Law.same_of_heard (c := ⟨geoOf S, iU3, nW, K5Law.matsOf tl.mats⟩) (i := ⟨geoOf S, p, t, zk, iU3⟩) rfl hp ht hp0 ht0 Z1
  obtain ⟨l₁, jn, kf, l₂, h1, hk, h2⟩ := All _ Sm
  have hkr : (geoOf S).units .kr [.rm, .rd] = _ := K5Law.place_kr PL.place
  obtain ⟨a1, a2, k1, k2, ea1, ea2, ek1, ek2, _⟩ := K5Law.sayAt_back (ρ := Reading.gl) (W := G.worldOf Reading.gl (fun _ => 0) fun _ _ _ => 0)
    (i := ⟨geoOf S, p, t, zk, iU3⟩) (gL := gL) A rfl hzk.symm hN hp h1 h2 Zs.G hkr (K5Law.place_scores PL.place)
  have ej := (K5Law.first_any A S gL ⟨geoOf S, p, t, zk, iU3⟩ Kc l₁ jn rfl hzk.symm hN h1).2
  have ek : kf = (K5Law.joinsT (oldOf S gL ⟨geoOf S, p, t, zk, iU3⟩)).kf := by
    rw [K5Law.keys_is _ _ _ _ hk, ej, ← K5Law.joinsT_att A _ hN]
    rfl
  have z4 := (K5Law.keys_port (K5Law.callsAre_of (gL := gL) (i := ⟨geoOf S, p, t, zk, iU3⟩) PL.place rfl hp ea1 ea2 ek1 ek2)
    default default).1
  obtain ⟨xj, hx⟩ := joinF_ret (g := gL) (KF := kf) (by rw [ek, z4, hsh]) (by rw [he, hsh]) Fj tj
  exact ⟨l, ⟨geoOf S, p, t, zk, iU3⟩, l₁, l₂, jn, kf, xj, ⟨zx, true, #[], #[], #[]⟩,
    ⟨li, rfl, hzk.symm, hzk, hN, hp, h1, h2, hk, hx, ht, rfl, hmf, hu⟩⟩

end At

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.heard_lens
#print axioms VerifiableInference.Desc.First.Att.P.returns_at
