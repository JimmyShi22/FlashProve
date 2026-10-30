-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05ReturnsLk.lean: returns_at (Att/K05ReturnsAt.lean) with the lookup's
record lk a letter: the gathering returns at every lk whose point is zx and whose
planesOk says yes; its three weight vectors are free.

Main names: `returns_at_lk`.

Premises: those of returns_at; lk.zx = zx; lk.planesOk = true. The proof is that of returns_at, line
for line, with lk in the place of the record that is
made there.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReturnsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model Inst.Model.AttSeg
open OnBytes.Tie.Pv.Att (PscH recOf)
open OnBytes.Road.L5 (dimOf callsOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PlanLaw)

section At
variable {S : Attention.Shape} {fs : Model.Forest.Shape} {lid : ℕ} {cf : Attention.Cfg} {r1 r2 u1 u2 wl ix wh : UnitG}
variable {K M X : Type} [Field K] [Fintype K]

/-- **The gathering returns, at every record of the lookup's with the point zx and planesOk.** -/
theorem returns_at_lk (hid : Attention.shapeHid lid cf = Except.ok (S, fs)) (PL : PlanLaw cf S fs)
    (U : UnitsAll S fs r1 r2 u1 u2 wl ix wh) (tl : HTailF2) (hmf : OnBytes.Road.Rows.MatsFit S tl) (iU3 nW : ℕ) {Kc : ℕ}
    {k3 : Runs.PadIn} {nzx : ℕ} (hd : claimsOk ⟨geoOf S, iU3, nW, K5Law.matsOf tl.mats⟩ Kc k3 true nzx = true)
    {zx zy : Array E} {zk : Array (Array E)} {z : ℕ → Cb.Gl.E} (H3 : K3Pts fs zx zy zk z) (hz4 : zk.size = 4)
    (hlm : ∀ f : Fam, Cb.Pv.Att.End.IsPlane f → S.cf.lmS ≤ f.l (dimOf S))
    (P : OwnPar K M X) (hD : P.D = dimOf S) (hn : P.npl = 2) (rows : ℕ) {h : Heard} {G : Fork} {L : Lists}
    (b2 : Said (recOf P rows) h G L) (b3 : Sized G) (A : Attention.Plan) (hN : A.NC = S.calls.size)
    (hu : iU3 = A.iU3)
    (gL : Forest.Heard) (hzk : gL.zk = zk) (hsh : gL.shape.calls.size = 4) (he : gL.e.size = 4) (Fj : Fork)
    (tj : OnBytes.K.Kc.Tape) (lk : LookIn) (hlz : lk.zx = zx) (hlp : lk.planesOk = true) :
    ∃ l i l₁ l₂ jn kf xj, Returns S zx zk G h l A gL i Kc l₁ l₂ jn k3 kf Fj tj xj tl nW lk := by
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
  obtain ⟨t, ht⟩ := K5Law.tablesP_of_lens (lk := lk) LL ht0 hlp
    (by rw [hlz]; exact mergedPlanes_at U H3 Kz hlm hx1 hp) (by rw [hlz]; exact mergedTokens_at U Nn hl H3 Kz hx2 hp)
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
  exact ⟨l, ⟨geoOf S, p, t, zk, iU3⟩, l₁, l₂, jn, kf, xj,
    ⟨li, rfl, hzk.symm, hzk, hN, hp, h1, h2, hk, hx, ht, hlz, hmf, hu⟩⟩

end At

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.returns_at_lk
