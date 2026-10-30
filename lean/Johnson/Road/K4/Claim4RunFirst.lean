-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Claim4RunFirst.lean: THE FIRST GROUP's twin of Johnson/Road/K4/Claim4Run.lean (its
part at the typed chain): the same with the public record made from the hearing itself.

The statements and proofs are that file's, turned to the first group's letters by a program
(FullFPar for FullPar; the chain P.ownF.toOwn.tail; the records LedG and TgRecF, which stand in
every group, with the tail's tape t0.drop (k0 g)) and compiled; each name bears an F.

Main names: `first4_of_hearF`.

Limits. As that file's. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.Claim4Run
import Johnson.Road.K4.Claim4HeardFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Env Lay Heard Pub Own Reads PanelEnv ClaimEnv layout scalesHeld
  readsOf stubO nEndT HPlan2)
open OnBytes.Tie.Pv.Lay (OutIs)
open OnBytes.Desc.First.K4 (engFl hear stackRec)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aY4 aD3 sentOf)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim used lut LW)
open OnBytes.Desc.First.K4 (k0)

variable [scl : Scl] {M Xs : Type}

/-- **The fourth equation on the claimed sums, from the hearing and the plan's public lines.** -/
theorem first4_of_hearF (P : FullFPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.ownF.toOwn.tail R)
    {Pp : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape}
    {H1 : Heard} {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork} {u5 : Tape}
    (h : hear engFl Pp hp g fo F t0 = some (o, G, u))
    (Ld : LedG Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5)
    {hS : Layer.Shape} {pc : List (List String)} {s : WsShape} {lk : ℕ} {s0 : Forest.Shape}
    {tl : HTailF2}
    (hy : layout hS pc = .ok Pp.y) (S : Switches hS) (hs : scalesHeld hS Pp.sc = .ok ())
    (hg : g < Pp.y.NGr) (hrd : readsOf Pp.y = .ok Pp.rd)
    (hmats : ((Pp.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR Pp.y g)
    (hρ : Numerals Reading.gl) (Z : Sized hS P.D) (hc : P.D.cap = hS.lidb) (hN : LinesAre Pp.y)
    (hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used P.D k))
    (hsx : fo.zx.size = Pp.y.fo.dT) (hsy : fo.zy.size = Pp.y.fo.rK)
    (hzk : fo.zk = (Array.range Pp.y.fo.NC).map fun q =>
      fo.zy.extract (Pp.y.fo.rK - Pp.y.fo.iota.getD q 0) fo.zy.size ++ fo.zx)
    (he : fo.e = (Array.range Pp.y.fo.NC).map (Forest.callWeight Pp.y.fo fo.zy))
    (hs0 : Forest.shape Pp.y.cl Pp.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (Zw : SizedW s P.D.P) (hsL : s.L = hS.L) (hlw : wsLayOf s true lk = .ok Pp.wsLay)
    (h4 : hS.p4 = true)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < Pp.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := Pp.wsLay, rope := Pp.rope, rs := o.K.rs, rt := rt } P.D P.tb
        (g * Pp.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR Pp.y g) (hNM : tl.NM = tl.mats.size)
    (hpad : ∀ k : Fin 8,
      Reading.gl.val (ofF ((Pp.y.cl.getD k.val {}).tauAt (Pp.y.cl.getD k.val {}).t0)) =
        (((lut P.tb k).pad : ℤ) : Cb.Gl.E))
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam)
    (w : ℕ → LW Cb.Gl.E) (nz : NzT P.ownF.toOwn.tail (ksOf Pp hp) (t0.drop (k0 g)))
    (x : P.ofp.fs.X3) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop (k0 g)))).target)
    (O3 : OutIs gl (aD3 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7) tT.p)
    (hz0 : P.zOf (P.ofp.fs.x0F x) = zAt fo) (hk0 : P.kTg (P.ofp.fs.x0F x) = kTgAt fo F) (hfil :
        Fo.FilledA F
        fo.cEnd) :
    (P.ownF.toOwn.tail.s4.cl (aY4 W (ksOf Pp hp) (t0.drop (k0 g)) nz x g7)
      (Johnson.L5.Layers.rd gl P.ownF.toOwn.tail.s4.n
        (sentOf (((ksOf Pp hp).tc4 (t0.drop (k0 g))).drop 1)))).1 = gl.val g7.t4 := by
  obtain ⟨X, a1, a2, a3, _, _, _, _, _, _, _, _, _, _, _, a15, a16, _, _, _, a20, _, _, a23, a24,
    a25, _, _, _, H1', G1x, G2x, _, _, u1x, u2x, _, n1, n2, _, hom, hst, _⟩ :=
    pub34_of_hear_run Reading.gl h hy S hs hg hrd hmats hρ Z hc hN hfl hsx hsy hzk he hs0 hpt Zw
      hsL hlw h4 Rp htm hNM hpad hinv
  obtain ⟨u1, m1, m2⟩ := Ld.nt
  have e1 := Option.some.inj (n1.symm.trans m1)
  simp only [Prod.mk.injEq] at e1
  obtain ⟨rfl, rfl, rfl⟩ := e1
  have e2 := Option.some.inj (n2.symm.trans m2)
  simp only [Prod.mk.injEq, true_and] at e2
  obtain ⟨rfl, rfl⟩ := e2
  obtain ⟨_, _, _, _, _, _, _, q6⟩ := Desc.First.K4.hearNorms_public m1
  obtain ⟨kfo, _⟩ := Desc.First.K4.hearTerms_keeps m2
  exact first4F P W Ld X a1 a2 (by rw [kfo, q6]) (by rw [a16, a3]; exact hscl) a15 a20 a23 a24 a25
    hom hst w nz x g7 ht4 O3 hz0 hk0 hfil

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.first4_of_hearF
