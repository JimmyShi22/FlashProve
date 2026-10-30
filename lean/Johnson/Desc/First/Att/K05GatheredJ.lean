-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05GatheredJ.lean: GatheredAll (Att/K05Agree.lean) with the join's tie as a
letter, so that a record in the lookup's
own names can stand in a statement.

Main names:
  `GatheredAllJ`: GatheredAll with "Jn x0 gL W m" in the place of hjv (the join's worth at what the
    lookup heard is its worth at the
    letters of Q, for all key values).
  `gatheredAll_of_J`: where Jn gives hjv: GatheredAllJ gives GatheredAll.

No conjunct of GatheredAllJ is shown in this file or in what it imports.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Agree

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open Iop Prob Cb TWhole IOR OnBytes OnBytes.Model OnBytes.Model.Road Johnson.L5.Layers Cb.Pv.Att Inst.Model
open OnBytes.Tie.Pv.Att (PscH SumH TailH UnitsH UnitsClaims seenAfter recOf)
open VerifiableInference.Desc.Part
open K5Law (oldOf PlanLaw AllZero)
open Cb.Pv.Att.End (EndLay JoinLay)

variable {M0 Mg X : Type}

/-- **GatheredAll with the join's tie as a letter.** Jn x0 gL W m: what ties the lookup's heard
record gL, in the world W, to the
first statement x0 and the message m. -/
def GatheredAllJ (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape)
    {J₂ : Type} [Fintype J₂] [DecidableEq J₂] (Ly : EndLay (closedOf P0 Λ ns N) J₂)
    (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop) (zx : Array E)
    (zk : Array (Array E)) (entry : ℕ → ℕ → ℕ → Cb.Gl.E) (G : Fork) (h : Heard) (L : Lists) (x0 : X) (m : Mg) : Prop :=
  ∀ (nz : BetasNz Reading.gl L) (du : UnitsH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units) (dt : TailH Reading.gl ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail),
    UnitsOfP ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (recOf (closedOf P0 Λ ns N) rows).score h.scores.toList L.planes.flatten L.units →
    TailOfP dt (recOf (closedOf P0 Λ ns N) rows) h L →
    UnitsVals ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du
      (unitsAdd (ρ := Reading.gl) ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units (landedUnits _ _) L.planes.flatten L.units (x0, [])) →
    TailVals dt (tailAdd ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).tail L h nz (landedTail _ _) (seenAfter ((closedOf P0 Λ ns N).own (theMeans Cb.Gl.E _ _ _)).units du (x0, []))) →
    ∃ (l : Left) (A : Attention.Plan) (gL : Forest.Heard) (i : Runs.In) (Kc : ℕ) (l₁ l₂ : List Aff) (jn : Runs.JoinsP)
      (k3 : Runs.PadIn) (kf : Array Aff) (Fj : Fork) (tj : OnBytes.K.Kc.Tape) (xj : Aff × Fork × OnBytes.K.Kc.Tape)
      (tl : HTailF2) (nW : ℕ) (lk : LookIn) (M : OnBytes.Road.Mats Cb.Gl.E),
      LeftIs (geoOf S) zk h G l ∧ i.g = geoOf S ∧ i.zk = gL.zk ∧ gL.zk = zk ∧ A.NC = S.calls.size ∧
      pointsOf i.g zk h l = some i.p ∧ Runs.firstRun i Kc = some (l₁, jn) ∧ Runs.secondRun i Kc = some l₂ ∧
      AllZero Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) (l₁ ++ l₂) ∧
      Runs.keysRun i k3 jn = some kf ∧ VerifiableInference.Desc.First.Look.joinF gL kf Fj tj = some xj ∧
      xj.1.value Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) = 0 ∧
      Jn x0 gL (G.worldOf Reading.gl (Λ.maskOf m) entry) m ∧
      tablesP i.g (K5Law.matsOf tl.mats) nW lk i.p = some i.t ∧ lk.zx = zx ∧
      OnBytes.Road.Rows.AttAt Reading.gl (G.worldOf Reading.gl (Λ.maskOf m) entry) tl Kc M (oldOf S gL i) lid cf fs ∧
      K5Law.CellsTie (oldOf S gL i) M Ly.cellJ ((closedOf P0 Λ ns N).msg m)

theorem gatheredAll_of_J (P0 : OwnPar Cb.Gl.E M0 X) (Λ : Lin P0 Mg) (ns : ℕ) (N : Nums) (rows : ℕ) (S : Attention.Shape)
    (lid : ℕ) (cf : Attention.Cfg) (fs : Model.Forest.Shape) {J₂ : Type} [Fintype J₂] [DecidableEq J₂]
    (Ly : EndLay (closedOf P0 Λ ns N) J₂) (Q : JoinLay (closedOf P0 Λ ns N)) (Jn : X → Forest.Heard → World Cb.Gl.E → Mg → Prop)
    {zx : Array E} {zk : Array (Array E)} {entry : ℕ → ℕ → ℕ → Cb.Gl.E} {G : Fork} {h : Heard} {L : Lists} {x0 : X} {m : Mg}
    (hJn : ∀ gL W, Jn x0 gL W m → ∀ kv, Cb.Pv.Att.End.joinVal (K5Law.qAt Reading.gl gL) kv (gL.cEnd.value Reading.gl W) =
      Cb.Pv.Att.End.joinVal (Q.q x0) kv ((Q.ce x0).val ((closedOf P0 Λ ns N).msg m)))
    (hga : GatheredAllJ P0 Λ ns N rows S lid cf fs Ly Jn zx zk entry G h L x0 m) :
    GatheredAll P0 Λ ns N rows S lid cf fs Ly Q zx zk entry G h L x0 m := by
  intro nz du dt d1 d2 d3 d4
  obtain ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, M, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hk, hx, hv, hJ,
    rest⟩ := hga nz du dt d1 d2 d3 d4
  exact ⟨l, A, gL, i, Kc, l₁, l₂, jn, k3, kf, Fj, tj, xj, tl, nW, lk, M, li, hg, hz, hzk, hN, hP, h1, h2, hZ, hk, hx, hv,
    hJn gL _ hJ, rest⟩

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.gatheredAll_of_J
