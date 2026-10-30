-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageFitsMore.lean: Johnson/Road/K4/StageFits.lean GOES ON: the products' token
sumcheck and the batched sumcheck; and the general lemma for a product layer's form of weights. Glue
over `stgFits_eq`, `stgFits_plain`. No draw, no count.

  `stgFits_plainAt`: `stgFits_plainWs` at a number k that the stage's number of variables is.
  `stgFits_level`: for every stage with the pick of the constant coefficient, two scalars a round,
    whose weight at variable i reads rho[mu - 1 - order[i]], order of the stage's length: `StgFits`
    at `levelWs mu rho order`.
  `fits2`, `out2`: the second stage (the products' token sumcheck), at a state whose weights read
    zs; at a hearing: `OutIs` of `aD2` and K4's record H1.tV.p, if the token point in the first
    statement reads what the tape's first round drew.
  `fits4`, `out4`: the fourth stage (the batched sumcheck): plain; at a hearing: `OutIs` of `aD4`
    and `stackRec` at the ledger and the tape at which it begins.

Limits. PREMISES: the sizes' ties (lT = lt; the fourth stage's number of variables = lamS) · hx (the
token point) · the targets are the records'. The first, fifth, sixth and seventh stages are not
treated: `stgFits_level` is their tool. A group that is not the first.
-/
import Johnson.Road.K4.StageFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Cb Cb.Pv.Lay Cb.Pv.Att Cb.Pv.Lay.At
open OnBytes OnBytes.K.Kc OnBytes.Desc.First.K4
open OnBytes.Model (Reading Fork Forest.Heard Level Tsc)
open OnBytes.Model.Layer (Pub HPlan2 Own Heard)
open OnBytes.Psc (Weight)
open OnBytes.Tie.Pv.Lay (StgFits OutIs stgFits_eq)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD2 aS2 aD4 aS4 tscWs plainWs levelWs drawnOf)
open Inst.Model (Scl)

section Any
variable {M X : Type}

/-- The plain form, at a number that the stage's number of variables is. -/
theorem stgFits_plainAt (S : Stg Cb.Gl.E M X) (st : S.L.St) (k : ℕ) (hk : S.L.S.k = k)
    (hF : S.F = fun st => Cb.Pv.Lay.pick (S.L.T.par.vars st)) (hn : ∀ i, S.L.M.n i = 2)
    (hw : ∀ i, S.L.S.w st i = none) : StgFits gl S st (plainWs k) k S.L.M.DY := by
  subst hk
  exact stgFits_plainWs S st hF hn hw

/-- A product layer's form of weights. -/
theorem stgFits_level (S : Stg Cb.Gl.E M X) (st : S.L.St) (mu : ℕ) (rho : Array E)
    (order : List ℕ) (hF : S.F = TWhole.F₀ S.L.T.par) (hn : ∀ i, S.L.M.n i = 2)
    (hl : order.length = S.L.S.k)
    (hw : ∀ i, S.L.S.w st i = some (gl.val (rho.getD (mu - 1 - order.getD i.val 0) zeroE))) :
    StgFits gl S st (levelWs mu rho order) S.L.S.k S.L.M.DY := by
  have h := stgFits_eq gl S st (fun i => rho.getD (mu - 1 - order.getD i.val 0) zeroE) hF hn hw
  rwa [ofFn_getD (fun v => Weight.equality (rho.getD (mu - 1 - v) zeroE) 3) 0 S.L.S.k order hl]
    at h

end Any

variable [scl : Scl] {M Xs : Type}

/-- **The products' token sumcheck.** -/
theorem fits2 (P : FullPar Cb.Gl.E M Xs) (st : P.own.toOwn.tail.s2.L.St) (zs : List E)
    (hl : zs.length = P.D.lT)
    (hw : ∀ i, P.own.toOwn.tail.s2.L.S.w st i = some (gl.val (zs.getD i.val zeroE))) :
    StgFits gl P.own.toOwn.tail.s2 st (tscWs zs) P.D.lT 2 :=
  stgFits_tsc P.own.toOwn.tail.s2 st zs rfl (fun _ => rfl) hl hw

/-- **The batched sumcheck.** -/
theorem fits4 (P : FullPar Cb.Gl.E M Xs) (st : P.own.toOwn.tail.s4.L.St) (k : ℕ)
    (hk : P.own.toOwn.tail.s4.L.S.k = k) : StgFits gl P.own.toOwn.tail.s4 st (plainWs k) k 2 :=
  stgFits_plainAt P.own.toOwn.tail.s4 st k hk rfl (fun _ => rfl) fun _ => rfl

variable (P : FullPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.own.toOwn.tail R) {Pp : Pub}
  {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
  {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}

/-- **At a hearing the typed output of the products' token sumcheck is K4's record, read.** -/
theorem out2 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hlt : P.D.lT = Pp.y.h.lt) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (ht2 : g7.t2 = H1.tV.p.target)
    (hx : ∀ j : Fin P.own.toOwn.gT, x.2 j = gl.val ((drawnOf t0).getD j.val zeroE)) :
    OutIs gl (aD2 W (ksOf Pp hp) (t0.drop 1) nz x g7) H1.tV.p := by
  obtain ⟨u1, m1, _⟩ := Ld.nt
  obtain ⟨_, _, _, _, _, _, _, _, _, _, d0, _, e0, l0, hPV, _⟩ := hearNorms_tape m1
  obtain ⟨v2, c2⟩ := Ld.c2
  have hd : drawnOf t0 = d0 := by
    rw [e0]
    rfl
  have ht : H1.PV.toList.take Pp.y.h.lt = d0 := by
    rw [hPV, ← l0]
    exact List.take_length
  have f0 : StgFits gl P.own.toOwn.tail.s2 (aS2 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.PV.toList.take Pp.y.h.lt)) P.D.lT 2 := by
    rw [ht]
    refine fits2 P _ d0 (l0.trans hlt.symm) fun i => ?_
    rw [← hd]
    exact congrArg some (hx i)
  exact stgT_out W.w2.num (ksOf Pp hp).k2 _ nz.b2 _ g7.t2 rfl (tsc_recAt c2) ht2
    ⟨f0.k.trans hlt, f0.dY, f0.two, f0.fit⟩

/-- **At a hearing the typed output of the batched sumcheck is K4's record, read.** -/
theorem out4 (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hk : P.own.toOwn.tail.s4.L.S.k = hp.lamS)
    (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7)
    (ht4 : g7.t4 = (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop 1))).target) :
    OutIs gl (aD4 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (stackRec o.v o.H hp.lamS G2 ((ksOf Pp hp).tc4 (t0.drop 1))) :=
  stgT_out W.w4.num (ksOf Pp hp).k4 _ nz.b4 _ g7.t4 rfl (stack_recAt Ld.c4) ht4
    (fits4 P _ hp.lamS hk)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stgFits_level
#print axioms OnBytes.Road.K4.out2
#print axioms OnBytes.Road.K4.out4
