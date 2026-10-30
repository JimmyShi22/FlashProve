-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/StageFits.lean: THE WEIGHTS THAT K4's TEXT HANDS A MASKED SUMCHECK FIT THE TYPED
STAGE's VARIABLES (`StgFits`, OnBytes/Tie/Pv/Lay/HearTieAll.lean), for the two token sumchecks'
form of weights and for the plain one; and, at a hearing, the typed output of the terms' sumcheck is
K4's record, read. Glue over `stgFits_eq`, `stgFits_plain`
(OnBytes/Tie/Pv/Lay/HearCanon.lean). No draw, no count.

  `ofFn_getD`: a list's image, written entry by entry.
  `stgFits_tsc`: for every stage with the pick of the constant coefficient, two scalars a round, k
    variables, whose weight at variable i reads zs[i], zs of length k: `StgFits` at `tscWs zs`.
  `stgFits_plainWs`: for every stage with the pick of the linear coefficient, two scalars a round
    and no weight: `StgFits` at `plainWs k`.
  `fits3`: at every `FullPar`, the third stage (the terms' token sumcheck), at a state z (the
    lookup's point): if `zpos D z j` reads zs[j] for j < lT and zs has length lT.
  `out3`: at a hearing's ledgers (`Led7`): `OutIs` of the third stage's data read off the tape
    (`aD3`) and K4's record tT.p: the premise O3 of Johnson/Road/K4/Claim4Heard.lean.

Limits. PREMISES of `out3`: the sizes' tie lT = lt · the letter zOf at the first statement is the
lookup's point (hz0) · `zpos` at that point reads the tail ztF that K4 holds (hzp:
`look_of_lines` gives it at a public record) · the third target is the record's. The first, second,
fifth, sixth and seventh stages are not treated here. A group that is not the first.
-/
import Johnson.Road.K4.OwnJoint
import Johnson.Road.K4.OwnLedgers
import Johnson.Road.K4.LookLeft
import OnBytes.Desc.First.P1.TailAdds
import OnBytes.Tie.Pv.Lay.HearCanon
import Cb.Pv.Lay.At.OwnW

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
open OnBytes.Tie.Pv.Lay (StgFits OutIs stgFits_eq stgFits_plain)
open OnBytes.Desc.First.P1 (gl NzT TailM TailR Tg7 aD3 aS3 tscWs plainWs)
open Inst.Model (Scl)
open Inst.Model.FFSeg (zpos)

/-- A list's image, written entry by entry. -/
theorem ofFn_getD {α β : Type} (f : α → β) (d : α) (n : ℕ) (zs : List α) (h : zs.length = n) :
    List.ofFn (fun i : Fin n => f (zs.getD i.val d)) = zs.map f := by
  subst h
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp

section Any
variable {M X : Type}

/-- The token sumchecks' form of weights. -/
theorem stgFits_tsc (S : Stg Cb.Gl.E M X) (st : S.L.St) (zs : List E)
    (hF : S.F = TWhole.F₀ S.L.T.par) (hn : ∀ i, S.L.M.n i = 2)
    (hl : zs.length = S.L.S.k)
    (hw : ∀ i, S.L.S.w st i = some (gl.val (zs.getD i.val zeroE))) :
    StgFits gl S st (tscWs zs) S.L.S.k S.L.M.DY := by
  have h := stgFits_eq gl S st (fun i => zs.getD i.val zeroE) hF hn hw
  rwa [ofFn_getD (fun z => Weight.equality z 3) zeroE S.L.S.k zs hl] at h

/-- The plain form. -/
theorem stgFits_plainWs (S : Stg Cb.Gl.E M X) (st : S.L.St)
    (hF : S.F = fun st => Cb.Pv.Lay.pick (S.L.T.par.vars st)) (hn : ∀ i, S.L.M.n i = 2)
    (hw : ∀ i, S.L.S.w st i = none) : StgFits gl S st (plainWs S.L.S.k) S.L.S.k S.L.M.DY :=
  stgFits_plain gl S st hF hn hw

end Any

variable [scl : Scl] {M Xs : Type}

/-- **The terms' token sumcheck.** -/
theorem fits3 (P : FullPar Cb.Gl.E M Xs) (z : ℕ → Cb.Gl.E) (zs : List E) (hl : zs.length = P.D.lT)
    (hz : ∀ j, j < P.D.lT → zpos P.D z j = gl.val (zs.getD j zeroE)) :
    StgFits gl P.own.toOwn.tail.s3 z (tscWs zs) P.D.lT 1 :=
  stgFits_tsc P.own.toOwn.tail.s3 z zs rfl (fun _ => rfl) hl
    fun i => congrArg some (hz i.val i.isLt)

/-- **At a hearing the typed output of the terms' sumcheck is K4's record, read.** -/
theorem out3 (P : FullPar Cb.Gl.E M Xs) {R : TailR} (W : TailM P.own.toOwn.tail R) {Pp : Pub}
    {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {o : Own} {F G : Fork} {t0 u : Tape} {H1 : Heard}
    {hd2 : Level} {tT : Tsc} {F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork}
    (Ld : Led7 Pp hp g fo o F G t0 u H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4)
    (hlt : P.D.lT = Pp.y.h.lt) (nz : NzT P.own.toOwn.tail (ksOf Pp hp) (t0.drop 1))
    (x : Xs × (Fin P.own.toOwn.gT → Cb.Gl.E)) (g7 : Tg7) (ht3 : g7.t3 = tT.p.target)
    (hz0 : P.zOf x.1 = zAt fo) (hzl : Pp.y.h.lt ≤ H1.ztF.size)
    (hzp : ∀ j, j < P.D.lT → zpos P.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE)) :
    OutIs gl (aD3 W (ksOf Pp hp) (t0.drop 1) nz x g7) tT.p := by
  have hl : (H1.ztF.toList.take Pp.y.h.lt).length = P.D.lT := by
    rw [List.length_take, Array.length_toList, hlt]
    exact Nat.min_eq_left hzl
  have f0 : StgFits gl P.own.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) P.D.lT 1 := by
    refine fits3 P _ _ hl fun j hj => ?_
    have e : aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7 = P.zOf x.1 := rfl
    rw [e, hz0, hzp j hj]
    congr 1
    rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (hlt ▸ hj),
      ← List.getD_eq_getElem?_getD]
    simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]
  have f : StgFits gl P.own.toOwn.tail.s3 (aS3 W (ksOf Pp hp) (t0.drop 1) nz x g7)
      (tscWs (H1.ztF.toList.take Pp.y.h.lt)) Pp.y.h.lt 1 :=
    ⟨f0.k.trans hlt, f0.dY, f0.two, f0.fit⟩
  exact stgT_out W.w3.num (ksOf Pp hp).k3 _ nz.b3 _ g7.t3 rfl (tsc_recAt Ld.c3) ht3 f

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.stgFits_tsc
#print axioms OnBytes.Road.K4.fits3
#print axioms OnBytes.Road.K4.out3
