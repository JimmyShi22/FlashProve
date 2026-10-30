-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PubOfHear.lean: the library's public record of a layer sub-proof, AT THE LETTERS OF
A RUN OF K4's OWN TEXT.

Johnson/Road/Rows/LayerEnds34.lean, LayerEnds3S.lean and LayerEnds3Y.lean state, for every record
`Pub34`, what the claims around the second token sumcheck and the batched sumcheck come to on cells.
A record has some sixty fields. Johnson/Road/Rows/LayerEnds34Ref.lean makes one at made-up letters,
and says: "that a run of the verifier on a proof file ends in such letters is not shown". Here a
record is made at what a run of `hear` (OnBytes/Desc/First/K4/Hear.lean) over the plain engine
returns.

  `pub34_of_hear`: if `hear engFl P hp g fo F t` returns o, and the named premises hold, there is a
      record X : Pub34 K with X.H = o.H, X.p.v = o.v, X.c.rs = o.K.rs, X.fin = o.K.fin, the four
      slots o.K's, X.hd = o.hd, X.hd2 = o.hd2, X.funs = o.funs, X.lam = hp.lamS, X.rd = P.rd;
      and, at the ledger and tape at which the batched sumcheck's stretch began, X.om is the
      powers 1, x of the element that the tape's first round drew, and the start form that the
      text made there (`stackStart`, K4/StackLaw.lean) is `startOf X.H X.om X.parts`.

WHICH FIELDS ARE PAID BY THE RUN (25): hl ht hZ hzt hm ha env hcrt hpts hfun hT hTS hp hcl hom hst
hlam hHe hw hparts hrs hKT hsH1 hsB0 hsV.
WHICH STAY PREMISES. Public lines of the plan (17): hy S hs hg
hrd hmats hρ Z hc hN hfl Zw hsL hlw h4 htm hNM, with R and hpad, which also read the reading. What
the lookup heard (6; another kind's): hsx hsy hzk he hs0 hpt. On the reading at the drawn eps (1):
hinv.

Limits. It makes a record: nothing on what anything is worth, on a draw, on soundness. By the head
of LayerEnds34.lean no record exists at the small example (hfl fails there).
-/
import Johnson.Road.Rows.LayerEnds3Y
import Johnson.Road.K4.JoinTie
import OnBytes.Desc.First.K4.BatchLaws
import OnBytes.Desc.First.K4.HearCalls
import OnBytes.Desc.First.K4.HearPublic
import OnBytes.Desc.First.K4.NormsPublic
import OnBytes.Desc.First.K4.StackPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Env Lay Heard Pub Own Reads PanelEnv ClaimEnv layout scalesHeld
  readsOf stubO)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim used lut)
open OnBytes.Desc.First.K4 (engFl hear)

variable {K : Type} [Field K]

theorem pub34_of_hear (ρ : Reading K) {P : Pub} {hp : Layer.HPlan2} {g : Nat} {fo : Forest.Heard}
    {F G : Fork} {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u))
    {hS : Layer.Shape} {pc : List (List String)} {D : Dim} {s : WsShape} {lk : ℕ} {tb : Tables}
    {s0 : Forest.Shape} {tl : HTailF2}
    (hy : layout hS pc = .ok P.y) (S : Switches hS) (hs : scalesHeld hS P.sc = .ok ())
    (hg : g < P.y.NGr) (hrd : readsOf P.y = .ok P.rd)
    (hmats : ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)) = matsR P.y g)
    (hρ : Numerals ρ) (Z : Sized hS D) (hc : D.cap = hS.lidb) (hN : LinesAre P.y)
    (hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used D k))
    (hsx : fo.zx.size = P.y.fo.dT) (hsy : fo.zy.size = P.y.fo.rK)
    (hzk : fo.zk = (Array.range P.y.fo.NC).map fun q =>
      fo.zy.extract (P.y.fo.rK - P.y.fo.iota.getD q 0) fo.zy.size ++ fo.zx)
    (he : fo.e = (Array.range P.y.fo.NC).map (Forest.callWeight P.y.fo fo.zy))
    (hs0 : Forest.shape P.y.cl P.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (Zw : SizedW s D.P) (hsL : s.L = hS.L) (hlw : wsLayOf s true lk = .ok P.wsLay)
    (h4 : hS.p4 = true)
    (R : ∀ (rt : Array E) (lam : ℕ), lam < P.y.Lam →
      RopeFits ρ { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := rt } D tb
        (g * P.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR P.y g) (hNM : tl.NM = tl.mats.size)
    (hpad : ∀ k : Fin 8,
      ρ.val (ofF ((P.y.cl.getD k.val {}).tauAt (P.y.cl.getD k.val {}).t0)) =
        (((lut tb k).pad : ℤ) : K))
    (hinv : ∀ tT, o.H.tT = some tT → ρ.val (negE (invE tT.p.eps)) * ρ.val tT.p.eps = -1) :
    ∃ X : Rows.Pub34 K, X.ρ = ρ ∧ X.H = o.H ∧ X.p.v = o.v ∧ X.c.rs = o.K.rs ∧ X.fin = o.K.fin ∧
      X.sA0 = o.K.sA0 ∧ X.sH1 = o.K.sH1 ∧ X.sB0 = o.K.sB0 ∧ X.sV = o.K.sV ∧ X.hd = o.hd ∧
      X.hd2 = o.hd2 ∧ X.funs = o.funs ∧ X.lam = hp.lamS ∧ X.rd = P.rd ∧ X.D = D ∧
      ∃ (G2 G3 : Fork) (u2 u3 : Tape),
        Desc.First.K4.hearStack engFl P o.v o.H hp.lamS
          (hp.NCL - (if (g == 0) = true then 1 else 0)) G2 u2 = some (o.K, G3, u3) ∧
        X.om = powers (Desc.First.P1.tapeEps u2) 2 ∧
        Desc.First.K4.stackStart o.v o.H G2 u2 = startOf X.H X.om X.parts := by
  obtain ⟨hcov, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e5, _, ev, e7, e8, ehd2, e9,
    e10⟩ := Desc.First.K4.hear_public h
  obtain ⟨_, H1, G1, u1, G2, u2, n1, n2, G3, u3, n3, _⟩ := Desc.First.K4.hear_calls h
  obtain ⟨Zc, ends, _, q2, q3, q4, q5, q6⟩ := Desc.First.K4.hearNorms_public n1
  obtain ⟨kfo, _, _, _, kzt, _⟩ := Desc.First.K4.hearTerms_keeps n2
  obtain ⟨tT, hT, hKT, _⟩ := Desc.First.K4.hearTerms_KT n2
  obtain ⟨tT', shownT, TS', pans, Fe, Hv, V, shA, shB, C, Fk, tk, j0, hT', _, s4, s5,
    s6, _, s8, s9, s10, _, _, _, _, _, _, s16⟩ := Desc.First.K4.hearStack_public n3
  obtain ⟨weighed, parts, _, _, w1, w2, _, _, _, _, eC, _, _⟩ := joinStart_startOf j0
  have eS : Desc.First.K4.stackStart o.v o.H G2 u2 =
      startOf o.H (powers (Desc.First.P1.tapeEps u2) 2) parts := by
    unfold Desc.First.K4.stackStart
    rw [j0]
    exact eC
  have efo : o.H.fo = fo := by rw [kfo, q6]
  have ezt : o.H.ztF = H1.ztF := kzt
  have eTS : TS' = TS := by
    rw [e7] at s4
    exact (Option.some.inj s4).symm
  subst eTS
  have p3 : P.y.h.p3 = true := by
    unfold Desc.First.K4.covers at hcov
    simp only [Bool.and_eq_true] at hcov
    exact hcov.1.1.1.2
  have vy : o.v.y = P.y := by rw [ev]
  have vsc : o.v.sc = P.sc := by rw [ev]
  have vg : o.v.g = g := by rw [ev]
  have vtab : o.v.tab = tab := by rw [ev]
  have vzk : o.v.zk = fo.zk := by rw [ev]
  refine ⟨
    { ρ := ρ, h := hS, pc := pc,
      p := { v := o.v, e := o.H.fo.e, shownT := shownT, zt := o.H.ztF, stubO := stubO P.y },
      c := { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := tT.r },
      rd := P.rd, r := (tab, laid, nU3), D := D, s := s, lk := lk, tb := tb, Zp := Zc,
      ends := ends, s0 := s0, H := o.H, tT := tT, tl := tl, hd := o.hd, hd2 := some hd2,
      pts := pts, funs := o.funs, TS := TS', pans := pans, cl := claimsP,
      om := powers (Desc.First.P1.tapeEps u2) 2,
      H1 := Hv, V := V, lam := hp.lamS, shownA := shA, shownB := shB, fin := o.K.fin,
      alpha := o.H.fo.alpha, theta := o.H.fo.theta, weighed := weighed, parts := parts,
      sA0 := o.K.sA0, sH1 := o.K.sH1, sB0 := o.K.sB0, sV := o.K.sV,
      hy := by rw [vy]; exact hy
      S := S
      hs := by rw [vsc]; exact hs
      hg := by rw [vg, vy]; exact hg
      hrd := by rw [vy]; exact hrd
      hl := by rw [vy, vg, ← hmats]; exact e5
      ht := vtab
      hρ := hρ, Z := Z, hc := hc
      hN := by rw [vy]; exact hN
      hfl := hfl
      hsx := by rw [efo, vy]; exact hsx
      hsy := by rw [efo, vy]; exact hsy
      hzk := by rw [efo, vy, vzk]; exact hzk
      he := by rw [efo, vy]; exact he
      hZ := by rw [efo, vy]; exact ok_of_toOption q2
      hzt := by rw [efo, vy, ezt]; exact ok_of_toOption q5
      hm := by rw [vzk, vy]; exact q3
      ha := q4
      hs0 := by rw [vy]; exact hs0
      hpt := by rw [vzk]; exact hpt
      env := rfl
      Zw := Zw, hsL := hsL, hlw := hlw, h4 := h4
      hcrt := rfl
      R := fun lam hl => by
        have hl' : lam < P.y.Lam := by rw [← vy]; exact hl
        have r := R tT.r lam hl'
        rw [← vg, ← vy] at r
        exact r
      htm := by rw [vy, vg]; exact htm
      hNM := hNM
      hpts := by rw [vy]; exact e9
      hfun := by rw [vy, efo]; exact e10
      hT := hT
      hTS := by rw [vy]; exact e7
      hp := s5
      hcl := by
        rw [hT] at e8
        exact e8
      hom := by
        rw [Desc.First.K4.powers_val ρ _ (by omega : 0 < 2), pow_zero]
      hst := by rw [vy]; exact s16
      hlam := s6
      hHe := rfl
      hw := w1
      hparts := w2
      hpad := by rw [vy]; exact hpad
      hrs := Nat.le_of_eq (Desc.First.K4.hearStack_rs n3).symm
      hKT := hKT
      hinv := hinv tT hT
      hsH1 := s8
      hsB0 := by rw [vy, p3]; exact s9
      hsV := s10 },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ehd2.symm, rfl, rfl, rfl, rfl,
    G2, G3, u2, u3, n3, rfl, eS⟩

#print axioms pub34_of_hear

end OnBytes.Road.K4
