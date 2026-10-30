-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PubOfHearTied.lean: the library's public record of a layer sub-proof at the letters
of a run of K4's own text, WITH EVERY LETTER THAT THE RECORD's CLAIMS READ TIED TO THE RUN OR TO A
PREMISE.

Johnson/Road/K4/PubOfHear.lean (`pub34_of_hear`) makes a record X : Pub34 K from a return of `hear`
and ties fifteen of its letters. The claims of
Johnson/Road/Rows/LayerEnds34.lean read more letters of X than these: the tables X.tb, X.lk and the
shape X.h (joinK, clT, gpos, sig1), X.alpha and X.theta (joinK), X.p.shownT (sig1), X.tl
(ReadsTrue), X.c.wsLay and X.cl (Merged, vecB), X.pans (Gated, MapsL4). Whoever opens "there is X"
there gets these claims at SOME tables and SOME tail. Here the same record is made, by the same
term, and the conclusion says which they are.

  `pub34_of_hear_run`: under the premises of pub34_of_hear, to the letter, there is a record X with
      that theorem's fifteen ties and its three lines on the batched sumcheck's stretch, and beside
      them: X.h, X.pc, X.s, X.lk, X.tb, X.s0, X.tl are the premises' letters; X.alpha and X.theta
      are what the lookup heard; o.H.tT = some X.tT; X.c and X.p are written out whole, X.p but for
      shownT; X.p.shownT is what the ledger G2, at which the batched sumcheck's stretch began, shows
      from the slot X.tT.sEnd on; G2 and the tape u2 there are what hearNorms and then hearTerms
      return from the run's own start (F, t), so that a caller who has these two returns has the
      same G2 and u2; X.H1, X.V, X.shownA, X.shownB are what one ledger Fe shows at the slots of
      o.K; the number of X.pans' weight claims is the plan's NCL, less 1 in the first group.
      X.TS, X.pans, X.cl, X.r, X.Zp, X.ends, X.pts, X.weighed, X.parts are not tied by an equation
      here: the record's own fields (hTS hp hcl hl hZ hm hpts hw hparts) say of each that a function
      of tied letters returns it.

  `pub34_of_hear_tied`: the same without the two returns of hearNorms and hearTerms.


Limits. As PubOfHear.lean's: it makes a record; nothing on what anything is worth, on a draw, on
soundness. The premises are that file's (public lines of the plan; what the lookup heard; hinv).
Of the ledger Fe nothing is said but what it shows. By the head of LayerEnds34.lean no record exists
at the small example (hfl fails there).
-/
import Johnson.Road.K4.PubOfHear

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Env Lay Heard Pub Own Reads PanelEnv ClaimEnv layout scalesHeld
  readsOf stubO nEndT)
open Inst.Model (Tables)
open Inst.Model.FFSeg (Dim used lut)
open OnBytes.Desc.First.K4 (engFl hear)

variable {K : Type} [Field K]

theorem pub34_of_hear_run (ρ : Reading K) {P : Pub} {hp : Layer.HPlan2} {g : Nat}
    {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (h : hear engFl P hp g fo F t = some (o, G, u))
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
      X.h = hS ∧ X.pc = pc ∧ X.s = s ∧ X.lk = lk ∧ X.tb = tb ∧ X.s0 = s0 ∧ X.tl = tl ∧
      X.alpha = o.H.fo.alpha ∧ X.theta = o.H.fo.theta ∧ o.H.tT = some X.tT ∧
      X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := X.tT.r } ∧
      X.p = { v := o.v, e := o.H.fo.e, shownT := X.p.shownT, zt := o.H.ztF, stubO := stubO P.y } ∧
      (X.pans.nextV == hp.NCL - (if (g == 0) = true then 1 else 0)) = true ∧
      ∃ (H1 : Heard) (G1 G2 G3 Fe : Fork) (u1 u2 u3 : Tape),
        Desc.First.K4.hearNorms engFl P g fo F t = some (H1, G1, u1) ∧
        Desc.First.K4.hearTerms engFl P H1 G1 u1 = some (o.H, G2, u2) ∧
        Desc.First.K4.hearStack engFl P o.v o.H hp.lamS
          (hp.NCL - (if (g == 0) = true then 1 else 0)) G2 u2 = some (o.K, G3, u3) ∧
        X.om = powers (Desc.First.P1.tapeEps u2) 2 ∧
        Desc.First.K4.stackStart o.v o.H G2 u2 = startOf X.H X.om X.parts ∧
        ((Array.range (nEndT P.y)).mapM fun i => G2.shown (X.tT.sEnd + i)) = some X.p.shownT ∧
        ((Array.range (1 + P.y.LamM)).mapM fun i => Fe.shown (o.K.sH1 + i)) = some X.H1 ∧
        ((Array.range (hp.NCL - (if (g == 0) = true then 1 else 0))).mapM
          fun i => Fe.shown (o.K.sV + i)) = some X.V ∧
        Fe.shown o.K.sA0 = some X.shownA ∧ Fe.shown o.K.sB0 = some X.shownB := by
  obtain ⟨hcov, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e5, _, ev, e7, e8, ehd2, e9,
    e10⟩ := Desc.First.K4.hear_public h
  obtain ⟨_, H1, G1, u1, G2, u2, n1, n2, G3, u3, n3, _⟩ := Desc.First.K4.hear_calls h
  obtain ⟨Zc, ends, _, q2, q3, q4, q5, q6⟩ := Desc.First.K4.hearNorms_public n1
  obtain ⟨kfo, _, _, _, kzt, _⟩ := Desc.First.K4.hearTerms_keeps n2
  obtain ⟨tT, hT, hKT, _⟩ := Desc.First.K4.hearTerms_KT n2
  obtain ⟨tT', shownT, TS', pans, Fe, Hv, V, shA, shB, C, Fk, tk, j0, hT', s3, s4, s5,
    s6, s7, s8, s9, s10, s11, s12, s13, s14, _, _, s16⟩ := Desc.First.K4.hearStack_public n3
  obtain ⟨weighed, parts, _, _, w1, w2, _, _, _, _, eC, _, _⟩ := joinStart_startOf j0
  have eS : Desc.First.K4.stackStart o.v o.H G2 u2 =
      startOf o.H (powers (Desc.First.P1.tapeEps u2) 2) parts := by
    unfold Desc.First.K4.stackStart
    rw [j0]
    exact eC
  have eT : tT = tT' := Option.some.inj (hT.symm.trans hT')
  subst eT
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
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hT, rfl, rfl, s7,
    H1, G1, G2, G3, Fe, u1, u2, u3, n1, n2, n3, rfl, eS, s3, s11, s12, s13, s14⟩

/-- The same without the two returns that fix G2 and u2.
For whoever calls it. -/
theorem pub34_of_hear_tied (ρ : Reading K) {P : Pub} {hp : Layer.HPlan2} {g : Nat}
    {fo : Forest.Heard} {F G : Fork} {t u : Tape} {o : Own}
    (h : hear engFl P hp g fo F t = some (o, G, u))
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
      X.h = hS ∧ X.pc = pc ∧ X.s = s ∧ X.lk = lk ∧ X.tb = tb ∧ X.s0 = s0 ∧ X.tl = tl ∧
      X.alpha = o.H.fo.alpha ∧ X.theta = o.H.fo.theta ∧ o.H.tT = some X.tT ∧
      X.c = { v := o.v, wsLay := P.wsLay, rope := P.rope, rs := o.K.rs, rt := X.tT.r } ∧
      X.p = { v := o.v, e := o.H.fo.e, shownT := X.p.shownT, zt := o.H.ztF, stubO := stubO P.y } ∧
      (X.pans.nextV == hp.NCL - (if (g == 0) = true then 1 else 0)) = true ∧
      ∃ (G2 G3 Fe : Fork) (u2 u3 : Tape),
        Desc.First.K4.hearStack engFl P o.v o.H hp.lamS
          (hp.NCL - (if (g == 0) = true then 1 else 0)) G2 u2 = some (o.K, G3, u3) ∧
        X.om = powers (Desc.First.P1.tapeEps u2) 2 ∧
        Desc.First.K4.stackStart o.v o.H G2 u2 = startOf X.H X.om X.parts ∧
        ((Array.range (nEndT P.y)).mapM fun i => G2.shown (X.tT.sEnd + i)) = some X.p.shownT ∧
        ((Array.range (1 + P.y.LamM)).mapM fun i => Fe.shown (o.K.sH1 + i)) = some X.H1 ∧
        ((Array.range (hp.NCL - (if (g == 0) = true then 1 else 0))).mapM
          fun i => Fe.shown (o.K.sV + i)) = some X.V ∧
        Fe.shown o.K.sA0 = some X.shownA ∧ Fe.shown o.K.sB0 = some X.shownB := by
  obtain ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28,
    _, _, G2, G3, Fe, _, u2, u3, _, _, r⟩ :=
    pub34_of_hear_run ρ h hy S hs hg hrd hmats hρ Z hc hN hfl hsx hsy hzk he hs0 hpt Zw hsL hlw h4
      R htm hNM hpad hinv
  exact ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21, a22, a23, a24, a25, a26, a27, a28,
    G2, G3, Fe, u2, u3, r⟩

#print axioms pub34_of_hear_run
#print axioms pub34_of_hear_tied

end OnBytes.Road.K4
