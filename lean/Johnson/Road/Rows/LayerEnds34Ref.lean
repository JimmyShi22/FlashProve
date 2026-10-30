-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerEnds34Ref.lean: a public record Pub34 (Johnson/Road/Rows/LayerEnds34.lean) at
the full-size example's numbers, from one equation that a program evaluates.

The statements of Johnson/Road/Rows/LayerEnds34.lean hold for every record Pub34. They would say
nothing if no such record existed. Johnson/Road/FormsKeysRef.lean has a run of the public hypotheses
of capstone, refRun, at the shape hKF, the library's reference sizes DF, tables tbRef and number of
column bits kRef; if it returns letters, the record PubRef holds of them (pubRef_of_run).

Main definitions: withKT: inputs of refRun with a given record of the second token sumcheck, and
with the form KT written by the line of hearTerms (OnBytes/Model/Layer.lean). pscLeft: a record of a
sumcheck in the shape in which the verifier's routines leave it.
Main theorems.
 - pub34_of_ref: if PubRef holds of letters d, and four more lines hold of them, there is a record
   Pub34 at these letters, with the slots numbered as hearStack numbers them.
 - refRun_letters: what refRun hands through from its inputs.
 - pub34_of_run: if refRun returns on the inputs withKT I t, eps is 1 in t, the two arrays of
   challenges of I are one array, and it has a challenge for each round, then there is a record
   Pub34 over the library's extension field at the letters that were returned and at t, and QKOk
   holds of it.
 - hinv_of, gl_inv: the field hinv at the reading Reading.gl. qkOk_of: QKOk.

What shows that the hypotheses of pub34_of_run can be met: a run that is no part of this library (it
costs some five minutes), at the full-size example's two files, with a record pscLeft. It is an
evaluation by Lean's interpreter: no theorem says that a record Pub34 exists. At the inputs of the
run of the public hypotheses themselves eps is 0, and no record Pub34 exists at them.

What is not claimed. The points, challenges and sent values of that run are made up: that a run of
the verifier on a proof file ends in such letters is not shown. Nothing on soundness, and nothing on
hiding. The program does not read this file.

-/
import Johnson.Road.Rows.LayerEnds3Y
import Johnson.Road.FormsKeysRef
import OnBytes.Slice.FieldInv
import OnBytes.Field.ExtEq

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open OnBytes.Model (Reading powers)
open Inst.Model (Scl tbRef)
open Inst.Model.All (DF)
open Inst.Model.Layout (kRef)

variable {K : Type} [Field K]

/-- The field hinv of Pub34, from two plainer facts: eps does not read as 0, and the reading takes
the program's inverse of eps to the inverse. -/
theorem hinv_of {ρ : Reading K} (hρ : Numerals ρ) {eps : E} (h0 : ρ.val eps ≠ 0)
    (hi : ρ.val (invE eps) = (ρ.val eps)⁻¹) : ρ.val (negE (invE eps)) * ρ.val eps = -1 := by
  rw [hρ.neg, hi, neg_mul, inv_mul_cancel₀ h0]

/-- The reading in the library's extension field takes the program's inverse to the inverse. -/
theorem gl_inv (a : E) : Reading.gl.val (invE a) = (Reading.gl.val a)⁻¹ := by
  show Slice.toE (invE a).triple = (Slice.toE a.triple)⁻¹
  rw [invE_triple, Slice.toE_invE]

/-- QKOk, from what the panel QK asks of the sizes: the condition on the shifts of queries and keys
follows from the verifier's test on the file of scales. -/
theorem qkOk_of (X : Pub34 K) (C : X.D.ChOK) : X.QKOk :=
  And.intro C fun l _ =>
    hk_of_scalesHeld (admitted_of_layout X.hy X.S.p3) X.hs X.hg X.D l

/-- A record Pub34 at the letters of a record PubRef. sA0: the slot of the first end value of the
batched sumcheck. -/
theorem pub34_of_ref {ρ : Reading K} {d : RefData} (A : PubRef ρ d) (hr : d.rs = d.c.rs)
    (hrs : d.lam ≤ d.c.rs.size)
    (hKT : d.H.KT = (d.tT.p.rowForm zeroE {}).scale (negE (invE d.tT.p.eps)))
    (hinv : ρ.val (negE (invE d.tT.p.eps)) * ρ.val d.tT.p.eps = -1) (sA0 : ℕ) :
    ∃ X : Pub34 K, X.ρ = ρ ∧ X.h = hKF ∧ X.p = d.p ∧ X.c = d.c ∧ X.H = d.H ∧ X.tT = d.tT ∧
      X.D = DF ∧ X.tb = tbRef ∧ X.lk = kRef ∧ X.om = powers d.xo 2 ∧ X.funs = d.funs ∧
      X.tl = d.pl.tl ∧ X.cl = d.cl ∧ X.pans = d.pans ∧ X.fin = d.s' ∧ X.parts = d.parts ∧
      X.sA0 = sA0 := by
  obtain ⟨hrd, ⟨s0, hs0, hpt⟩, hsx, hsy, htm, hNM, e⟩ := A.more
  have R := A.R
  rw [← e] at R
  have hst := A.hst
  rw [hr] at hst
  exact ⟨
    { ρ := ρ, h := hKF, pc := d.pc, p := d.p, c := d.c, rd := d.P.rd, r := d.r, D := DF,
      s := shapeV hKF 202048, lk := kRef, tb := tbRef, Zp := d.Zp, ends := d.ends, s0 := s0,
      H := d.H, tT := d.tT, tl := d.pl.tl, hd := d.hd, hd2 := d.hd2, pts := d.pts,
      funs := d.funs, TS := d.TS, pans := d.pans, cl := d.cl, om := powers d.xo 2, H1 := d.H1,
      V := d.V, lam := d.lam, shownA := d.shownA, shownB := d.shownB, fin := d.s',
      alpha := d.H.fo.alpha, theta := d.H.fo.theta, weighed := d.weighed, parts := d.parts,
      sA0 := sA0, sH1 := sA0 + 1,
      sB0 := sA0 + 1 + (1 + (if d.p.v.y.h.p3 then d.p.v.y.LamM else 0)),
      sV := sA0 + 1 + (1 + (if d.p.v.y.h.p3 then d.p.v.y.LamM else 0)) + 1,
      hy := A.hy, S := switchesK.2, hs := A.hs, hg := A.hg, hrd := hrd, hl := A.hl, ht := A.ht,
      hρ := A.hρ, Z := sizedKF.1, hc := cap_ref, hN := A.hN, hfl := hfl_ref, hsx := hsx,
      hsy := hsy, hzk := A.hzk, he := A.he, hZ := A.hZ, hzt := A.hzt, hm := A.hm, ha := A.ha,
      hs0 := hs0, hpt := hpt, env := A.env, Zw := sizedW_KF, hsL := rfl, hlw := A.hlw,
      h4 := rfl, hcrt := A.hcrt, R := R, htm := htm, hNM := hNM, hpts := A.hpts,
      hfun := A.hfun, hT := A.hT, hTS := A.hTS, hp := A.hp, hcl := A.hcl,
      hom := (powers_two ρ d.xo).1, hst := hst, hlam := A.hlam, hHe := A.hHe, hw := A.hw,
      hparts := A.hparts, hpad := A.hpad, hrs := hrs, hKT := hKT, hinv := hinv, hsH1 := rfl,
      hsB0 := rfl, hsV := rfl },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## From a run -/

/-- What refRun hands through from its inputs. -/
theorem refRun_letters {I : RefIn} {d : RefData} (h : refRun I = some d) :
    d.H = I.H ∧ I.H.tT = some d.tT ∧ d.rs = I.rs ∧ d.c.rs = I.crs := by
  unfold refRun at h
  obtain ⟨y, hy, h⟩ := bind_some h
  obtain ⟨u, hs, h⟩ := bind_some h
  obtain ⟨wsLay, hlw, h⟩ := bind_some h
  obtain ⟨P, hP, h⟩ := bind_some h
  obtain ⟨G, hG, h⟩ := bind_some h
  obtain ⟨pl, hpl, h⟩ := bind_some h
  obtain ⟨r, hl, h⟩ := bind_some h
  obtain ⟨Zp, hZ, h⟩ := bind_some h
  obtain ⟨zt, hzt, h⟩ := bind_some h
  obtain ⟨ends, hm, h⟩ := bind_some h
  obtain ⟨tT, hT, h⟩ := bind_some h
  obtain ⟨pts, hpts, h⟩ := bind_some h
  obtain ⟨funs, hfun, h⟩ := bind_some h
  obtain ⟨TS, hTS, h⟩ := bind_some h
  obtain ⟨pans, hp, h⟩ := bind_some h
  obtain ⟨cl, hcl, h⟩ := bind_some h
  obtain ⟨s', hst, h⟩ := bind_some h
  obtain ⟨weighed, hw, h⟩ := bind_some h
  obtain ⟨parts, hparts, h⟩ := bind_some h
  by_cases ht : I.tests y (I.c y r.1 wsLay tT.r) Zp zt ends = true
  · rw [if_pos ht] at h
    have e := (Option.some.inj h).symm
    subst e
    exact ⟨rfl, hT, rfl, rfl⟩
  · rw [if_neg ht] at h
    cases h

/-- A record of a sumcheck over token bits in the shape in which the verifier's routines are meant
to leave it (that they do is shown by no file): it starts from the hidden value under slot sCl;
it has one weight for each coordinate of zs, under the equality form, and one for the further
variable; one challenge for each; and the marks that it has started, has ended, and that its claim
has been made. Returns none if a weight is refused. -/
def pscLeft (sCl first : ℕ) (zs rs : List E) (beta eps target claim : E) : Option Model.Psc :=
  (zs.mapM fun z => Model.RoundForm.eq2.weight z 0).map fun ws =>
    { start := Model.Aff.slot sCl, target := target, eps := eps, claim := claim, first := first,
      vars := ws.toArray.push (OnBytes.Psc.Weight.atZero 2), r := rs.toArray.push beta,
      ended := true, rowMade := true, started := true }

/-- The inputs I with the record t of the second token sumcheck, and with the form KT written by the
line of hearTerms. -/
def withKT (I : RefIn) (t : Model.Tsc) : RefIn :=
  { I with H := { I.H with
      tT := some t
      KT := (t.p.rowForm zeroE {}).scale (negE (invE t.p.eps)) } }

/-- A record Pub34 over the library's extension field, from one equation: refRun returns on the
inputs withKT I t; and three tests on the inputs: eps is 1, the two arrays of challenges are one
array, and it has a challenge for each round. -/
theorem pub34_of_run {I : RefIn} {t : Model.Tsc} {d : RefData}
    (h : refRun (withKT I t) = some d) (he : t.p.eps = oneE) (hc : I.crs = I.rs)
    (hs : d.lam ≤ I.rs.size) (sA0 : ℕ) :
    ∃ X : Pub34 Cb.Gl.E, X.ρ = Reading.gl ∧ X.h = hKF ∧ X.p = d.p ∧ X.c = d.c ∧ X.H = d.H ∧
      X.tT = t ∧ X.D = DF ∧ X.tb = tbRef ∧ X.lk = kRef ∧ X.sA0 = sA0 ∧ X.QKOk := by
  obtain ⟨eH, eT, er, ec⟩ := refRun_letters h
  have eT' : d.tT = t := (Option.some.inj eT).symm
  have hr : d.rs = d.c.rs := by rw [er, ec]; exact hc.symm
  have hrs : d.lam ≤ d.c.rs.size := by rw [ec]; exact hc ▸ hs
  have hKT : d.H.KT = (d.tT.p.rowForm zeroE {}).scale (negE (invE d.tT.p.eps)) := by
    rw [eH, eT']
    rfl
  have h1 : Reading.gl.val d.tT.p.eps ≠ 0 := by
    rw [eT', he, Reading.gl.one]
    exact one_ne_zero
  obtain ⟨X, a1, a2, a3, a4, a5, a6, a7, a8, a9, -, -, -, -, -, -, -, a17⟩ :=
    pub34_of_ref (pubRef_of_run gl_numerals h) hr hrs hKT
      (hinv_of gl_numerals h1 (gl_inv _)) sA0
  exact ⟨X, a1, a2, a3, a4, a5, a6.trans eT', a7, a8, a9, a17,
    qkOk_of X (by rw [a7]; exact Inst.Model.FFSeg.ref_chOK)⟩

end OnBytes.Road.Rows
