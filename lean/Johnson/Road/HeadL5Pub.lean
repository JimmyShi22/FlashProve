-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5Pub.lean: the public hypotheses on the layers and on the output head, from the
public part of a stage and one short list of numbers of the parameter file.

The theorems that lead to the reply from statements on the integer matrices behind each sub-proof,
numbered as the verifier's lists number them, ask public things: that the layers' layout and the
head's layout are what the verifier's functions return, and that the shapes have the sizes of the
library's reference. This file gathers them under two hypotheses: the verifier's function publicOf
(OnBytes/Model/VerifyPublic.lean) has returned X; and 46 numbers and two switches of the parameter
file, as the strict scan has read them, are the reference's. (Twelve of the 46 do not enter
public_of_publicOf: seven are attention's, five the normalisations'. Here att_of_at and norms_of_at
only read them off the list, for other files. They stand here so that there is one list.)

Which is which. That a layout is what a function returns is a line of publicOf. The number of groups
of layers is a line of the layers' layout and two numbers. All else are values of the parameter
file: no test of publicOf fixes one of the 46 to its number. They are gathered in one condition,
PublicAt, which reads the scanned file alone and is decidable, so that a run can show it of a given
file.

Main definitions: numsOf, refNums, PublicAt; LayersHeadAt (what is concluded).
Main theorems: PublicAt.num; att_of_at, norms_of_at; switches_of_at, sized_of_at, sized2_of_at,
p4_of_at, fullH_of_at; public_of_publicOf.

What is not claimed. Nothing on attention's shapes, on the table of scales, or on any file: that
some parameter file has PublicAt is not shown here. The program does not import this file.
-/
import Johnson.Road.HeadPub
import Johnson.Road.HeadPlace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model.All (DF)

/-- 46 numbers of the parameter file as scanned, in this order, counted from 0: prof (the line's
value modulo 16), lt, L, ll, d, H, G, dh, f, fe, NE, V, la, lmaf, NAf, lmad, NAd, lmar, lmq, lmx,
lmhf, NHf, lmhd, lmhr, hq, hv, ho, hgD, huD, hdD, hr, the limbs of a value of the stream (5 with the
line xl, else 4), sh, sT; from number 34 on, attention's: lB, S, rx, lmS, lmh, lmo, NAs; from number
41 on, the normalisations': eps1, eps2, MF, KF, epsF. -/
def numsOf (P : Model.PolScan) : List ℕ :=
  [P.h.prof, P.h.lt, P.h.L, P.h.ll, P.h.d, P.h.H, P.h.Gk, P.h.dh, P.h.f, P.h.fe, P.h.NE, P.h.V,
    P.h.la, P.h.lmaf, P.h.NAf, P.h.lmad, P.h.NAd, P.h.lmar, P.h.lmq, P.h.lmx, P.h.lmhf, P.h.NHf,
    P.h.lmhd, P.h.lmhr, P.value "hq", P.value "hv", P.value "ho", P.value "hgD", P.value "huD",
    P.value "hdD", P.value "hr", P.XL, P.h.digSh, P.h.tabS, P.h.lB, P.h.Sx, P.h.rx, P.h.lmS,
    P.h.lmh, P.h.lmo, P.h.NAs, P.h.eps.getD 0 0, P.h.eps.getD 1 0, P.h.MF, P.h.KF, P.h.epsF]

/-- The same numbers at the library's reference sizes, in the same order. -/
def refNums : List ℕ :=
  [4, 10, 48, 2, 5120, 40, 8, 128, 16384, 8192, 128, 202048, 16, 16, 3, 15, 1, 13, 16, 16, 16, 4,
    14, 13, 2, 1, 1, 1, 1, 1, 1, 5, 8, 4, 6, 12, 8, 16, 13, 16, 1, 53687, 53687, 44, 30, 53687]

/-- **The numbers that stay numbers of the configuration**: the 46 numbers are the reference's, and
the lines gcl and rcl are there. -/
def PublicAt (P : Model.PolScan) : Prop :=
  numsOf P = refNums ∧ P.gcl = true ∧ P.rcl = true

/-- A run can decide it. -/
instance decPublicAt (P : Model.PolScan) : Decidable (PublicAt P) := by
  unfold PublicAt
  infer_instance

/-- Number k of the list. -/
theorem PublicAt.num {P : Model.PolScan} (A : PublicAt P) (k : ℕ) :
    (numsOf P).getD k 0 = refNums.getD k 0 := by
  rw [A.1]

section At

variable {P : Model.PolScan} (A : PublicAt P)

include A

/-- Attention's seven numbers. -/
theorem att_of_at : P.h.lB = 6 ∧ P.h.Sx = 12 ∧ P.h.rx = 8 ∧ P.h.lmS = 16 ∧ P.h.lmh = 13 ∧
    P.h.lmo = 16 ∧ P.h.NAs = 1 :=
  ⟨A.num 34, A.num 35, A.num 36, A.num 37, A.num 38, A.num 39, A.num 40⟩

/-- The normalisations' five numbers. -/
theorem norms_of_at : P.h.eps.getD 0 0 = 53687 ∧ P.h.eps.getD 1 0 = 53687 ∧ P.h.MF = 44 ∧
    P.h.KF = 30 ∧ P.h.epsF = 53687 :=
  ⟨A.num 41, A.num 42, A.num 43, A.num 44, A.num 45⟩

/-- The layers' switches. -/
theorem switches_of_at : Switches (Model.Verify.layerShape P) where
  p3 := by
    have e1 : P.h.prof = 4 := A.num 0
    have e2 : P.h.NE = 128 := A.num 10
    show (P.h.prof == 3 || (P.h.prof == 4 && decide (0 < P.h.NE))) = true
    simp [e1, e2]
  gcl := A.2.1
  rcl := A.2.2
  xl := A.num 31
  hq := A.num 24
  hv := A.num 25
  ho := A.num 26
  hgD := A.num 27
  huD := A.num 28
  hdD := A.num 29
  hr := A.num 30

/-- The layers' sizes are the reference's. -/
theorem sized_of_at : Sized (Model.Verify.layerShape P) DF where
  d := (A.num 4).symm
  f := (A.num 8).symm
  fe := (A.num 9).symm
  nexp := (A.num 10).symm
  nq := (A.num 5).symm
  nkv := (A.num 6).symm
  ch := (A.num 7).symm
  lT := (A.num 1).symm
  lL := (A.num 3).symm

/-- The sizes of the layers' matrices are the reference's. -/
theorem sized2_of_at : Sized2 (Model.Verify.layerShape P) DF := by
  have e1 : P.h.lt = 10 := A.num 1
  have e2 : P.h.lmaf = 16 := A.num 13
  have e3 : P.h.NAf = 3 := A.num 14
  have e4 : P.h.lmad = 15 := A.num 15
  have e5 : P.h.NAd = 1 := A.num 16
  have e6 : P.h.lmar = 13 := A.num 17
  have e7 : P.h.lmq = 16 := A.num 18
  have e8 : P.h.lmx = 16 := A.num 19
  exact {
    fBig_af := by
      show 6 = P.h.lmaf - P.h.lt
      rw [e2, e1]
    fBig_q := by
      show 6 = P.h.lmq - P.h.lt
      rw [e7, e1]
    fBig_x := by
      show 6 = P.h.lmx - P.h.lt
      rw [e8, e1]
    fAd := by
      show 5 = P.h.lmad - P.h.lt
      rw [e4, e1]
    fAr := by
      show 3 = P.h.lmar - P.h.lt
      rw [e6, e1]
    parts := e3.symm
    NAd := e5 }

/-- The proof covers attention. -/
theorem p4_of_at : (Model.Verify.layerShape P).p4 = true := by
  have e1 : P.h.prof = 4 := A.num 0
  show (P.h.prof == 4) = true
  simp [e1]

/-- The head's sizes are the reference's. -/
theorem fullH_of_at (y : Model.Layer.Lay) : FullH (Model.Verify.headShape P y) where
  lt := A.num 1
  la := A.num 12
  d := A.num 4
  V := A.num 11
  XL := A.num 31
  lmhf := A.num 20
  NHf := A.num 21
  lmhd := A.num 22
  lmhr := A.num 23

end At

/-- What is concluded of the layers and of the head, in the letters of the public part X: the shape
of the layers is layerShape X.P, their layout X.y, the head's shape X.hS, its layout X.HLy. -/
structure LayersHeadAt (X : Model.Verify.Public) : Prop where
  /-- the layers' layout is what the verifier's function returns -/
  lay : Model.Layer.layout (Model.Verify.layerShape X.P) X.P.polCalls = .ok X.y
  /-- the layers' switches -/
  switches : Switches (Model.Verify.layerShape X.P)
  /-- the layers' sizes -/
  sized : Sized (Model.Verify.layerShape X.P) DF
  /-- the sizes of the layers' matrices -/
  sized2 : Sized2 (Model.Verify.layerShape X.P) DF
  /-- the proof covers attention -/
  p4 : (Model.Verify.layerShape X.P).p4 = true
  /-- twelve groups of layers -/
  groups : X.y.NGr = 12
  /-- the head's sizes -/
  full : FullH X.hS
  /-- the head's layout is what the verifier's function returns -/
  head : Model.Head.layout X.hS X.y.tauFC = .ok X.HLy
  /-- two further numbers of the head's shape -/
  sh : X.hS.digSh = 8
  sT : X.hS.tabS = 4

/-- **The public hypotheses on the layers and on the head, from one line and one list of
numbers.** -/
theorem public_of_publicOf {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) (A : PublicAt X.P) : LayersHeadAt X := by
  obtain ⟨P, y, hpl, eP, ey, eS, -, hl, -⟩ := public_parts h
  have hy := layerLayout_of_polLayout hpl
  rw [← eP, ← ey] at hy
  rw [← ey] at hl
  have S := switches_of_at A
  have hN := (admitted_of_layout hy S.p3).NGr
  have e1 : X.P.h.L = 48 := A.num 2
  have e2 : X.P.h.ll = 2 := A.num 3
  have eS' : X.hS = Model.Verify.headShape X.P X.y := by rw [eS, eP, ey]
  exact {
    lay := hy
    switches := S
    sized := sized_of_at A
    sized2 := sized2_of_at A
    p4 := p4_of_at A
    groups := by
      rw [hN]
      show X.P.h.L / 2 ^ X.P.h.ll = 12
      rw [e1, e2]
      norm_num
    full := by
      rw [eS']
      exact fullH_of_at A X.y
    head := hl
    sh := by
      rw [eS']
      exact A.num 32
    sT := by
      rw [eS']
      exact A.num 33 }

#print axioms public_of_publicOf

end OnBytes.Road.Hd
