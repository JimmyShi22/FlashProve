-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/PublicCore.lean: the eleven public hypotheses of the way from the integer matrices
behind each sub-proof to "the request is true under its policy", from 41 numbers of the parameter
file instead of 46.

Why. Johnson/Road/HeadL5Pub.lean and HeadL5All.lean draw the eleven hypotheses from `PublicAt`: 46
numbers and two switches of the scanned parameter file are the reference's. The last five of the 46
are eps1, eps2, MF, KF and epsF, the constants of the normalisations. The goals' scope
(`VerifierAndGoals.InScope`, Ladder.lean) leaves these five free, so a theorem that asks `PublicAt` speaks of
fewer files than the goals do. None of the eleven hypotheses reads one of the five. This file says
so: `PublicCore` is `PublicAt` without the five, and the eleven follow from it.

The proofs are those of the two files named above, with the shorter list in the longer one's place.

Main definitions: `coreOf`, `refCore`, `PublicCore`.
Main theorems:
  `core_of_at`, `at_iff_core`: `PublicAt` is `PublicCore` with the five numbers.
  `public_of_core`: the eight hypotheses on the layers and on the head (`LayersHeadAt`).
  `fillRef_of_core`: attention's fourteen numbers.
  `eleven_of_core`: all eleven, at any numbers of the final normalisation.

What is not claimed. That a parameter file has `PublicCore`: for all files in the goals' scope that
is `core_of_scope` (Johnson/Goal/Meaning/ScopeCore.lean). Nothing on the table of scales being
lawful (Johnson/Meaning/Scope.lean). Nothing on a request or on a proof file. The program does not
import this file.
-/
import Johnson.Road.HeadL5All

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (NormPar tbRef)
open Inst.Model.All (DF)

/-- The first 41 of the 46 numbers of `numsOf`, in the same order: all but eps1, eps2, MF, KF and
epsF. -/
def coreOf (P : Model.PolScan) : List ℕ :=
  [P.h.prof, P.h.lt, P.h.L, P.h.ll, P.h.d, P.h.H, P.h.Gk, P.h.dh, P.h.f, P.h.fe, P.h.NE, P.h.V,
    P.h.la, P.h.lmaf, P.h.NAf, P.h.lmad, P.h.NAd, P.h.lmar, P.h.lmq, P.h.lmx, P.h.lmhf, P.h.NHf,
    P.h.lmhd, P.h.lmhr, P.value "hq", P.value "hv", P.value "ho", P.value "hgD", P.value "huD",
    P.value "hdD", P.value "hr", P.XL, P.h.digSh, P.h.tabS, P.h.lB, P.h.Sx, P.h.rx, P.h.lmS,
    P.h.lmh, P.h.lmo, P.h.NAs]

/-- The same numbers at the library's reference sizes: the first 41 of `refNums`. -/
def refCore : List ℕ :=
  [4, 10, 48, 2, 5120, 40, 8, 128, 16384, 8192, 128, 202048, 16, 16, 3, 15, 1, 13, 16, 16, 16, 4,
    14, 13, 2, 1, 1, 1, 1, 1, 1, 5, 8, 4, 6, 12, 8, 16, 13, 16, 1]

/-- The 41 numbers are the reference's, and the lines gcl and rcl are there. Nothing is asked of the
normalisations' five numbers. -/
def PublicCore (P : Model.PolScan) : Prop :=
  coreOf P = refCore ∧ P.gcl = true ∧ P.rcl = true

/-- A run can decide it. -/
instance decPublicCore (P : Model.PolScan) : Decidable (PublicCore P) := by
  unfold PublicCore
  infer_instance

/-- Number k of the list. -/
theorem PublicCore.num {P : Model.PolScan} (A : PublicCore P) (k : ℕ) :
    (coreOf P).getD k 0 = refCore.getD k 0 := by
  rw [A.1]

/-- The two lists are the longer lists' first 41 members. -/
theorem coreOf_eq_take (P : Model.PolScan) : coreOf P = (numsOf P).take 41 := rfl

theorem refCore_eq_take : refCore = refNums.take 41 := rfl

/-- `PublicAt` asks more. -/
theorem core_of_at {P : Model.PolScan} (A : PublicAt P) : PublicCore P :=
  ⟨by rw [coreOf_eq_take, refCore_eq_take, A.1], A.2.1, A.2.2⟩

/-- `PublicAt` is `PublicCore` and the reference's five numbers of the normalisations. -/
theorem at_iff_core (P : Model.PolScan) :
    PublicAt P ↔ PublicCore P ∧ P.h.eps.getD 0 0 = 53687 ∧ P.h.eps.getD 1 0 = 53687 ∧
      P.h.MF = 44 ∧ P.h.KF = 30 ∧ P.h.epsF = 53687 := by
  constructor
  · exact fun A => ⟨core_of_at A, norms_of_at A⟩
  · rintro ⟨⟨c, g, r⟩, e1, e2, e3, e4, e5⟩
    refine ⟨?_, g, r⟩
    have s : numsOf P = coreOf P ++
        [P.h.eps.getD 0 0, P.h.eps.getD 1 0, P.h.MF, P.h.KF, P.h.epsF] := rfl
    rw [s, c, e1, e2, e3, e4, e5]
    rfl

section Core

variable {P : Model.PolScan} (A : PublicCore P)

include A

/-- The layers' switches. -/
theorem switches_of_core : Switches (Model.Verify.layerShape P) where
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
theorem sized_of_core : Sized (Model.Verify.layerShape P) DF where
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
theorem sized2_of_core : Sized2 (Model.Verify.layerShape P) DF := by
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
theorem p4_of_core : (Model.Verify.layerShape P).p4 = true := by
  have e1 : P.h.prof = 4 := A.num 0
  show (P.h.prof == 4) = true
  simp [e1]

/-- The head's sizes are the reference's. -/
theorem fullH_of_core (y : Model.Layer.Lay) : FullH (Model.Verify.headShape P y) where
  lt := A.num 1
  la := A.num 12
  d := A.num 4
  V := A.num 11
  XL := A.num 31
  lmhf := A.num 20
  NHf := A.num 21
  lmhd := A.num 22
  lmhr := A.num 23

end Core

/-- **The public hypotheses on the layers and on the head, from the verifier's own call and the 41
numbers.** -/
theorem public_of_core {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) (A : PublicCore X.P) : LayersHeadAt X := by
  obtain ⟨P, y, hpl, eP, ey, eS, -, hl, -⟩ := public_parts h
  have hy := layerLayout_of_polLayout hpl
  rw [← eP, ← ey] at hy
  rw [← ey] at hl
  have S := switches_of_core A
  have hN := (admitted_of_layout hy S.p3).NGr
  have e1 : X.P.h.L = 48 := A.num 2
  have e2 : X.P.h.ll = 2 := A.num 3
  have eS' : X.hS = Model.Verify.headShape X.P X.y := by rw [eS, eP, ey]
  exact {
    lay := hy
    switches := S
    sized := sized_of_core A
    sized2 := sized2_of_core A
    p4 := p4_of_core A
    groups := by
      rw [hN]
      show X.P.h.L / 2 ^ X.P.h.ll = 12
      rw [e1, e2]
      norm_num
    full := by
      rw [eS']
      exact fullH_of_core A X.y
    head := hl
    sh := by
      rw [eS']
      exact A.num 32
    sT := by
      rw [eS']
      exact A.num 33 }

/-- **Attention's fourteen numbers follow from the 41 numbers and the layers' layout.** -/
theorem fillRef_of_core {X : Model.Verify.Public} (A : PublicCore X.P) (H : LayersHeadAt X) :
    L5.FillRef X.P X.y := by
  have eh : X.y.h = Model.Verify.layerShape X.P := (admitted_of_layout H.lay H.switches.p3).shape
  have L2 := laid2_of_layout H.lay
  have e1 : X.P.h.lt = 10 := A.num 1
  have e2 : X.P.h.lmq = 16 := A.num 18
  have e3 : X.P.h.dh = 128 := A.num 7
  have a7 : X.P.h.NAs = 1 := A.num 40
  exact {
    lt := e1
    lB := A.num 34
    H := A.num 5
    Gk := A.num 6
    ll := A.num 3
    Sx := A.num 35
    rx := A.num 36
    lmS := A.num 37
    lmh := A.num 38
    lmo := A.num 39
    NAs := by
      rw [a7]
      exact Nat.one_pos
    ldh := by
      rw [ldh_of_layout H.lay]
      show ceilLog2 X.P.h.dh = 7
      rw [e3]
      exact ceilLog2_128
    T := by
      rw [L2.T, eh]
      show 2 ^ X.P.h.lt = 1024
      rw [e1]
      norm_num
    mrow := by
      rw [L2.mrow3, eh]
      show 2 ^ X.P.h.lmq = 65536
      rw [e2]
      norm_num }

/-- **All eleven public hypotheses, from the verifier's own call and the 41 numbers.** nf: any
numbers of the final normalisation; the table of scales is made of the scale file's words and of nf.
The last clause, on the width of attention's matrix of weights, is asked only where the bundle of
statements is shown to have a value. -/
theorem eleven_of_core {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : Model.Verify.publicOf pol KL lay = .ok X) (A : PublicCore X.P) (nf : NormPar) :
    LayersHeadAt X ∧ (∀ g, g < 12 → L5.AttSized (shapeA X g)) ∧
      (∀ g, g < 12 →
        ((scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf).kap (4 * g)).sh =
          (shapeA X g).cf.sh.getD 0 0) ∧
      (∀ g, g < 12 → ∀ ι : ℕ, ι < (shapeA X g).u0 →
        (((shapeA X g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) ∧
      ∀ g, g < 12 → 7200 ≤ (shapeA X g).kAs / (shapeA X g).cf.NAs * (shapeA X g).cf.NAs := by
  have H := public_of_core h A
  have F := fillRef_of_core A H
  have K : ∀ g, g < 12 → _ := fun g hg =>
    L5.att_public h H.p4 F (by rw [H.groups]; exact hg) hg (Model.Verify.layerShape X.P) nf
  exact ⟨H, fun g hg => (K g hg).1, fun g hg => (K g hg).2.1, fun g hg => (K g hg).2.2.1,
    fun g hg => (K g hg).2.2.2⟩

#print axioms at_iff_core
#print axioms public_of_core
#print axioms fillRef_of_core
#print axioms eleven_of_core

end OnBytes.Road.Hd
