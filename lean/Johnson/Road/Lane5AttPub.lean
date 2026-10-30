-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttPub.lean

Attention's public hypotheses from the public part of the verifier's stage: if publicOf
(OnBytes/Model/VerifyPublic.lean) returns X, at profile 4, and thirteen numbers of the parameter
file and of the layers' layout are the reference numbers and NAs is at least 1, then for every group
g the shape in the attention plan X.A[g] has all that "linkA_of_ord"
(Johnson/Road/Lane5AttLink.lean) and the way back (Johnson/Road/Lane5AttBack.lean) ask of a shape,
and the plan's own list has the copy of qa under the label that the layers' formula gives.

* "fill_eq": what the verifier's function fill returns, field by field.
* "FillRef P y": these fourteen conditions.
* "cfRef_of_fill": they give CfRef, S = 12, rx = 8 and at least one part of "as".
* "att_public": AttSized; the tie of the shift to the table scalesOf of the verifier's file of
  scales; the tie of the table of exponentials to the library's; the width of "as".
* "label_public": the label of number NAs + 3 in the list of X.A[g].
* "linkA_of_public": link 2 g + 1 is in order, with no public hypothesis but publicOf's call, the
  profile, the fourteen conditions and the number of groups.

Over "groups_of_public" (Johnson/Road/HeadL5Grp.lean): each plan X.A[g] is a value of group, but for
one record of its seam.

Not claimed: that the group has one shift (AttFit.one): it is no test of publicOf; that a parameter
file meets the fourteen conditions.
-/
import Johnson.Road.Lane5AttPort2
import Johnson.Road.Lane5AttLabel
import Johnson.Road.Lane5AttOwn
import Johnson.Road.HeadL5Grp

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model
open OnBytes.Model.Layer (matIx)

section Fill

variable {P : Model.PolScan} {y : Model.Layer.Lay} {sc : Model.Layer.Scales}
  {lines : List Attention.Line} {g : ℕ} {cf : Attention.Cfg}

/-- **What fill returns.** -/
theorem fill_eq (hf : Attention.fill P y sc lines g = Except.ok cf) :
    cf = { lt := P.h.lt, lB := P.h.lB, H := P.h.H, lgk := Model.clog2 P.h.Gk, ldh := y.ldh,
           ll := P.h.ll, S := P.h.Sx, rx := P.h.rx, kFD := P.h.kFD, lmS := P.h.lmS, la := P.h.la,
           lmb := P.h.lmbA, nmin := P.h.nmin, NAs := P.h.NAs, wcH := 2 ^ P.h.lmh / y.T,
           wcO := 2 ^ P.h.lmo / y.T, wcQ := y.mrow.getD 3 0 / y.T, Ty := 2 ^ (1 + Model.lbz),
           lines := lines,
           sh := (Array.range y.Lam).map fun lam => sc.klSh (g * y.Lam + lam) } := by
  unfold Attention.fill at hf
  obtain ⟨_, _, hf⟩ := bind_ok hf
  obtain ⟨_, _, hf⟩ := bind_ok hf
  exact (Except.ok.inj hf).symm

/-- Fourteen numbers of the parameter file as read and of the layers' layout. -/
structure FillRef (P : Model.PolScan) (y : Model.Layer.Lay) : Prop where
  lt : P.h.lt = 10
  lB : P.h.lB = 6
  H : P.h.H = 40
  Gk : P.h.Gk = 8
  ll : P.h.ll = 2
  Sx : P.h.Sx = 12
  rx : P.h.rx = 8
  lmS : P.h.lmS = 16
  lmh : P.h.lmh = 13
  lmo : P.h.lmo = 16
  NAs : 0 < P.h.NAs
  ldh : y.ldh = 7
  T : y.T = 1024
  mrow : y.mrow.getD 3 0 = 65536

theorem clog2_8 : Model.clog2 8 = 3 := by decide +kernel

/-- The configuration that fill returns has the reference numbers. -/
theorem cfRef_of_fill (hf : Attention.fill P y sc lines g = Except.ok cf) (F : FillRef P y) :
    CfRef cf ∧ cf.S = 12 ∧ cf.rx = 8 ∧ 0 < cf.NAs := by
  have e := fill_eq hf
  subst e
  refine ⟨⟨F.lt, F.lB, ?_, F.ldh, F.ll, F.H, F.lmS, ?_, ?_, ?_⟩, F.Sx, F.rx, F.NAs⟩
  · show Model.clog2 P.h.Gk = 3
    rw [F.Gk]
    exact clog2_8
  · show 2 ^ P.h.lmh / y.T = 8
    simp [F.lmh, F.T]
  · show 2 ^ P.h.lmo / y.T = 64
    simp [F.lmo, F.T]
  · show y.mrow.getD 3 0 / y.T = 64
    simp [F.mrow, F.T]

end Fill

section Public

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **Attention's public hypotheses, at the shape of the plan X.A[g].** -/
theorem att_public (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) (F : FillRef X.P X.y) {g : ℕ}
    (hg : g < X.y.NGr) (hg12 : g < 12) (hL : Model.Layer.Shape) (nf : NormPar) :
    AttSized (Hd.shapeA X g) ∧
      ((scalesOf hL X.layers.sc nf).kap (4 * g)).sh = (Hd.shapeA X g).cf.sh.getD 0 0 ∧
      (∀ ι : ℕ, ι < (Hd.shapeA X g).u0 →
        (((Hd.shapeA X g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) ∧
      7200 ≤ (Hd.shapeA X g).kAs / (Hd.shapeA X g).cf.NAs * (Hd.shapeA X g).cf.NAs := by
  obtain ⟨lines, A0, seenG, seenA, -, H⟩ := Hd.groups_of_public h hp4
  obtain ⟨Xg, Ag, s, hG, -, -, -, -, -, -, -, eS⟩ := H g hg
  rw [eS]
  obtain ⟨cf, hf, Sh, hLam, -⟩ := shaped_of_group hG
  obtain ⟨hc, h12, h8, hN⟩ := cfRef_of_fill hf F
  obtain ⟨hu, hE⟩ := exp_of_shaped Sh h12 h8
  have hS := sized_of_shaped Sh hc hu
  refine ⟨hS, ?_, hE, wide_of_shaped Sh hc hN⟩
  rw [Sh.cfg]
  exact hsh_of_fill hf (hLam.symm.trans hS.Lam) hg12 hL nf

/-- **In the list of the plan X.A[g] the copy of qa bears the label that the layers' formula gives
the matrix qa of group g.** -/
theorem label_public (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) {g : ℕ} (hg : g < X.y.NGr) :
    ∃ Ag, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      (Ag.seam.tl.mats[Ag.S.cf.NAs + 3]?).map (fun M => M.aId) =
        some (labA X.y g (matIx X.y).iQA) := by
  obtain ⟨lines, A0, seenG, seenA, hO, H⟩ := Hd.groups_of_public h hp4
  obtain ⟨Xg, Ag, s, hG, h0, hs, hA, eAS, -, -, etl, eS⟩ := H g hg
  refine ⟨Ag, hA, eAS.trans eS.symm, ?_⟩
  rw [etl, owners_plan hO h0 hs, eAS]
  exact group_label_qa hG hg

/-- **Link 2 g + 1 is in order, from the public part of the verifier's stage.** -/
theorem linkA_of_public (h : Model.Verify.publicOf pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) (F : FillRef X.P X.y) {g : ℕ}
    (hg : g < X.y.NGr) (hg12 : g < 12) (hL : Model.Layer.Shape) (nf : NormPar) {Z : Zs}
    (O : AttOrd (Hd.shapeA X g) Z) (Wz : Mat) (x : Instance ppref) :
    LinkOK Cm.Seg.Hd.plain (Cm.Seg.TS.segM (scalesOf hL X.layers.sc nf)) Wz x (2 * g + 1)
      (attMx (Hd.shapeA X g) g Z) := by
  obtain ⟨hS, hsh, hE, -⟩ := att_public h hp4 F hg hg12 hL nf
  exact linkA_of_ord hg12 hS hsh hE O Wz x

end Public

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.cfRef_of_fill
#print axioms OnBytes.Road.L5.att_public
#print axioms OnBytes.Road.L5.label_public
#print axioms OnBytes.Road.L5.linkA_of_public
