-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Lane5AttAddr.lean

At the reference sizes the rule of addresses for the cells of an attention sub-proof that is written
after the verifier's forms ("addrA", Johnson/Road/Lane5AttDef.lean: a definition of ours; that it is
the program's rule is shown by no theorem) is the library's (Inst.Model.AttSeg.addr,
Inst/Model/Att/Trace.lean), and the sizes made from the verifier's shape are the library's.

* "AttSized S": the numbers of the verifier's shape S that the two definitions read are the
  reference numbers. The number NAs of parts of the matrix "as" and the number kAs of its columns
  are left free.
* "portOf S": a matrix, row and column of the library, as number in the verifier's list, row and
  column.
* "dimOf_ref": dimOf S is the library's reference sizes with S.u0 live rows.
* "addrA_ref": addrA S c = portOf S (the library's address of c), for ALL names c, valid or not.

What is compared with what: a definition of ours (addrA), written by a reading of the verifier's
forms, with the library's address map. Not here: that a shape which the verifier derives meets
AttSized (from the verifier's own calls and numbers of the parameter file:
Johnson/Road/Lane5AttShape.lean, Johnson/Road/Lane5AttPub.lean).

Files named above that a package may lack. Johnson/Road/Lane5AttPub.lean and
Johnson/Road/Lane5AttShape.lean (and Johnson/Road/Lane5AttBack.lean, named further down) are in the
library's full tree and are not imported by this file; a package that is cut to what its front
theorems need may not hold them. Where they lack, what this comment says of them cannot be checked
there.

-/
import Johnson.Road.Lane5AttDef
import Inst.Model.All.Addr
import Inst.Model.Scales

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model.All (DA KA)
open Inst.Model

/-- **The verifier's shape has the reference numbers.** NAs and kAs are free: asCell, portOf and
attMx read both, and the theorems on the way from the list to the library's matrices hold at every
value of them. The way back asks that the parts of "as" have together at least 7,200 columns
(Johnson/Road/Lane5AttBack.lean: hw). -/
structure AttSized (S : Attention.Shape) : Prop where
  lgk : S.cf.lgk = 3
  lnT : S.lnT = 4
  lB : S.cf.lB = 6
  ldh : S.cf.ldh = 7
  HA : S.HA = 5
  Lam : S.Lam = 4
  lt : S.cf.lt = 10
  H : S.cf.H = 40
  T : S.T = 1024
  dh : S.dh = 128
  dq : S.dq = 5120
  nM : S.nM = 22
  nD : S.nD = 19
  lmS : S.cf.lmS = 16
  wcH : S.cf.wcH = 8
  wcO : S.cf.wcO = 64
  wcQ : S.cf.wcQ = 64
  oMr : S.oMr = 0
  oZr : S.oZr = 640
  oIb : S.oIb = 1280
  oRh : S.oRh = 0
  oRhp : S.oRhp = 20480
  atQ : S.atQ = ⟨0, 2, 4, 5120⟩
  atK : S.atK = ⟨40960, 2, 4, 1024⟩
  atV : S.atV = ⟨49152, 2, 4, 1024⟩
  atO : S.atO = ⟨57344, 2, 4, 5120⟩
  u0 : S.u0 = 2307

/-- A matrix of the library with a row and a column, as number in the verifier's list, row and
column. The library's matrix "as" is one matrix; the verifier's list has it in parts of kAs / NAs
columns. -/
def portOf (S : Attention.Shape) (a : AttSeg.Mx × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  match a.1 with
  | .as => (a.2.2 / (S.kAs / S.cf.NAs), a.2.1, a.2.2 % (S.kAs / S.cf.NAs))
  | .ah => (S.cf.NAs, a.2.1, a.2.2)
  | .ao => (S.cf.NAs + 1, a.2.1, a.2.2)
  | .b => (S.cf.NAs + 2, a.2.1, a.2.2)
  | .qa => (S.cf.NAs + 3, a.2.1, a.2.2)

variable {S : Attention.Shape}

/-- **The sizes are the library's reference sizes**, with the verifier's number of live rows. -/
theorem dimOf_ref (hS : AttSized S) : dimOf S = AttSeg.Dim.refK S.u0 := by
  unfold dimOf
  rw [hS.lgk, hS.lnT, hS.lB, hS.ldh, hS.HA, hS.Lam]
  rfl

/-! ## The matrix "as" -/

theorem asCell_ref (hS : AttSized S) (n : ℕ) :
    asCell S n = portOf S (.as, AttSeg.asAt DA KA n) := by
  unfold asCell
  rw [hS.lmS]
  rfl

theorem pair_eq (jj b : ℕ) : (jj * 4 + b / 5) * 5 + b % 5 = 20 * jj + b := by omega

theorem num_M (hS : AttSized S) (jj b x : ℕ) :
    ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nM + x =
      (DA.nb * jj + b) * 2 ^ DA.lM + x := by
  rw [hS.Lam, hS.HA, hS.nM]
  show ((jj * 4 + b / 5) * 5 + b % 5) * 2 ^ 22 + x = (20 * jj + b) * 2 ^ 22 + x
  rw [pair_eq]

theorem num_D (hS : AttSized S) (jj b x : ℕ) :
    5 * S.Lam * S.HA * 2 ^ S.nM + ((jj * S.Lam + b / S.HA) * S.HA + b % S.HA) * 2 ^ S.nD + x =
      5 * DA.nb * 2 ^ DA.lM + (DA.nb * jj + b) * 2 ^ DA.lD + x := by
  rw [hS.Lam, hS.HA, hS.nM, hS.nD]
  show 5 * 4 * 5 * 2 ^ 22 + ((jj * 4 + b / 5) * 5 + b % 5) * 2 ^ 19 + x =
    5 * 20 * 2 ^ 22 + (20 * jj + b) * 2 ^ 19 + x
  rw [pair_eq]

/-! ## Features -/

theorem feat_ref (hS : AttSized S) {wc f φ φ' : ℕ} (a i : ℕ) (hw : wc = 2 ^ f) (hφ : φ = φ') :
    featCell S a wc φ i = (a, φ' % 2 ^ f * DA.T + i, φ' / 2 ^ f) := by
  subst hw hφ
  unfold featCell
  rw [hS.T]
  rfl

theorem phi_mx (hS : AttSized S) (k b g : ℕ) :
    S.oMr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA) =
      DA.nH * (DA.nl * k + DA.lamOf b) + DA.head g b := by
  rw [hS.oMr, hS.Lam, hS.HA, hS.H]
  show 0 + (k * 4 + b / 5) * 40 + (g * 5 + b % 5) = 40 * (4 * k + b / 5) + (5 * g + b % 5)
  omega

theorem phi_den (hS : AttSized S) (k b g : ℕ) :
    S.oZr + (k * S.Lam + b / S.HA) * S.cf.H + (g * S.HA + b % S.HA) =
      4 * DA.nl * DA.nH + DA.nH * (DA.nl * k + DA.lamOf b) + DA.head g b := by
  rw [hS.oZr, hS.Lam, hS.HA, hS.H]
  show 640 + (k * 4 + b / 5) * 40 + (g * 5 + b % 5) =
    4 * 4 * 40 + 40 * (4 * k + b / 5) + (5 * g + b % 5)
  omega

theorem phi_ib (hS : AttSized S) (k b g : ℕ) :
    S.oIb + (0 * S.Lam + b / S.HA) * (S.cf.lt * S.cf.H) + (k * S.cf.H + g * S.HA + b % S.HA) =
      8 * DA.nl * DA.nH + DA.lT * DA.nH * DA.lamOf b + DA.nH * k + DA.head g b := by
  rw [hS.oIb, hS.Lam, hS.HA, hS.lt, hS.H]
  show 1280 + (0 * 4 + b / 5) * (10 * 40) + (k * 40 + g * 5 + b % 5) =
    8 * 4 * 40 + 10 * 40 * (b / 5) + 40 * k + (5 * g + b % 5)
  omega

theorem phi_qh (hS : AttSized S) (b g n : ℕ) :
    Model.tenCell (Attention.atRh S) 0 (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n =
      DA.nH * DA.ch * DA.lamOf b + DA.ch * DA.head g b + n := by
  show S.oRh + (0 * S.Lam + b / S.HA) * S.dq + (g * S.HA + b % S.HA) * S.dh + n = _
  rw [hS.oRh, hS.Lam, hS.HA, hS.dq, hS.dh]
  show 0 + (0 * 4 + b / 5) * 5120 + (g * 5 + b % 5) * 128 + n =
    40 * 128 * (b / 5) + 128 * (5 * g + b % 5) + n
  omega

theorem phi_qh' (hS : AttSized S) (b g n : ℕ) :
    Model.tenCell (Attention.atRhp S) 0 (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n =
      DA.nl * DA.nH * DA.ch + DA.nH * DA.ch * DA.lamOf b + DA.ch * DA.head g b + n := by
  show S.oRhp + (0 * S.Lam + b / S.HA) * S.dq + (g * S.HA + b % S.HA) * S.dh + n = _
  rw [hS.oRhp, hS.Lam, hS.HA, hS.dq, hS.dh]
  show 20480 + (0 * 4 + b / 5) * 5120 + (g * 5 + b % 5) * 128 + n =
    4 * 40 * 128 + 40 * 128 * (b / 5) + 128 * (5 * g + b % 5) + n
  omega

theorem phi_qry (hS : AttSized S) (k b g n : ℕ) :
    Model.tenCell S.atQ k (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n =
      DA.nH * DA.ch * (DA.nl * k + DA.lamOf b) + DA.ch * DA.head g b + n := by
  rw [hS.atQ, hS.HA, hS.dh]
  show 0 + (k * 4 + b / 5) * 5120 + (g * 5 + b % 5) * 128 + n =
    40 * 128 * (4 * k + b / 5) + 128 * (5 * g + b % 5) + n
  omega

theorem phi_out (hS : AttSized S) (k b g n : ℕ) :
    Model.tenCell S.atO k (b / S.HA) ((g * S.HA + b % S.HA) * S.dh) + n =
      2 * DA.nl * DA.nH * DA.ch + 4 * DA.nl * DA.nG * DA.ch +
        DA.nH * DA.ch * (DA.nl * k + DA.lamOf b) + DA.ch * DA.head g b + n := by
  rw [hS.atO, hS.HA, hS.dh]
  show 57344 + (k * 4 + b / 5) * 5120 + (g * 5 + b % 5) * 128 + n =
    2 * 4 * 40 * 128 + 4 * 4 * 8 * 128 + 40 * 128 * (4 * k + b / 5) + 128 * (5 * g + b % 5) + n
  omega

theorem phi_key (hS : AttSized S) (k lam g n : ℕ) :
    Model.tenCell S.atK k lam (g * S.dh) + n =
      2 * DA.nl * DA.nH * DA.ch + DA.nG * DA.ch * (DA.nl * k + lam) + DA.ch * g + n := by
  rw [hS.atK, hS.dh]
  show 40960 + (k * 4 + lam) * 1024 + g * 128 + n =
    2 * 4 * 40 * 128 + 8 * 128 * (4 * k + lam) + 128 * g + n
  omega

theorem phi_val (hS : AttSized S) (k lam g n : ℕ) :
    Model.tenCell S.atV k lam (g * S.dh) + n =
      2 * DA.nl * DA.nH * DA.ch + 2 * DA.nl * DA.nG * DA.ch +
        DA.nG * DA.ch * (DA.nl * k + lam) + DA.ch * g + n := by
  rw [hS.atV, hS.dh]
  show 49152 + (k * 4 + lam) * 1024 + g * 128 + n =
    2 * 4 * 40 * 128 + 2 * 4 * 8 * 128 + 8 * 128 * (4 * k + lam) + 128 * g + n
  omega

theorem w8 : (8 : ℕ) = 2 ^ 3 := by norm_num
theorem w64 : (64 : ℕ) = 2 ^ 6 := by norm_num

/-- **At the reference sizes addrA, the rule of addresses written after the verifier's forms, is the
library's**, at every name. That addrA is the program's rule is shown by no theorem. -/
theorem addrA_ref (hS : AttSized S) :
    ∀ c : AttSeg.Raw, addrA S c = portOf S (AttSeg.addr DA KA c)
  | .c .M jj b x => (congrArg (asCell S) (num_M hS jj b x)).trans (asCell_ref hS _)
  | .c .D jj b x => (congrArg (asCell S) (num_D hS jj b x)).trans (asCell_ref hS _)
  | .mx k b g i => feat_ref hS (f := 3) _ i (hS.wcH.trans w8) (phi_mx hS k b g)
  | .den k b g i => feat_ref hS (f := 3) _ i (hS.wcH.trans w8) (phi_den hS k b g)
  | .ib k b g i => feat_ref hS (f := 3) _ i (hS.wcH.trans w8) (phi_ib hS k b g)
  | .qh b g i n => feat_ref hS (f := 6) _ i (hS.wcO.trans w64) (phi_qh hS b g n)
  | .qh' b g i n => feat_ref hS (f := 6) _ i (hS.wcO.trans w64) (phi_qh' hS b g n)
  | .qry k b g i n => feat_ref hS (f := 6) _ i (hS.wcQ.trans w64) (phi_qry hS k b g n)
  | .out k b g i n => feat_ref hS (f := 6) _ i (hS.wcQ.trans w64) (phi_out hS k b g n)
  | .key k lam g j n => feat_ref hS (f := 6) _ j (hS.wcQ.trans w64) (phi_key hS k lam g n)
  | .val k lam g j n => feat_ref hS (f := 6) _ j (hS.wcQ.trans w64) (phi_val hS k lam g n)

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.dimOf_ref
#print axioms OnBytes.Road.L5.addrA_ref
