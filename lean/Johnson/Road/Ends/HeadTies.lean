-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Ends/HeadTies.lean: the record TiesH (Johnson/Road/Ends/HeadSeg.lean) at the reading of
names in integer matrices: the matrices Mh behind the head's sub-proof and the committed matrix Wz.

Definitions: readH Mh Wz (a name's cell, carried into the extension field); pubH R b lay (what is
public at the head's lookup, from a run's record R, the record b of the stream's matrix and the
layout lay of the committed weights).
Main theorems:
  read_cellAt: the cell of a feature at a position by H.cellAt is the cell by cellIn
    (Johnson/Road/HeadPlace.lean): two texts of one rule.
  wH_read: for a shape of the weights that agrees with the library's reference parameters and a
    layout that wsLayOf returns with the library's number of column bits: the weight H[k][v] that
    H.wH spells from the digits in Wz is the library's (Layout.weightsOf ppref kRef Wz).H k v.
  tiesH_of: TiesH at the library's sizes, at the cells cellsH R.h R.L b Mh and that output matrix,
    under the head's records Laid and ReqFits (Johnson/Road/HeadLines.lean), numbers of the shape
    and of b, "every checked token is below the vocabulary's size", and the equation on the weights
    that wH_read concludes (a premise here: the caller brings it).

Limits: nothing on a table, a call, a form or a protocol. The reference sizes.

-/
import Johnson.Road.HeadPlace
import Johnson.Road.HeadWeight
import Johnson.Road.HeadReq
import Johnson.Road.Ends.AlgWcell
import Johnson.Road.Ends.HeadSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Finset
open OnBytes.Ends
open OnBytes.Model (WsLay WsShape wsLayOf)
open OnBytes.Model.Head (Border)
open Inst.Model (NormPar Mat ppref)
open Inst.Model.Layout (kRef units uH)

/-- A name's cell in the integer matrices, carried into the extension field. -/
def readH (Mh : Mats ℤ) (Wz : Mat) : H.NameH → Cb.Gl.E
  | .cell m r c => ((Mh m r c : ℤ) : Cb.Gl.E)
  | .w r c => ((Wz r c : ℤ) : Cb.Gl.E)

/-- What is public at the head's lookup. -/
def pubH (R : Model.Head.Run) (b : Border) (lay : WsLay) : H.PubH :=
  ⟨R.h, R.L, b, R.cov, R.x.win, lay⟩

/-- Two texts of one rule. -/
theorem read_cellAt (Mh : Mats ℤ) (Wz : Mat) (M0 m k T F t : ℕ) :
    readH Mh Wz (H.cellAt M0 m k T F t) = ((cellIn Mh M0 k (m / T) T F t : ℤ) : Cb.Gl.E) := by
  have e : F / (k * (m / T)) = F / (m / T) / k := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
  show ((Mh (M0 + F / (k * (m / T))) (F % (m / T) * T + t) (F / (m / T) % k) : ℤ) : Cb.Gl.E) = _
  rw [e]
  rfl

/-- **The weight from its digits is the library's.** -/
theorem wH_read {s : WsShape} (Z : SizedW s ppref) {lay : WsLay}
    (h : wsLayOf s true kRef = .ok lay) (R : Model.Head.Run) (b : Border) (Mh : Mats ℤ) (Wz : Mat)
    {k v : ℕ} (hk : k < Inst.Model.Head.nD) (hv : v < Inst.Model.Head.nV) :
    H.wH (pubH R b lay) (readH Mh Wz) k v =
      (((Inst.Model.Layout.weightsOf ppref kRef Wz).H k v : ℤ) : Cb.Gl.E) := by
  obtain ⟨-, hsz, -, hall⟩ := layout_eq Z h
  have hsz' : lay.U.size = 386 := hsz.trans units_head.1
  obtain ⟨u, hu, hok, hnl, -, -, -, -, -, hcell⟩ := hall 385 (uH ppref) units_head.2
  have hget : lay.U.getD (lay.U.size - 1) default = u := by
    rw [hsz']
    show lay.U.getD 385 default = u
    rw [Array.getD_eq_getD_getElem?, hu]
    rfl
  have e0 : H.wH (pubH R b lay) (readH Mh Wz) k v =
      (List.range u.nlw).foldl (fun a δ => a + (256 : Cb.Gl.E) ^ δ *
        readH Mh Wz (.w (H.wcell u δ [v, k]).1 (H.wcell u δ [v, k]).2)) 0 := by
    have hget' : (pubH R b lay).lay.U.getD ((pubH R b lay).lay.U.size - 1) default = u := hget
    unfold H.wH
    simp only [hget']
  rw [e0, foldl_sum (fun δ => (256 : Cb.Gl.E) ^ δ *
    readH Mh Wz (.w (H.wcell u δ [v, k]).1 (H.wcell u δ [v, k]).2)) u.nlw, hnl,
    HeadReq.cast_H_eq_Hof Wz hk hv, ← entryW_Hof]
  unfold Inst.Model.entryW
  refine sum_congr rfl fun δ _ => ?_
  rw [Alg.wcell_eq_cellOf hok.grp, hcell]
  rfl

/-- **The record, at the reading in integer matrices.** -/
theorem tiesH_of {R : Model.Head.Run} {b : Border} {lay : WsLay} {Mh : Mats ℤ} {Wz : Mat}
    {np : NormPar} {y : Inst.Model.Head.Req} (La : Laid R HeadSizes.ref)
    (Rq : ReqFits R HeadSizes.ref y) (hXL : R.h.XL = 5) (hKF : R.h.KF = np.K)
    (hsh : R.h.digSh = 8) (hnl : b.nl = 5) (hwin : ∀ i, y.win i < 202048)
    (hW : ∀ k v, k < 5120 → v < 202048 → H.wH (pubH R b lay) (readH Mh Wz) k v =
      (((Inst.Model.Layout.weightsOf ppref kRef Wz).H k v : ℤ) : Cb.Gl.E)) :
    TiesH (pubH R b lay) (readH Mh Wz) HeadSizes.ref np ((cellsH R.h R.L b Mh).cast Cb.Gl.E)
      (fun j v => (((Inst.Model.Layout.weightsOf ppref kRef Wz).H j v : ℤ) : Cb.Gl.E)) y where
  hf := fun φ i => read_cellAt Mh Wz 0 R.L.m R.L.k R.h.T φ i
  hd := fun φ i => read_cellAt Mh Wz R.h.NHf R.L.mD R.L.kD R.h.T φ i
  hr := fun φ i => read_cellAt Mh Wz (R.h.NHf + 1) R.L.mR R.L.kR R.h.T φ i
  x := fun l k i _ hk => by
    have hd : R.h.d = 5120 := La.d
    have hk' : k < 5120 := hk
    have e1 : (5120 * l + k) / R.h.d = l := by
      rw [hd, Nat.mul_add_div (by norm_num), Nat.div_eq_of_lt hk', Nat.add_zero]
    have e2 : (5120 * l + k) % R.h.d = k := by
      rw [hd, Nat.mul_add_mod, Nat.mod_eq_of_lt hk']
    refine (read_cellAt Mh Wz (R.h.NHf + 3) b.mxb b.kxb R.h.T (b.cell l k) i).trans ?_
    show _ = ((cellIn Mh (R.h.NHf + 3) b.kxb (b.mxb / R.h.T) R.h.T
      (b.cell ((5120 * l + k) / R.h.d) ((5120 * l + k) % R.h.d)) i : ℤ) : Cb.Gl.E)
    rw [e1, e2]
  d := La.d
  JV := La.JV
  JVa := La.JVa
  Va := by decide
  oAw := La.oAw
  oRa := La.oRa
  oD1 := La.oD1
  oD2 := La.oD2
  oE := La.oE
  nl := hnl
  XL := hXL
  KF := hKF
  sh := hsh
  w := hW
  rho := fun v i hv hi => by
    have hV : v < R.h.V := by rw [La.V]; exact hv
    show (H.ind (R.cov.hOn.getD i false && decide (v < R.h.V)) : Cb.Gl.E) = _
    rw [Rq.rho i hi]
    unfold H.ind
    by_cases hon : R.cov.hOn.getD i false = true <;> simp [hon, hV]
  cnt := fun v i hv hi => by
    have hV : v < R.h.V := by rw [La.V]; exact hv
    show (H.ind (decide (v < R.h.V) && R.cov.hOnC.getD i false) : Cb.Gl.E) = _
    rw [Rq.rhoC i hi]
    unfold H.ind
    by_cases hon : R.cov.hOnC.getD i false = true <;> simp [hon, hV]
  win := fun i hi hon => (Rq.win i hi hon).symm
  winV := hwin

end OnBytes.Road.Hd

#print axioms OnBytes.Road.Hd.read_cellAt
#print axioms OnBytes.Road.Hd.wH_read
#print axioms OnBytes.Road.Hd.tiesH_of
