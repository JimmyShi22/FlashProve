-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K11Caller/HeadSays.lean: what the head's one claim on the weights says at the typed record G, in the library's own output matrix.

Prog.lean: claim a of the record G says: OnBytes.Road.claimVal + (its mask entry) * be = sh. Johnson/Road/HeadWeight.lean (claimVal_head): at the reference parameters, claimVal of the head's claim
(the layout's last unit; a vector AV on the vocabulary; the equality weights of 13 coordinates rs on the channels) is the sum over the vocabulary and the channels of AV[v] * eq(rs, k) * Hof W k v,
Hof W the library's reading of the output matrix in W (Inst/Model/Head/Trace.lean). Joined:
    G_head_says   the typed claim at the head's place holds  ⇔  that sum, at the cells of W among the entries, + (the mask entry) * be = sh
    G_head_says_idx   the same with the output matrix of an index i (Cm.Idx: i.index.val.H, integers carried into the field), where the cells hold i's digit matrix, carried
                      (by OnBytes.Road.HeadReq.cast_H_eq_Hof, Johnson/Road/HeadReq.lean, and OnBytes.Road.layout_eq)
The premises: the shape of the weights agrees with the library's reference parameters (SizedW); wsLayOf returns at the library's number of column bits; the claim passes wsClaimShape; the
state's factors are the claim's, read; the reading takes numerals to numbers.
SPENT OF THE LIBRARY: OnBytes.Road.Hd.claimVal_head, units_head (Johnson/Road/HeadWeight.lean) · OnBytes.Road.layout_eq (Johnson/Road/FormsKeysWLay.lean) · OnBytes.Road.HeadReq.cast_H_eq_Hof
(Johnson/Road/HeadReq.lean) · Inst.Model.Head.oH_eq (Inst/Model/Head/Trace.lean): all on pure functions and plain records.
Limits: the full size's parameters alone. An identity: no random step. W is whatever the entries hold at the cells' names: that they hold an index's digits is a premise of G_head_says_idx. The equation is one
between elements of the field: the integers stand in it carried into the field. That a run's claim has this form is OnBytes.Road.Hd.weightsClaim_ok's. On hiding nothing.

-/
import Johnson.Top.H0.K11Caller.Prog
import Johnson.Road.HeadWeight
import Johnson.Road.HeadReq
import Cm.RelBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.K11Caller
open OnBytes
open OnBytes.Model (Reading WsShape WsLay WsClaim wsLayOf wsClaimShape)
open OnBytes.Road (Numerals SizedW eqR)
open OnBytes.Road.Hd (facKK claimVal_head)
open Inst.Model (ppref)
open Inst.Model.Layout (kRef)
open Inst.Model.Head (Hof nV nD oH)
open Finset

variable {E' : Type} [Field E'] [Fintype E'] {ρ : Reading E'}

/-- The head's claim, as weightsClaim makes it at the reference parameters. -/
def headClaim (lay : WsLay) (AV rs : Array E) : WsClaim := { ui := lay.U.size - 1, f := [{ AV := AV }, facKK rs 10 5 13] }

/-- **What the head's claim says at the typed record.** P: a place on a layout out of wsLayOf with one claim, on the last unit. -/
theorem G_head_says (hρ : Numerals ρ) {s : WsShape} (Z : SizedW s ppref) (P : Place) (h : wsLayOf s true kRef = .ok P.lay)
    (a : Fin P.n) (T : Letters E' P) (st : T.St) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (AV rs : Array E) (hs : 13 ≤ rs.size) (ha : cl a = headClaim P.lay AV rs) (F : Fit ρ P T st cl) :
    (G P T).Cl st m a ↔
      ∑ v ∈ range nV, ∑ k ∈ range nD, ρ.val (AV.getD v zeroE) * eqR ρ rs 0 13 k * Hof (Wof P fun rc => m (.inl rc)) k v +
        m (.inr (T.nm a)) * (T.rd st).be a = (T.rd st).sh a := by
  unfold Cb.Pv.Lay.WeightsL.Cl
  rw [G_val_means hρ P T st m cl (ofLay_pos h) F a, ha]
  unfold headClaim
  rw [claimVal_head ρ Z h _ AV rs hs]
  exact Iff.rfl

/-- At the reference parameters the head's unit lies within W, and W has the library's number of column bits. -/
theorem head_rows {s : WsShape} (Z : SizedW s ppref) {lay : WsLay} (h : wsLayOf s true kRef = .ok lay) :
    oH + 10240 ≤ lay.m0 ∧ lay.lk = kRef := by
  obtain ⟨hlk, -, -, H⟩ := OnBytes.Road.layout_eq Z h
  obtain ⟨u, hu, -, -, hoff, hrows, -⟩ := H 385 _ OnBytes.Road.Hd.units_head.2
  have h1 := ofLay_in h 385 u hu
  have e2 : Inst.Model.Layout.rows kRef (Inst.Model.Layout.uH ppref) = 10240 := by decide +kernel
  rw [hoff, hrows, Inst.Model.Head.oH_eq, e2] at h1
  exact ⟨h1, hlk⟩

omit [Fintype E'] in
/-- Where the cells hold the digits of an integer matrix, carried into the field, the library's reading of the output matrix is that of the integer matrix, carried. -/
theorem Hof_Wof (P : Place) (w : P.Cell → E') (Wz : Inst.Model.Mat) (hW : ∀ rc : P.Cell, w rc = ((Wz rc.1.val rc.2.val : ℤ) : E'))
    (hm : oH + 10240 ≤ P.lay.m0) (hl : P.lay.lk = kRef) {k v : ℕ} (hk : k < nD) (hv : v < nV) :
    Hof (Wof P w) k v = Hof (fun r c => ((Wz r c : ℤ) : E')) k v := by
  have hk' : k < 5120 := hk
  have hv' : v < 2 ^ P.lay.lk := by
    rw [hl]
    exact lt_of_lt_of_le hv (by decide)
  unfold Hof Wof
  rw [dif_pos ⟨by omega, hv'⟩, dif_pos ⟨by omega, hv'⟩, hW, hW]

/-- **The same in an index's own output matrix**: where the cells of W among the entries hold the digit matrix of an index i (Cm.Idx), carried into the field. -/
theorem G_head_says_idx (hρ : Numerals ρ) {s : WsShape} (Z : SizedW s ppref) (P : Place) (h : wsLayOf s true kRef = .ok P.lay)
    (a : Fin P.n) (T : Letters E' P) (st : T.St) (m : P.Cell ⊕ T.Jm → E') (cl : Fin P.n → WsClaim)
    (AV rs : Array E) (hs : 13 ≤ rs.size) (ha : cl a = headClaim P.lay AV rs) (F : Fit ρ P T st cl)
    (i : Cm.Idx) (hW : ∀ rc : P.Cell, m (.inl rc) = ((i.mat rc.1.val rc.2.val : ℤ) : E')) :
    (G P T).Cl st m a ↔
      ∑ v ∈ range nV, ∑ k ∈ range nD, ρ.val (AV.getD v zeroE) * eqR ρ rs 0 13 k * ((i.index.val.H k v : ℤ) : E') +
        m (.inr (T.nm a)) * (T.rd st).be a = (T.rd st).sh a := by
  rw [G_head_says hρ Z P h a T st m cl AV rs hs ha F]
  obtain ⟨hm, hl⟩ := head_rows Z h
  have e : ∀ v ∈ range nV, ∀ k ∈ range nD, Hof (Wof P fun rc => m (.inl rc)) k v = ((i.index.val.H k v : ℤ) : E') := by
    intro v hv k hk
    rw [Hof_Wof P _ i.mat hW hm hl (mem_range.mp hk) (mem_range.mp hv)]
    exact (OnBytes.Road.HeadReq.cast_H_eq_Hof i.mat (mem_range.mp hk) (mem_range.mp hv)).symm
  rw [sum_congr rfl fun v hv => sum_congr rfl fun k hk => by rw [e v hv k hk]]

end VerifiableInference.Desc.First.K11Caller

#print axioms VerifiableInference.Desc.First.K11Caller.G_head_says_idx
#print axioms VerifiableInference.Desc.First.K11Caller.G_head_says
