-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5B.lean: "the head's link is in order" with the bound asked inside the matrices'
own rows and columns alone.

HeadOrd (Johnson/Road/HeadL5.lean) asks that every entry Mh a r c is small: for every number a, row
r and column c, also where the head's list has no matrix or a matrix has no entry. Here the bound is
SmallH: it speaks of the four parts of hf, of hd, of hr and of the head's copy of the stream, inside
the rows and columns that the layout gives them. The matrix of the lookup's counts, number NHf + 2
of the list, holds no cell, and nothing is asked of it. With that bound the statement still gives
LinkOK (Johnson/Road/Lane5.lean) at link 24. The head with the cost ledger is in
Johnson/Road/HeadL5BL.lean.

Main definitions: SmallH; HeadOrdB.
Main theorems: small_24 (an own cell of segment 24 stands inside a matrix of the list); linkOK_24B;
ordB_of_ord (HeadOrd gives HeadOrdB).

What is not claimed. As in Johnson/Road/HeadL5.lean. From LinkOK at link 24 SmallH does not follow:
the last part of hf has entries that are no cells, and LinkOK's bound does not speak of the copy of
the stream. The program does not import this file.
-/
import Johnson.Road.HeadL5
import Johnson.Road.Lane5

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat)
open Inst.Model.Head (nT)
open Inst.Model.All (DF)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL Border)
open OnBytes.Model.Verify (borderOf)

/-- Every entry of the matrices of the head's list that hold cells is below 2^18 in absolute value,
inside the rows and columns that the layout L and the stream's record b give: the parts of hf, hd,
hr, and the copy of the stream. -/
def SmallH (h : Model.Head.Shape) (L : HL) (b : Border) (Mh : Mats ℤ) : Prop :=
  (∀ a < h.NHf, ∀ r < L.m, ∀ c < L.k, |Mh a r c| < 2 ^ 18) ∧
  (∀ r < L.mD, ∀ c < L.kD, |Mh h.NHf r c| < 2 ^ 18) ∧
  (∀ r < L.mR, ∀ c < L.kR, |Mh (h.NHf + 1) r c| < 2 ^ 18) ∧
  ∀ r < b.mxb, ∀ c < b.kxb, |Mh (h.NHf + 3) r c| < 2 ^ 18

/-- The bound at all numbers, rows and columns gives it. -/
theorem smallH_of_all {h : Model.Head.Shape} {L : HL} {b : Border} {Mh : Mats ℤ}
    (small : ∀ a r c, |Mh a r c| < 2 ^ 18) : SmallH h L b Mh :=
  ⟨fun _ _ _ _ _ _ => small _ _ _, fun _ _ _ _ => small _ _ _, fun _ _ _ _ => small _ _ _,
    fun _ _ _ _ => small _ _ _⟩

/-- **An own cell of segment 24 stands inside a matrix of the head's list**: under SmallH it is
small. hd: the library's shape of the head, with no more features than the matrices hold. -/
theorem small_24 {h : Model.Head.Shape} {L : HL} {b : Border} (N : NumH h L) (Bd : BorderH b)
    {hd : Cm.Seg.Hd} (hOK : hd.OK) (y : Lay) {Mh : Mats ℤ} (Sm : SmallH h L b Mh)
    (n : Cm.Seg.Name) (hv : n.Valid hd) (hk : n.place.1 = 24) :
    |Cm.Seg.at' (headMx h y Mh) n.place| < 2 ^ 18 := by
  cases n with
  | ff g c =>
    have hg : g < 12 := hv.1
    have e : 2 * g = 24 := hk
    omega
  | att g c =>
    have e : 2 * g + 1 = 24 := hk
    omega
  | hf φ i =>
    obtain ⟨hφ, hi⟩ := hv
    have hin := (placeIn_inside N Bd (φ := φ) hi).1
      (lt_of_lt_of_le hφ (le_trans hOK.1 (Nat.le_add_right _ _)))
    show |stackedH y (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0) Mh
      (Cm.Seg.Name.hf φ i).place.1 (Cm.Seg.Name.hf φ i).place.2.1
      (Cm.Seg.Name.hf φ i).place.2.2| < 2 ^ 18
    rw [stacked_hf y _ _ Mh N b φ hi]
    show |cellIn Mh 0 L.k (L.m / h.T) h.T φ i| < 2 ^ 18
    rw [cellIn_place, Nat.zero_add]
    exact Sm.1 _ hin.1 _ hin.2.1 _ hin.2.2
  | hd φ i =>
    obtain ⟨hφ, hi⟩ := hv
    have hin := (placeIn_inside N Bd (φ := φ) hi).2.1 hφ
    show |stackedH y (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0) Mh
      (Cm.Seg.Name.hd φ i).place.1 (Cm.Seg.Name.hd φ i).place.2.1
      (Cm.Seg.Name.hd φ i).place.2.2| < 2 ^ 18
    rw [stacked_hd y _ _ Mh N b hφ hi]
    show |cellIn Mh h.NHf L.kD (L.mD / h.T) h.T φ i| < 2 ^ 18
    rw [cellIn_place, hin.1, Nat.add_zero]
    exact Sm.2.1 _ hin.2.1 _ hin.2.2
  | hr φ i =>
    obtain ⟨hφ, hi⟩ := hv
    have hφ' : φ < Inst.Model.Head.nFeat .hr := lt_of_lt_of_le hφ hOK.2
    have hin := (placeIn_inside N Bd (φ := φ) hi).2.2.1 hφ'
    show |stackedH y (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0) Mh
      (Cm.Seg.Name.hr φ i).place.1 (Cm.Seg.Name.hr φ i).place.2.1
      (Cm.Seg.Name.hr φ i).place.2.2| < 2 ^ 18
    rw [stacked_hr y _ _ Mh N b hφ' hi]
    show |cellIn Mh (h.NHf + 1) L.kR (L.mR / h.T) h.T φ i| < 2 ^ 18
    rw [cellIn_place, hin.1, Nat.add_zero]
    exact Sm.2.2.1 _ hin.2.1 _ hin.2.2

/-- HeadOrd with the bound inside the matrices' own rows and columns. -/
def HeadOrdB (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (Wz : Mat)
    (x : Instance ppref) (Mh : Mats ℤ) : Prop :=
  SmallH h L (borderOf y) Mh ∧
  (∀ f a i, a < Cm.Plain.len f → i < nT → Inst.Model.Head.InLut (Cm.Plain.TP.tableOf f)
    (Cm.Plain.TP.key np ((cellsH h L (borderOf y) Mh).cast Cb.Gl.F)
      (Cm.TP.castH Cb.Gl.p Wz) (Cm.reqOf x) f a i)) ∧
  ∀ i < nT, ∀ k < 17, Cm.Plain.idn np ((cellsH h L (borderOf y) Mh).cast Cb.Gl.F) i k = 0

theorem ordB_of_ord {h : Model.Head.Shape} {L : HL} {y : Lay} {np : NormPar} {Wz : Mat}
    {x : Instance ppref} {Mh : Mats ℤ} (O : HeadOrd h L y np Wz x Mh) :
    HeadOrdB h L y np Wz x Mh := ⟨smallH_of_all O.1, O.2⟩

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- **The plain head: link 24 is in order**, from HeadOrdB. For a request with e = 1,024. -/
theorem linkOK_24B (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {s : Cm.Scales} {x : Instance ppref} (he : x.e = 1024) {Wz : Mat} {Mh : Mats ℤ}
    (O : HeadOrdB h L y s.nf Wz x Mh) :
    L5.LinkOK Cm.Seg.Hd.plain (Cm.Seg.TS.segM s) Wz x 24 (headMx h y Mh) :=
  L5.linkOK_of_holds
    (small_24 (numH_of_layout hF hL) (borderH_of_layout hl S Z Z2) Cm.lay_figures.2.2.2.2.2 y O.1)
    ((segM24_iff s x he Wz _).2
      ((matHolds_iff_cells hF hL hl S Z Z2 (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0) Mh
        (fun _ _ _ _ => rfl) s.nf x Wz).2 O.2))

#print axioms small_24
#print axioms linkOK_24B

end OnBytes.Road.Hd
