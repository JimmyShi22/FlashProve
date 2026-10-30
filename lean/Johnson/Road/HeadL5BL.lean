-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/HeadL5BL.lean: "the head's link is in order", for the head with the cost ledger, with
the bound asked inside the matrices' own rows and columns alone.

HeadOrdL (Johnson/Road/HeadL5Link.lean) asks that every entry Mh a r c is small, at every number,
row and column. Here the bound is SmallH of Johnson/Road/HeadL5B.lean. With it the statement still
gives LinkOK (Johnson/Road/Lane5.lean) at link 24, at the family Policy.segPol s pol and the shape
Cm.Seg.Hd.main, for every request.

Main definition: HeadOrdLB.
Main theorems: linkOKL_24B; ordLB_of_ord (HeadOrdL gives HeadOrdLB).

What is not claimed. As in Johnson/Road/HeadL5B.lean and Johnson/Road/HeadL5Link.lean. The program
does not import this file.
-/
import Johnson.Road.HeadL5B
import Johnson.Road.HeadL5Link

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Hd

open Inst.Model (ppref NormPar Instance Mat AcceptancePolicy)
open Inst.Model.All (DF)
open OnBytes.Model.Layer (Lay)
open OnBytes.Model.Head (HL)
open OnBytes.Model.Verify (borderOf)

/-- HeadOrdL with the bound inside the matrices' own rows and columns. -/
def HeadOrdLB (h : Model.Head.Shape) (L : HL) (y : Lay) (np : NormPar) (pol : AcceptancePolicy) (Wz : Mat)
    (x : Instance ppref) (Mh : Mats ℤ) : Prop :=
  SmallH h L (borderOf y) Mh ∧
  Policy.HeadCl np pol Wz x (cellsH h L (borderOf y) Mh) ∧
  (x.e < ppref.T → ((x.y.val : ℕ) : ZMod Cb.Gl.p) = 0)

theorem ordLB_of_ord {h : Model.Head.Shape} {L : HL} {y : Lay} {np : NormPar} {pol : AcceptancePolicy}
    {Wz : Mat} {x : Instance ppref} {Mh : Mats ℤ} (O : HeadOrdL h L y np pol Wz x Mh) :
    HeadOrdLB h L y np pol Wz x Mh := ⟨smallH_of_all O.1, O.2⟩

variable {h : Model.Head.Shape} {tau : Array F} {L : HL} {hy : Model.Layer.Shape}
  {pc : List (List String)} {y : Lay}

/-- **With the ledger: link 24 is in order**, from HeadOrdLB. For every request. -/
theorem linkOKL_24B (hF : FullH h) (hL : Model.Head.layout h tau = .ok L)
    (hl : Model.Layer.layout hy pc = .ok y) (S : Switches hy) (Z : Sized hy DF) (Z2 : Sized2 hy DF)
    {s : Cm.Scales} {pol : AcceptancePolicy} {x : Instance ppref} {Wz : Mat} {Mh : Mats ℤ}
    (O : HeadOrdLB h L y s.nf pol Wz x Mh) :
    L5.LinkOK Cm.Seg.Hd.main (Policy.segPol s pol) Wz x 24 (headMx h y Mh) :=
  L5.linkOK_of_holds
    (small_24 (numH_of_layout hF hL) (borderH_of_layout hl S Z Z2) Policy.mainOK y O.1)
    (by
      rw [Policy.segPol_head]
      exact (Policy.headPolY_holds_int s pol x Wz (headMx h y Mh) (cellsH h L (borderOf y) Mh)
        (readsAtMain_cellsH hF hL hl S Z Z2 (fun _ _ r c => Mh (h.NHf + 3) r c) (fun _ _ _ => 0)
          Mh (fun _ _ _ _ => rfl))).2 O.2)

#print axioms linkOKL_24B

end OnBytes.Road.Hd
