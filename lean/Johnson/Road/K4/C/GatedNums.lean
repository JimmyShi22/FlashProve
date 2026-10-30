-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/GatedNums.lean: CONDITIONAL.

Not shown here. THAT THE HONEST SIDE's TENSORS READ AS THE LIBRARY's VALUES. Where K4Plan holds: the
head of Johnson/Road/K4/W/GroundOfHear.lean. Nothing on soundness, on completeness or on any other
property. No property is claimed.

The twelve public numbers `GatedNums` (C/Gated.lean) from the nine public facts on the plan
(`K4Plan`, Johnson/Road/K4/W/GroundOfHear.lean): so they are no hypothesis of their own.

  `gatedNums_of_plan`   GatedNums Q D. The powers of two come from the layout's own tests (an
      expert's width has one bit set, and a layer's width is twice that), the two numbers of
      variables from what readsOf lays.
-/
import Johnson.Road.K4.C.Gated
import Johnson.Road.K4.W.GroundOfHear
import Johnson.Road.K4.PlanClauses

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Road.K4.W (K4Plan)
open Inst.Model.FFSeg (Dim lF lFe)
open OnBytes.Desc.First.K4.Honest (K4Pub)

/-- **The twelve numbers, from the plan's public facts.** CONDITIONAL: on A. -/
theorem gatedNums_of_plan {Q : K4Pub} {hS : Layer.Shape} {pc : List (List String)} {tl : HTailF2}
    {D : Dim} (A : K4Plan hS pc Q.P Q.g tl D) : GatedNums Q D := by
  obtain ⟨_, m2, m3⟩ := Fo.readsOf_mu A.reads
  have L := laySizes_of_layout A.lay
  have L2 := laid2_of_layout A.lay
  have Mr := layMore_of_layout A.lay
  obtain ⟨g1, _, _, g4⟩ := gated_sizes A.lay A.sw.p3 A.sized
  have Z := A.sized
  have efe : hS.fe = 2 ^ lFe D := by
    rw [← Z.fe]
    exact g4
  have ef : hS.f = 2 ^ (lFe D + 1) := by rw [Mr.ffe A.sw.p3, efe, Nat.pow_succ, Nat.mul_comm]
  have eF : lF D = lFe D + 1 := by
    show Nat.clog 2 D.P.f = _
    rw [Z.f, ef, Nat.clog_pow 2 _ (by decide)]
  have elPf : Q.P.y.lPf = lF D := by
    rw [L.lPf, ceilLog2_eq_clog, ef, Nat.clog_pow 2 _ (by decide), eF]
  have elfe : Q.P.y.lfe = lFe D := by
    rw [L.lfe, if_pos A.sw.p3, ceilLog2_eq_clog, efe, Nat.clog_pow 2 _ (by decide)]
  have elt : Q.P.y.h.lt = D.lT := by rw [L.shape, Z.lT]
  have ell : Q.P.y.h.ll = D.lL := by rw [L.shape, Z.lL]
  exact
    { T := by rw [L2.T, elt]
      Lam := by rw [L.Lam, Z.lL]
      lL := g1
      f := by rw [L.shape, ef, eF]
      Pf := by rw [Mr.Pf, elPf]
      fe := by rw [L.shape]; exact efe
      Dfe := g4
      ffe := eF
      muH := by rw [m2, ell, elPf, elt]
      muH2 := by rw [m3, ell, elfe, elt]
      lfe := elfe
      LamM := by
        rw [L.LamM, Z.lL]
        obtain ⟨k, hk⟩ : ∃ k, hS.ll = k + 1 := ⟨hS.ll - 1, by have := L.ll; omega⟩
        rw [hk, Nat.pow_succ, Nat.mul_div_cancel _ (by decide), Nat.add_sub_cancel] }

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.gatedNums_of_plan
