-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/PlanLens.lean: CONDITIONAL.

Not shown here. WHERE K4Plan HOLDS: the head of Johnson/Road/K4/W/GroundOfHear.lean; its field sw
bars every shape but those with the library's eleven switches. Beside a small synthetic plan, given
one evaluated fact, no example is known. NOTHING ON THE PLAN OF THE HASHED ROUNDS (hp): K4Plan does
not read it. Nothing on soundness, on completeness or on any other property. No property is claimed.

Six public numbers more from the plan's nine public facts (`K4Plan`,
Johnson/Road/K4/W/GroundOfHear.lean), which the statements on the sumchecks' starts ask
(Johnson/Desc/ProofFile/Honest/K4/Law/W/StartsAt.lean): by the library's laws on a layout that
`layout` returns and on what `readsOf` returns.

  `planLens_of_plan`   ll = D.lL; lPf = lF D; lt = D.lT; lNI = D.lL + 1; D.nNu ≤ 2 ^ lNI; D.d ≤ 2 ^
      lPd.
-/
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

/-- **Six public numbers.** CONDITIONAL: on A. -/
theorem planLens_of_plan {hS : Layer.Shape} {pc : List (List String)} {P : Layer.Pub} {g : ℕ}
    {tl : HTailF2} {D : Dim} (A : K4Plan hS pc P g tl D) :
    P.y.h.ll = D.lL ∧ P.y.lPf = lF D ∧ P.y.h.lt = D.lT ∧ P.rd.lNI = D.lL + 1 ∧
      D.nNu ≤ 2 ^ P.rd.lNI ∧ D.d ≤ 2 ^ P.y.lPd := by
  have L := laySizes_of_layout A.lay
  have Mr := layMore_of_layout A.lay
  obtain ⟨_, n2, n3, n4, _⟩ := norms_sizes A.lay A.sized
  obtain ⟨_, _, _, g4⟩ := gated_sizes A.lay A.sw.p3 A.sized
  have Z := A.sized
  have two : 2 * 2 ^ hS.ll = 2 ^ (hS.ll + 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have eN : P.rd.lNI = hS.ll + 1 := by
    rw [Model.Fit.readsOf_lNI A.reads, L.NI, two, ceilLog2_eq_clog, Nat.clog_pow 2 _ (by decide)]
  have efe : hS.fe = 2 ^ lFe D := by
    rw [← Z.fe]
    exact g4
  have ef : hS.f = 2 ^ (lFe D + 1) := by rw [Mr.ffe A.sw.p3, efe, Nat.pow_succ, Nat.mul_comm]
  have eF : lF D = lFe D + 1 := by
    show Nat.clog 2 D.P.f = _
    rw [Z.f, ef, Nat.clog_pow 2 _ (by decide)]
  refine ⟨by rw [L.shape, Z.lL], ?_, by rw [L.shape, Z.lT], by rw [eN, Z.lL], ?_, ?_⟩
  · rw [L.lPf, ceilLog2_eq_clog, ef, Nat.clog_pow 2 _ (by decide), eF]
  · exact Nat.le_of_eq (by rw [nNu_tie Z, eN, two])
  · rw [n2]
    calc hS.d / P.y.S2 * 2 ^ P.y.ls ≤ 2 ^ (P.y.lPd - P.y.ls) * 2 ^ P.y.ls :=
          Nat.mul_le_mul_right _ n3
      _ = 2 ^ P.y.lPd := by rw [← Nat.pow_add, Nat.sub_add_cancel n4]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.planLens_of_plan
