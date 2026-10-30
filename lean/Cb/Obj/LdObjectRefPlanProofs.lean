-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectRefPlanProofs.lean: the proofs of the statements of Cb/Obj/LdObjectRefPlan.lean (the
plan of the batch test at the end of a request, as a term). An assembly.
Nothing is defined here.

Main names (statements and hypotheses: Cb/Obj/LdObjectRefPlan.lean):
  `ldRefPlan_six`: the six clauses, from conditions on places.
  `ldRefPlan_hyp`: the step from `Rr.HypPl₁` to `Rr.HypPl`.
-/
import Cb.Obj.LdObjectRefPlan

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldRefPlan_set : Spec.ldRefPlan_set := fun _ _ _ _ _ _ _ _ _ => ⟨rfl, rfl, rfl, rfl⟩

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldRefPlan_six : Spec.ldRefPlan_six F E := by
  intro Kc R p₀ plR h
  have hS := ldObjRefPl_says F E Kc R
  refine ⟨hS.abRel, hS.abRelR, fun b st a j hne => ?_, rfl, hS.restVal, fun st a j hne => ?_⟩
  · by_contra hno
    exact hne (h.off b _ ⟨a, j⟩ fun hp => hno (h.kept b ⟨a, j⟩ hp))
  · rcases hS.supp st ⟨a, j⟩ hne with ⟨i, e⟩ | ⟨x, e⟩
    · have ha : a = (R.wAt i).1 := congrArg Sigma.fst e
      subst ha
      exact h.own i
    · have ha : a = (R.μAt x).1 := congrArg Sigma.fst e
      subst ha
      exact h.laid x

theorem ldRefPlan_hyp : Spec.ldRefPlan_hyp F E := by
  intro Kc Rr R p₀ plR hIs hP h
  have hS : Rr.onPack.Six := by
    rw [hIs]
    exact ldRefPlan_six F E Kc R p₀ plR hP
  exact
    { q₀is := h.q₀is, entAt := h.entAt, restIs := h.restIs, plW := h.plW, plC := h.plC,
      plR := h.plR, nowX := h.nowX, kpX := h.kpX
      needA := h.needA, needW := h.needW, needU := h.needU, needO := h.needO
      shared := h.shared
      abRel := hS.abRel
      abRelR := hS.abRelR
      plRB := hS.plRB
      restIsB := hS.restIsB
      restVal := hS.restVal
      plSB := hS.plSB
      nowXB := h.nowXB, kpXB := h.kpXB, q₀Be := h.q₀Be, qaOK := h.qaOK, oneN := h.oneN
      needNA := h.needNA, needNW := h.needNW, needNU := h.needNU, needNO := h.needNO }

end
end Cb
