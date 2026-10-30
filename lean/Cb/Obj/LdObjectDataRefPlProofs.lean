-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectDataRefPlProofs.lean: the proofs of the statements of Cb/Obj/LdObjectDataRefPl.lean
(at the reference request four clauses on the plan of the batch test follow from one equation and a
condition on places). An assembly.
Nothing is defined here.

Main names (statements and hypotheses: Cb/Obj/LdObjectDataRefPl.lean):
  `ldObjRefPl_says`: the request's last claims, at every end of a request.
  `ldObjRefPl_hyp`: the four clauses on the plan of the batch test.

Limits: what the head of Cb/Obj/LdObjectDataRefPl.lean lists as still asked is still asked here, and
what it lists as not said is not said here either.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectDataRefPl

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldObjRefPl_says : Spec.ldObjRefPl_says F E := by
  intro Kc R
  obtain ⟨h1, h2⟩ := ldPartBatRe_facts F E Kc R
  refine ⟨fun sa _ m _ => h2 sa m, fun sa _ m _ => h2 sa m, h1, fun st n hn => ?_⟩
  by_contra hno
  rw [not_or] at hno
  exact hn ((ldORE_rest F E Kc R).2 st n (fun i e => hno.1 ⟨i, e⟩) fun a e => hno.2 ⟨a, e⟩)

theorem ldObjRefPl_hyp : Spec.ldObjRefPl_hyp F E := by
  intro Kc Rr plB R hIs h
  have hS : (Rr.rowsPack plB).Says := by
    rw [hIs]
    exact ldObjRefPl_says F E Kc R
  exact
    { q₀is := h.q₀is, entAt := h.entAt, restIs := h.restIs, plW := h.plW, plC := h.plC,
      plR := h.plR, nowX := h.nowX, kpX := h.kpX
      needA := h.needA, needW := h.needW, needU := h.needU, needO := h.needO
      shared := h.shared
      abRel := hS.abRel
      abRelR := hS.abRelR
      plRB := h.plRB
      restIsB := h.restIsB
      restVal := hS.restVal
      plSB := fun st a j hne => h.plB₂ ⟨a, j⟩ (hS.supp st ⟨a, j⟩ hne)
      nowXB := h.nowXB, kpXB := h.kpXB, q₀Be := h.q₀Be, qaOK := h.qaOK, oneN := h.oneN
      needNA := h.needNA, needNW := h.needNW, needNU := h.needNU, needNO := h.needNO }

end
end Cb
