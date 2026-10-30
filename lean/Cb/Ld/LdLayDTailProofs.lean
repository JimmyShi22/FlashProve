-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayDTailProofs.lean: the proof of Cb/Ld/LdLayDTail.lean's statement:
Cb/Req1/LdReqRefLayTail.lean's rule (`Spec.ldReqRefLay_tail`: under the hypotheses of its statement,
the wide fact passes the last segment), at the type of masks of the block that arrives: the two
bijections of the steps' conditions are taken over to the fact before the segment, which stays in
the set because the set is closed under "another type for the same masks". What is said and what is
not: the head of Cb/Ld/LdLayDTail.lean.
-/
import Cb.Ld.LdLayDTail
import Cb.Ld.LdLayDKitProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain

theorem ldLayD_tail : Spec.ldLayD_tail := by
  intro F E Kc _ _ _ _ _ pp _ R b T _ Q G β β'' hG hA hβ
    ⟨W, own, Mk, iF, iN, val, ⟨e₁, h₁⟩, hO, ⟨e₂, h₂⟩⟩
  obtain ⟨Fr, κ, hGh, hF, hQ⟩ := hO.front
  have hq : W.PassQ Fr own β''.Mk (fun M => val (e₂.symm M)) :=
    ⟨⟨fun w w' M h => hQ.lk w w' (e₂.symm M) h,
        fun w w' M h => hQ.s0 w w' (e₂.symm M) h,
        fun j hj w w' M h => hQ.s j hj w w' (e₂.symm M) h⟩,
      ldLayD_noLook _ _ _ _ _ _ hO.send1,
      ldLayD_noLook _ _ _ _ _ _ hO.send3⟩
  refine ⟨⟨β.fact.Kc, β.fact.kc, β''.Mk, fun M k => β.fact.put ((e₁.trans e₂).symm M) k⟩,
    hG _ (.equiv β.fact β''.Mk (e₁.trans e₂) (.base _ hβ)),
    fun Y hY => ?_⟩
  refine ldReqRefLay_tail F E Kc pp R b T W Fr κ own β''.Mk (fun M => val (e₂.symm M)) _ β''.fact.Kc
    β''.fact.kc β''.fact.put hA hGh hF hq hO.maskL hO.apartL hO.ownT hO.apartT (fun Y' hY' => ?_)
    (fun x w w' M h => ?_) Y hY
  · refine segCarry_step b T.A.V.Fp.s0 T.f T.g T.m T.back Y' _ _
      (W.fact own β''.Mk fun M => val (e₂.symm M)).kc
      (W.fact own β''.Mk fun M => val (e₂.symm M)).put hY' fun x w w' M h => ?_
    have h' := h₁ x w w' ((e₁.trans e₂).symm M) h
    refine ⟨h'.1, ?_⟩
    have h'' := h'.2
    rw [show e₁ ((e₁.trans e₂).symm M) = e₂.symm M from e₁.apply_symm_apply _] at h''
    exact h''
  · have h' := h₂ x w w' (e₂.symm M) h
    rw [e₂.apply_symm_apply] at h'
    exact h'

end Cb
