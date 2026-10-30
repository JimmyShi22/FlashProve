-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinkAtProofs.lean: the proofs of the statements of Cb/Obj/LdObjectLinkAt.lean. They
use: the link with its closing at a pair: Cb/Obj/LdObjectLinkPairFull.lean; within a third:
Cb/Obj/LdObjectThirdTestsProofs.lean; the errors: the rules of Cb/Obj/LdObjectErr.lean. Nothing is
defined here that a statement reads.
What `Spec.ldT3_link_far` is on, in the words of the head of Cb/Obj/LdObjectLinkAt.lean: the
sub-protocol for equality of two encoded indices (the link) with its closing, within a third of the
distance; the first index decodes (the second regime); but (its "Limits:") the radius e₀ may exceed
a third of the distance, up to d - eM - 1 (`K.e₀ + Cf.eM < Cf.C₀.d`).

Main names (statements and hypotheses: Cb/Obj/LdObjectLinkAt.lean):
  `ldT3_link_far`: `LinkListR` and `LinkKnowR` (Hiop/RecSubs.lean) of the link with its closing at
    the pair (`K.dec0`, `K.free`).
  `ldT3e_link_far`: the link's errors in the order of the rounds.
-/
import Cb.Obj.LdObjectLinkAt
import Cb.Obj.LdObjectThirdTestsProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem ldT3_link_far : Spec.ldT3_link_far F E := by
  intro Cf _ K S dN Kc dG d₂ d hC h0 h1 hpl hS hG hL hZ hT ht
  have hl := ldCm_list_unique F E Cf hC.dist (by have := hC.lt; omega)
  have hF : K.P.FoldErr K.dec0 K.free 0 (Cf.εThird K.e₁) :=
    ldLk_foldErr K.P Cf.C₀.d _ 1 (ldCm_dist F E Cf hC.dist) h0 h1
      (ldCm_mca_third F E Cf K.e₁ hC.dist (by have := hC.lt; omega))
      (ldCm_list_le F E Cf 1 K.e₁ hl h1)
  exact ldOlA_full F E Cf K K.dec0 K.free S 1 _ _ Kc d₂ d (ldT3_conf F E Cf hC)
    ⟨fun _ _ h _ => h, fun _ _ h => h⟩ hF hpl (ldT3_sndK E _ _ _ _ K.P S dN hS)
    (ldT3_run E _ Kc.run dG hG hL hZ hT) ht

theorem ldT3e_link_far : Spec.ldT3e_link_far F E := by
  intro Cf _ K on0 on1 S ε₀ ε₁ Kc d₂ d hS hL
  have h : (K.P.linkC on0 on1 S ε₀ ε₁ (Kc.cZ d₂) d).errs =
      [K.P.errGam ε₀ ε₁, ldSendFamErr K.P.N S.Sd S.L, 0, K.P.errLoc, K.P.errPhi] ++
        (Kc.cZ d₂).errs := by
    unfold LdLkP.linkC LdLkP.coreC
    rw [(chainErr_link _ _ _ _ _).1, (chainErr_append _ _ _ _ _ _).1,
      Chain.errs_snoc, Chain.errs_snoc, Chain.errs_snoc, Chain.errs_one]
    rfl
  have hc : (Kc.cZ d₂).errs = (Kc.L * Kc.Z.err) :: Kc.T.N.err.toList := by
    unfold LdLkP.Cl.cZ
    rw [(chainErr_append _ _ _ _ _ _).1, Chain.errs_one]
    show [] ++ (LdTc.cons Kc.run _ _ _).c.errs = _
    rw [(ldOErr_cons E _ _ _ Kc.run _ _ _).1]
    show [] ++ ((Kc.L * Kc.Z.err) :: Kc.T.N.err.toList ++ (Chain.one _).errs) = _
    rw [Chain.errs_one]
    show (Kc.L * Kc.Z.err) :: (Kc.T.N.err.toList ++ []) = _
    rw [List.append_nil]
  rw [hc, ldT3e_send E K.P.N S.Sd S.L hS, hL, Nat.one_mul] at h
  exact h

end
end Cb
