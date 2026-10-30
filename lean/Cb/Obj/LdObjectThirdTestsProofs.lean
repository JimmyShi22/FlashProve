-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectThirdTestsProofs.lean: the proofs of the statements of
Cb/Obj/LdObjectThirdTests.lean.

An assembly: lists of one member and counts of exceptional coefficients within a third of the
distance (Cb/Ld/LdTowerThird.lean, Cb/Ld/LdRelJohnson*.lean, Cb/Obj/LdObjectConfMore.lean) are put
into the theorems on the link with its closing (Cb/Obj/LdObjectLinkFull.lean) and on the test at one
instance with its closing (Cb/Obj/LdObjectLinFullProofs.lean, Cb/Ld/LdLinClosePlanProofs.lean,
Cb/Ld/LdLinCloseDemandProofs.lean). Nothing is defined here that a statement reads.

Limits: what the head of Cb/Obj/LdObjectThirdTests.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldT3_link` or `ldT3_lin` can be
   met together. -/
import Cb.Obj.LdObjectThirdTests
import Cb.Ld.LdRelJohnsonProofs
import Cb.Ld.LdLinClosePlanProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldT3_end : Spec.ldT3_end := by
  intro E _ _ S G _ B _ Sb sl Z d t cov h
  exact ldTower_base E _ t cov d (G.e + 1) 1
    (ldThird_base E (G.joint Sb sl Z) d (ld_laws_fam E G.P _ _ h.laws) (ld_dist_fam _ d h.dist)
      h.lt (ld_transp_fam _ h.transp))

theorem ldT3_run : Spec.ldT3_run := fun E _ _ S D d h h1 hZ hT =>
  ldThird_run E S D d h1 h.laws h.dist (by have := h.lt; omega) hZ h.fits hT

theorem ldT3_list : Spec.ldT3_list := fun E _ _ o d hL hD h2 =>
  sig_list_of_code E o 1 (ld_list_unique E _ o.C d o.e hL hD h2)

theorem ldT3_sndK : Spec.ldT3_sndK := fun E _ _ _ _ _ _ _ _ _ P S dN h =>
  { laws := h.laws, fair := h.fair,
    list := fun a => by rw [h.one a]; exact ldT3_list E _ (dN a) (h.laws a) (h.dist a) (h.lt a),
    ev := h.ev, snd := h.snd, bl := h.bl, hid := h.hid }

theorem ldT3_sndL : Spec.ldT3_sndL := fun E _ _ _ _ _ _ _ _ _ _ P S dW dU dO h =>
  { lawsW := h.lawsW, fairW := h.fairW,
    listW := fun a => by
        rw [h.oneW a]; exact ldT3_list E _ (dW a) (h.lawsW a) (h.distW a) (h.ltW a),
    evW := h.evW, sndW := h.sndW, blW := h.blW, hidW := h.hidW
    lawsU := h.lawsU, fairU := h.fairU, listU := fun a => by rw [h.oneU a]; exact ldT3_list E _ (dU a) (h.lawsU a) (h.distU a) (h.ltU a), evU := h.evU, sndU := h.sndU, blU := h.blU, hidU := h.hidU
    lawsO := h.lawsO, fairO := h.fairO, listO := fun a => by rw [h.oneO a]; exact ldT3_list E _ (dO a) (h.lawsO a) (h.distO a) (h.ltO a), evO := h.evO, sndO := h.sndO, blO := h.blO, hidO := h.hidO }

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
theorem ldT3_conf : Spec.ldT3_conf F E := fun Cf h =>
  ldCm_ok F E Cf 1
    ⟨h.core, by have := h.lt; omega,
      ldCm_list_unique F E Cf h.dist (by have := h.lt; omega), h.evades⟩ h.model

theorem ldT3_link : Spec.ldT3_link F E := by
  intro Cf _ K S dN Kc dG d₂ d hC h0 h1 hpl hS hG hL hZ hT ht
  have hl := ldCm_list_unique F E Cf hC.dist (by have := hC.lt; omega)
  have hF : K.P.FoldErr K.free K.free (Cf.εThird K.e₀) (Cf.εThird K.e₁) :=
    ldLk_foldErr_rec K.P Cf.C₀.d _ 1 _ 1 (ldCm_dist F E Cf hC.dist)
      (by have := hC.lt; show Cf.eM < Cf.C₀.d; omega) h0 h1
      (ldCm_mca_third F E Cf K.e₀ hC.dist (by have := hC.lt; omega))
        (ldCm_list_le F E Cf 1 K.e₀ hl h0)
        (ldCm_mca_third F E Cf K.e₁ hC.dist (by have := hC.lt; omega))
        (ldCm_list_le F E Cf 1 K.e₁ hl h1)
  exact ldOl_full F E Cf K S 1 _ _ Kc d₂ d (ldT3_conf F E Cf hC) hF hpl
    (ldT3_sndK E _ _ _ _ K.P S dN hS) (ldT3_run E _ Kc.run dG hG hL hZ hT) ht

open Classical in
theorem ldT3_lin : Spec.ldT3_lin F E := by
  intro O _ p T Sn dW dU dO dG₁ dG₂ q₀ ba b' d d0 hd h3 he' hpy hS hrest hA hG₁ hL₁ hZ₁ hT₁ hG₂ hL₂
    hZ₂ hT₂ hQ' hq' hba hbW hbU hbO
  have hl := ldCm_list_unique F E O.Cf hd (by omega)
  have h1 : T.D₁.OK := ldT3_run E _ T.D₁ dG₁ hG₁ hL₁ hZ₁ hT₁
  have h2 : T.D₂.OK := ldT3_run E _ T.D₂ dG₂ hG₂ hL₂ hZ₂ hT₂
  exact ldOLF_lin F E O _ 1 Sn (O.toC.Sa.qFam q₀ ba) T.Q T.fq d d0 hd (ldCm_dist F E O.Cf hd)
    (by omega) he' (ldCm_mca_third F E O.Cf O.e' hd (by omega))
    (ldCm_list_le F E O.Cf 1 O.e' hl he') hpy (ldT3_sndL E _ _ _ _ O.toC.P Sn dW dU dO hS)
    (ldLinPlan_says E _ _ _ _ O.toC p _ T.Q'.base T.fa hrest hA)
    (ldChain_cons E _ _ _ T.D₁ _ T.d₁ T.d₁' h1 (ldChain_cons E _ _ _ T.D₂ T.Q' T.d₂ T.d₂' h2 hQ'))
    (ldDemand_plan E _ _ _ _ O.toC p T Sn (O.toC.Sa.qFam q₀ ba) q₀ ba b' hq'
      (fun _ hW => hW) hba hbW hbU hbO)

end
end Cb
