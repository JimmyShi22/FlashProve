-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectJohnTestsProofs.lean: the proofs of the statements of Cb/Obj/LdObjectJohnTests.lean
(below the Johnson radius: sendings, link, test at one instance and weights-formedness).

Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Obj/LdObjectJohnTests.lean):
  `ldJn_link`: the link with its closing.
  `ldJn_lin`: the test at one instance.
  `ldJn_wf`: weights-formedness.

Limits: what the head of Cb/Obj/LdObjectJohnTests.lean lists as not said is not said here either.
Agreement stays a hypothesis, as told there.
Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectJohnTests
import Cb.Ld.LdRelJohnsonProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldJn_list : Spec.ldJn_list := fun E _ _ o d hL hD hJ =>
  sig_list_of_code E o _ (ld_list_johnson E o.P o.C d o.e hL hD hJ)

theorem ldJn_run : Spec.ldJn_run := fun E _ _ S D d hG hL hZ hT =>
  ldJohn_run E S D d hL hG.laws hG.dist hG.inJ hZ hG.fits hT

theorem ldJn_sndK : Spec.ldJn_sndK := fun E ι κ J Λ _ _ _ _ _ P S dN h =>
  { laws := h.laws, fair := h.fair,
    list := fun a => by rw [h.isL a]; exact ldJn_list E _ (dN a) (h.laws a) (h.dist a) (h.inJ a),
    ev := h.ev, snd := h.snd, bl := h.bl, hid := h.hid }

theorem ldJn_sndL : Spec.ldJn_sndL := fun E ι κ J Y _ _ _ _ _ _ P S dW dU dO h =>
  { lawsW := h.lawsW, fairW := h.fairW,
    listW := fun a => by
        rw [h.isLW a]; exact ldJn_list E _ (dW a) (h.lawsW a) (h.distW a) (h.inJW a),
    evW := h.evW, sndW := h.sndW, blW := h.blW, hidW := h.hidW
    lawsU := h.lawsU, fairU := h.fairU, listU := fun a => by rw [h.isLU a]; exact ldJn_list E _ (dU a) (h.lawsU a) (h.distU a) (h.inJU a), evU := h.evU, sndU := h.sndU, blU := h.blU, hidU := h.hidU
    lawsO := h.lawsO, fairO := h.fairO, listO := fun a => by rw [h.isLO a]; exact ldJn_list E _ (dO a) (h.lawsO a) (h.distO a) (h.inJO a), evO := h.evO, sndO := h.sndO, blO := h.blO, hidO := h.hidO }

theorem ldJe_send : Spec.ldJe_send := fun _ _ _ _ _ => rfl

section
variable (F E : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

omit [Fintype E] in
theorem ldJn_conf : Spec.ldJn_conf F E := fun Cf h =>
  ldCm_ok F E Cf 1
    ⟨h.core, by have := h.lt; omega, ldCm_list_unique F E Cf h.dist h.lt, h.evades⟩ h.model

theorem ldJn_link :
    Spec.ldJn_link F E := fun Cf _ K on0 on1 S dN ε₀ ε₁ Kc d₂ d hC hFit hF hpl hS hK ht =>
  ldOlA_full F E Cf K on0 on1 S 1 ε₀ ε₁ Kc d₂ d (ldJn_conf F E Cf hC) hFit hF hpl
    (ldJn_sndK E _ _ _ _ K.P S dN hS) hK ht

open Classical in
theorem ldJn_lin : Spec.ldJn_lin F E := by
  intro O _ p T Sn dW dU dO εf q₀ ba b' d d0 hd h2 hF hpy hS hrest hA h1 h2' hQ' hq' hba hbW hbU hbO
  exact ldOLF_items F E O _ Sn (O.toC.Sa.qFam q₀ ba) T.Q T.fq d d0 hd (by omega) hF hpy
    (ldJn_sndL E _ _ _ _ O.toC.P Sn dW dU dO hS)
    (ldLinPlan_says E _ _ _ _ O.toC p _ T.Q'.base T.fa hrest hA)
    (ldChain_cons E _ _ _ T.D₁ _ T.d₁ T.d₁' h1 (ldChain_cons E _ _ _ T.D₂ T.Q' T.d₂ T.d₂' h2' hQ'))
    (ldDemand_plan E _ _ _ _ O.toC p T Sn (O.toC.Sa.qFam q₀ ba) q₀ ba b' hq'
      (fun _ hW => hW) hba hbW hbU hbO)

theorem ldJn_wf : Spec.ldJn_wf F E := fun Z p dS h =>
  { toRest := h.toRest
    conf := ldJn_conf F E Z.W.Cf h.confH
    list := fun a => by rw [h.isL a]; exact ldJn_list E _ (dS a) (h.laws a) (h.dist a) (h.inJ a)
    evades := h.ev }

theorem ldJe_link : Spec.ldJe_link F E := by
  intro Cf _ K on0 on1 S ε₀ ε₁ Kc d₂ d
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
  rw [hc] at h
  exact h

theorem ldJe_lin : Spec.ldJe_lin F E := by
  intro O _ p T Sn εf d
  rw [ldOErr_lin F E O _ Sn T.Q T.fq d]
  have e1 := (ldOErr_cons E _ _ _ T.D₁ (LdTc.cons T.D₂ T.Q' T.d₂ T.d₂') T.d₁ T.d₁').1
  have e2 := (ldOErr_cons E _ _ _ T.D₂ T.Q' T.d₂ T.d₂').1
  have e3 : T.Q.c.errs =
      (T.L₁ * T.Z₁.err) :: T.T₁.N.err.toList ++
        ((T.L₂ * T.Z₂.err) :: T.T₂.N.err.toList ++ T.Q'.c.errs) :=
    e1.trans (congrArg _ e2)
  rw [e3]

end
end Cb
