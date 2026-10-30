-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdAltBProofs.lean: the proofs of the statements of Cb/Ld/LdAltB.lean.
-/
import Cb.Ld.LdAltB

set_option autoImplicit false

namespace Iop
open IOR IOR.ChainV

theorem chainV_append_assoc : Spec.chainV_append_assoc := by
  intro K N A B C D VA VB VC VD c₁ c₂ c₃
  induction c₃ with
  | one v => rw [append_one, append_one, append_snoc]
  | snoc c v ih => rw [append_snoc, append_snoc, append_snoc, ih]

theorem chainV_okFrom_append : Spec.chainV_okFrom_append := by
  intro K N Z A B C VZ VA VB VC c₀ c c'
  induction c' with
  | one v => rw [append_one, okFromV_snoc, okFromV_one]
  | snoc c' v ih => rw [append_snoc, okFromV_snoc, okFromV_snoc, ih, chainV_append_assoc, and_assoc]

end Iop

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldAltB_front : Spec.ldAltB_front := fun _ _ _ _ _ _ _ QA _ cF _ N kx ky h hQ =>
  chainA_kb_append Unit _ _ _ cF QA.cA N kx ky ldKeyT h hQ

theorem ldAltV_of_ok : Spec.ldAltV_of_ok := fun _ _ _ _ _ N _ V QV Z VZ c₀ h =>
  ⟨chainV_okFrom_of_all Unit N Z _ _ VZ V QV.VT c₀ QV.cV h.1, h.2.1, h.2.2⟩

theorem ldAltV_consLo : Spec.ldAltV_consLo := by
  intro E _ _ S E₀ Wp N D QA d d' VA tieB qB QV Z VZ c₀ hv hQ
  refine ⟨(chainV_okFrom_append Unit N _ _ _ _ _ _ _ _ c₀
        (ChainV.one (D.loV QA.Q.base d d' N VA tieB qB)) QV.cV).2
      ⟨(ChainV.okFromV_one c₀ _).2 (Or.inl hv), ?_⟩,
    (chainA_coh_append Unit _ _ _ (ChainA.one (D.linkLo QA.Q.base d d')) QA.cA).2
      ⟨(ChainA.coh_one _).2
          (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _),
        hQ.2.1⟩,
    hQ.2.2⟩
  rw [ChainV.append_one]
  exact hQ.1

theorem ldAltV_consSh : Spec.ldAltV_consSh := by
  intro E _ _ S E₀ Wp N D QA d d' VA W0' tieB qB rep nx QV Z VZ c₀ hv hQ
  refine ⟨(chainV_okFrom_append Unit N _ _ _ _ _ _ _ _ c₀
        (ChainV.one (D.shV QA.Q.base d d' N VA W0' tieB qB rep nx)) QV.cV).2
      ⟨(ChainV.okFromV_one c₀ _).2 (Or.inl hv), ?_⟩,
    (chainA_coh_append Unit _ _ _ (ChainA.one (D.linkSh QA.Q.base d d')) QA.cA).2
      ⟨(ChainA.coh_one _).2 (RoundSplits.const_coherent (fun r => RAnn.ofShared_coherent .sh r) _),
        hQ.2.1⟩,
    hQ.2.2⟩
  rw [ChainV.append_one]
  exact hQ.1

theorem ldAltV_front : Spec.ldAltV_front := by
  intro E _ _ S E₀ Wp N x QA p cF hF Vx Vy cV hV QV Z VZ c₀ hc hCoh hQ
  exact ⟨(chainV_okFrom_append Unit N _ _ _ _ _ _ _ _ c₀ cV QV.cV).2 ⟨hc, hQ.1⟩,
    (chainA_coh_append Unit _ _ _ cF QA.cA).2 ⟨hCoh, hQ.2.1⟩,
    hQ.2.2⟩

theorem ldAltV_cZ : Spec.ldAltV_cZ := by
  intro E ι κ J Y _ _ _ _ _ C N QA fq VA tieB qB QV Z VZ c₀ hstep hQ
  refine ⟨(chainV_okFrom_append Unit N _ _ _ _ _ _ _ _ c₀
        (ChainV.one ((C.link fq QA.Q.base).loV N VA tieB qB)) QV.cV).2
      ⟨(ChainV.okFromV_one c₀ _).2 (Or.inl hstep), ?_⟩,
    ?_, hQ.2.2⟩
  · rw [ChainV.append_one]
    exact hQ.1
  · rw [(ldLinV_cZ_same E ι κ J Y C N QA fq VA tieB qB QV).1]
    exact (chainA_coh_append Unit _ _ _ (ChainA.one (C.link fq QA.Q.base).lo) QA.cA).2
      ⟨(ChainA.coh_one _).2
          (RoundSplits.const_coherent (f := RAnn.allLocal) (fun r => RAnn.ofSlot_coherent .lo r) _),
        hQ.2.1⟩

end Cb
