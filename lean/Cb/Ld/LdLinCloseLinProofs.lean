-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseLinProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseLin.lean (the
closing of the test for linear constraints on the encoded index, for any plan of groups without a
splitting). An assembly: the step without rounds as a piece (`ldLinPre_step_cf`,
Cb/Ld/LdLinClosePreProofs.lean; `pieceTr_pure`, Cb/Ld/LdTowerKit.lean); a chain in front of a
closing (Cb/Ld/LdLinkCloseProofs.lean: `ldChain_front`); the test on chains (Cb/Ld/LdLinChain.lean).
Nothing is defined here that a statement reads.

Main names (statements and hypotheses: Cb/Ld/LdLinCloseLin.lean):
  `ldLinCl_chain`: the closing behind every chain (`OkFrom`, `SidesCT`).
  `ldLinCl_tail`: the test with this closing as a tail.

Limits: what the head of Cb/Ld/LdLinCloseLin.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLinCloseLin
import Cb.Ld.LdLinClosePreProofs
import Cb.Ld.LdLinkCloseProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype E] [Nonempty ι] in
theorem ldLinCl_chain : Spec.ldLinCl_chain E ι κ J Y := by
  classical
  intro C Q fq q A c₀ hS hQ hq
  have hT := ldLinPre_step_cf E ι κ J Y C Q.St Q.base fq hS
  have hp := pieceTr_pure Unit _ _ _ _ _ _ C.P.j6.cf (C.S.over Q.base).cf (C.stepF fq) C.toE
    (C.stepM fq) (fun _ w => C.back w) q Q.q ⟨hT.isLocal, hT.acc, hT.onOut, hT.keeps, hT.know⟩ hq
  exact ldChain_front Q c₀ (C.chain fq Q.base) q hQ ((Chain.okFrom_one c₀ _).2 (Or.inl hp.good))
    ((Chain.sidesC_one _ _ _).2
      (sideC_of_side _ _ _ _ _ _ _ _ _ _ _ ⟨hp.noHid, hp.noTie, hp.bears⟩))

theorem ldLinCl_tail : Spec.ldLinCl_tail E ι κ J Y := by
  intro C on0 εf S qa d Q fq hF hpy hS hSays hQ hq
  obtain ⟨h1, h2⟩ := ldLinCl_chain E ι κ J Y C Q fq (C.P.q5 S qa) _ (C.P.chain on0 S εf) hSays hQ hq
  exact ldLinC_tail C.P on0 εf S qa d (C.cZ Q fq) hF hpy hS h1 h2

end
end Cb
