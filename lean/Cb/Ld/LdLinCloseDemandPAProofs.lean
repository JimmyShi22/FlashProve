-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandPAProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseDemandPA.lean
(the write-up's plan: the term on which a batch is built). By composition.
Nothing is defined here.

Main names (statements and hypotheses: Cb/Ld/LdLinCloseDemandPA.lean):
  `ldLinPpT_behindA`: `T.QF` in order after the core and the step.
  `ldLinPpT_tailA`: the test with `C.cZ T.QF (C.fqP T.fa)` as a tail.
  `ldLinPpT_topA`: the same, under the hypotheses of `Spec.ldLinPpT_top`.
"The write-up": one of our own texts on this protocol (lean/CREDITS.md); it is not in this
repository.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldLinPpT_tailA` or
   `ldLinPpT_topA` can be met together. -/
import Cb.Ld.LdLinCloseDemandPA
import Cb.Ld.LdLinCloseDemandPProofs
import Cb.Ld.LdLinCloseDemandTProofs
import Cb.Ld.LdFrontFreshProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

theorem ldLinPpT_behindA : Spec.ldLinPpT_behindA E ι κ J Y := by
  intro C p T on0 εf Sn Rd Rr hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' r0 f0
  exact ldAlt_front E C.S C.E₀ C.Wpa (p.x₁ T.Q'.base) T.Q T.front _
    ((C.P.chain on0 Sn εf).append (C.chain (C.fqP T.fa) (p.x₁ T.Q'.base).A)) Rd Rr
    (C.step_ok E ι κ J Y on0 εf Sn _ _ hF hpy hS
      (ldLinPp_says E ι κ J Y C p _ T.Q'.base T.fa hr hA))
    (ldLinPp_hyp E ι κ J Y C p _ T.Q'.base hP hK) (ldLinPp_sd E ι κ J Y C p _ T.Q'.base T.Q.q)
    (ldLinPp_zk E ι κ J Y C p _ T.Q'.base Rd Rr _ r0
      (idle_fresh E Unit (p.x₁ T.Q'.base).stage _ _ _ _ E _ f0))
    (ldAlt_of_ok E C.S C.E₀ C.Wpa T.Q _ _ (ldLinPpT_ok E ι κ J Y C p T h₁ h₂ h₃ hQ'))

theorem ldLinPpT_tailA : Spec.ldLinPpT_tailA E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd Rr hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ'
    r0 f0 hq hqa i1 i2 i3 i4
  exact ldLinAlt_tail E ι κ J Y C on0 εf Sn qa d T.QF (C.fqP T.fa) hF hpy hS
    (ldLinPp_says E ι κ J Y C p _ T.Q'.base T.fa hr hA)
    (ldLinPpT_behindA E ι κ J Y C p T on0 εf Sn Rd Rr hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' r0 f0)
    (ldLinPpT_demand E ι κ J Y C p T Sn qa q₀ ba b' hq hqa i1 i2 i3 i4)

open Classical in
theorem ldLinPpT_topA : Spec.ldLinPpT_topA E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd n₀ U₀ hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' r0 e0
    d0 l0 hq hqa i1 i2 i3 i4
  refine ldLinPpT_tailA E ι κ J Y C p T on0 εf Sn qa d q₀ ba b' Rd (fun _ => False)
    hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' r0 ?_ hq hqa i1 i2 i3 i4
  rw [e0]
  exact ldLinSp_entO E ι κ J Y C on0 εf Sn (p.x₁ T.Q'.base) (C.fqP T.fa) U₀ Rd (fun _ => False)
    n₀ l0 hS.hidO (fun _ h => h) d0

end
end Cb
