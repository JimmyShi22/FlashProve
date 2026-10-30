-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinCloseDemandPProofs.lean: the proofs of the statements of Cb/Ld/LdLinCloseDemandP.lean
(the plan of this protocol's technical report (lean/CREDITS.md): the whole closing). By composition.
Nothing is defined here.

Main names (statements and hypotheses: Cb/Ld/LdLinCloseDemandP.lean):
  `ldLinPpT_ok`: `T.Q`, the three tests and then the closing of what the preamble left, in order.
  `ldLinPpT_demand`: its demand within what the three sendings bear.
  `ldLinPpT_tail`, `ldLinPpT_top`: the test with the whole closing (`C.cZf ..`) as a tail, under two
    sets of hypotheses.
-/
/- Limits: no theorem of this library states that the hypotheses of `ldLinPpT_tail` or
   `ldLinPpT_top` can be met together. -/
import Cb.Ld.LdLinCloseDemandP
import Cb.Ld.LdLinClosePlanPProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

section
variable (E ι κ J Y : Type)
  [Field E] [Fintype E] [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype J] [Fintype Y]

omit [Fintype ι] [Nonempty ι] in
theorem ldLinPpT_ok : Spec.ldLinPpT_ok E ι κ J Y := fun C p T h₁ h₂ h₃ hQ =>
  ldChain_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' h₁
    (ldChain_cons E p.S₁ C.E₀ C.Wpa T.D₂ _ T.d₂ T.d₂' h₂
      (ldChain_cons E p.S₂ C.E₀ C.Wpa T.D₃ T.Q' T.d₃ T.d₃' h₃ hQ))

omit [Fintype ι] [Nonempty ι] in
open Classical in
theorem ldLinPpT_demand : Spec.ldLinPpT_demand E ι κ J Y := by
  intro C p T Sn qa q₀ ba b' hQ hqa hA hW hU hO V hV
  exact ldDemand_lin E ι κ J Y C Sn qa q₀ ba _ hqa hA hW hU hO V
    (ldDemand_cons E C.S C.E₀ C.Wpa T.D₁ _ T.d₁ T.d₁' q₀ _
      (ldDemand_cons E p.S₁ C.E₀ C.Wpa T.D₂ _ T.d₂ T.d₂' q₀ _
        (ldDemand_cons E p.S₂ C.E₀ C.Wpa T.D₃ T.Q' T.d₃ T.d₃' q₀ b' hQ))
      V hV)

theorem ldLinPpT_tail : Spec.ldLinPpT_tail E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd Rr hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ'
    r0 f0 hq hqa i1 i2 i3 i4
  exact ldLinSp_tail E ι κ J Y C on0 εf Sn qa d (p.x₁ T.Q'.base) T.Q (C.fqP T.fa) T.front Rd Rr hF
    hpy hS (ldLinPp_says E ι κ J Y C p _ T.Q'.base T.fa hr hA)
    (ldLinPpT_ok E ι κ J Y C p T h₁ h₂ h₃ hQ')
    (ldLinPpT_demand E ι κ J Y C p T Sn qa q₀ ba b' hq hqa i1 i2 i3 i4)
    (ldLinPp_hyp E ι κ J Y C p _ T.Q'.base hP hK) (ldLinPp_sd E ι κ J Y C p _ T.Q'.base T.Q.q)
    (ldLinPp_zk E ι κ J Y C p _ T.Q'.base Rd Rr
      (fun g =>
        ((C.P.chain on0 Sn εf).append (C.chain (C.fqP T.fa) (p.x₁ T.Q'.base).A)).FreshFor
          g.kc g.Mk g.put)
      r0 f0)

open Classical in
theorem ldLinPpT_top : Spec.ldLinPpT_top E ι κ J Y := by
  intro C p T on0 εf Sn qa d q₀ ba b' Rd n₀ U₀ hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' r0 e0
    d0 l0 hq hqa i1 i2 i3 i4
  refine ldLinPpT_tail E ι κ J Y C p T on0 εf Sn qa d q₀ ba b' Rd (fun _ => False)
    hF hpy hS hr hA hP hK h₁ h₂ h₃ hQ' r0 ?_ hq hqa i1 i2 i3 i4
  rw [e0]
  exact ldLinSp_entO E ι κ J Y C on0 εf Sn (p.x₁ T.Q'.base) (C.fqP T.fa) U₀ Rd (fun _ => False)
    n₀ l0 hS.hidO (fun _ h => h) d0

end
end Cb
