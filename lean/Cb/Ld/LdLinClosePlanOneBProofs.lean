-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLinClosePlanOneBProofs.lean: the proofs of the statements of Cb/Ld/LdLinClosePlanOneB.lean
(the rest of the plan without a splitting, with one group, for a batch). By composition.
Nothing is defined here.

Main names (statements and hypotheses: Cb/Ld/LdLinClosePlanOneB.lean):
  `ldRowsOneB_kb`: knowledge soundness of the annotated links of `X.oneA w₀`
  `ldRowsOneB_v`: the honest side `X.oneV N q₀ w₀`
-/
import Cb.Ld.LdLinClosePlanOneB

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem ldRowsOneB_same : Spec.ldRowsOneB_same := fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl

theorem ldRowsOneB_kb : Spec.ldRowsOneB_kb := by
  intro E _ _ S E₀ Wp Cl B _ rows X w₀ N hk hX
  haveI : IsEmpty (S.sub X.kp).O := ⟨fun o => hk o.1 o.2⟩
  exact ldPlanB_cons_local E S E₀ Wp X.run (LdTcA.nil (S.sub X.kp) E₀ Wp w₀) X.d X.d' N (ldKeyU _)
    (ldKeyU _) id hX (ldPlanB_nil E _ E₀ Wp w₀ N _) fun _ _ _ _ => rfl

theorem ldRowsOneB_v : Spec.ldRowsOneB_v := by
  intro E ι κ J Y _ _ _ _ _ _ _ C p Cl B _ rows X w₀ N q₀ hk hX hq
  haveI : IsEmpty (p.S₂.sub X.kp).O := ⟨fun o => hk o.1 o.2⟩
  refine ldPlanV_cons_local E p.S₂ C.E₀ C.Wpa N X.run (LdTcA.nil (p.S₂.sub X.kp) C.E₀ C.Wpa w₀)
    X.d X.d' ⟨C.P.Sh6, fun _ _ _ _ => True, p.qB₂ N q₀ (X.bOne N)⟩ (fun _ _ _ _ => True)
    (X.qEnd N q₀) (LdTcV.nil (p.S₂.sub X.kp) C.E₀ C.Wpa w₀ _) hX ?_ (fun _ _ _ _ => trivial) ?_ ?_
  · exact ldPlanV_nil E _ C.E₀ C.Wpa w₀ N _ fun Jn =>
      ldDemandV_empty E _ _ N _ _ _ (fun _ _ => hq) Jn
  · exact ldRunV_bears_local E p.S₂ X.run _ _ _ _ X.d X.d' N _ _ hX
      (ldDemandV_local E p.S₂ X.run _ _ _ _ X.d X.d' N (fun a => C.isSh a.1.1)
        (QFam.each q₀) (fun _ => 0) _ hX)
  · exact ldDemandV_her E _ _ N _ _ _ ((qfam_her _ extNone N).1 _)

end Cb
