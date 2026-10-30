-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdGroupProofs.lean: the proofs of the statements of Cb/Ld/LdGroup.lean.

`ldGroup_run` is an assembly: the bridge (`ldBat_bridge`, Cb/Ld/LdBatSigProofs.lean), a piece beside
a carried part (`pieceTr_beside`, Cb/Ld/LdGroupKit.lean), a piece after a piece (`pieceTr_seq`,
Cb/Ld/LdTowerKit.lean).

Main names (statements and hypotheses: Cb/Ld/LdGroup.lean):
  `ldGroup_run`: under the hypotheses of `Spec.ldGroup_run`, a run on a group (`ldRunG`) is a piece
    of a chain (`PieceTr`, Cb/Ld/LdTowerKit.lean).
  `ldGroup_run_data`: see its statement in Cb/Ld/LdGroup.lean.

Limits: what the head of Cb/Ld/LdGroup.lean lists as not said is not said here either.
-/
import Cb.Ld.LdGroup
import Cb.Ld.LdBatSigProofs

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR Cb.Ood

open Classical in
theorem ldGroup_run : Spec.ldGroup_run := by
  intro E B Kc St₀ Wp _ _ _ S G _ kp _ Sb sl Z L E₀ A₀ hc d b Bk t t' qi qF hZ hL hF hB hq
  exact pieceTr_seq Kc _ _ _ _ _ _ (ldBridge G kp Sb Z St₀ E₀)
    (Bk.R.keep (LdCarX kp St₀) (LdCarE kp E₀)) _ _ _ (ldBridgeH G kp Sb Z St₀ Wp E₀)
    ((Bk.H.keep (LdCarX kp St₀) (LdCarE kp E₀)).carry (LdCarW kp Wp)) _ _ _ _ _ d _ _ qi
    (besideQ ((G.joint Sb sl Z).atMost t) qF) (besideQ (b.atMost t') qF)
    (ldBat_bridge E B Kc St₀ Wp S G kp Sb sl Z L E₀ A₀ hc qi _ hZ hL hF hq)
    (pieceTr_beside Kc _ _ _ _ _ _ Bk.R _ _ _ Bk.H _ _ Bk.ext Bk.N ((S.sub kp).over A₀) _ _ qF hB)

theorem ldGroup_run_data : Spec.ldGroup_run_data := by
  intro E B Kc St₀ _ _ _ S G _ kp _ Sb sl Z err E₀ b Bk
  refine ⟨?_, rfl, rfl, rfl⟩
  show ((ldBridge G kp Sb Z St₀ E₀).shape ++ Bk.R.shape).length = _
  rw [List.length_append, Nat.add_comm]
  rfl

end Cb
