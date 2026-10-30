-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/All/CompleteAsIOPEveryCoin.lean: a bound at every coin of the prover is a bound over
coins and challenges together.
-/
import Johnson.Prover.All.CompleteAsIOPForTheCompiler

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.Prover
open Prob
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- **Every coin gives the joint form.** -/
theorem everyCoinGivesFailsRarely : EveryCoinGivesFailsRarely := by
  intro Y E Q Wt H work y w x error h
  show pr (unif (H.Coin × Rho Q.shape)) {d | FailsAt H work y w x d.1 (work.cleared d.2)} ≤ error
  rw [unif_prod, pr_prod]
  exact expect_le_of_forall_le _ fun c _ => h c

end OnBytes.Prover

#print axioms OnBytes.Prover.everyCoinGivesFailsRarely
