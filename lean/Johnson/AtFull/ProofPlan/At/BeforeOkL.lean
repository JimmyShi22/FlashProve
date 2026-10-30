-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/At/BeforeOkL.lean: ONE OF THE TESTS ON THE PLAN (`FileDescription.planOk`,
Johnson/Desc/Block.lean) AT THE WRITTEN DESCRIPTION `WP` (Johnson/AtFull/ProofPlan/WP.lean):
beforeOk. A joining: nothing is evaluated here: `P2Law.OneWalk.beforeOk_tab`
(Johnson/AtFull/ProofPlan/OneWalk.lean) at the three tables (At/Tab1.lean, Tab2.lean, Tab3.lean) and
the three answers over them (At/BeforeL1.lean, BeforeL2.lean, BeforeL3.lean).

Limits. A fact on written values. That the proof file's description is alike to `WP` is not said
here. Nothing on soundness.

Terms: lean/GLOSSARY.md.
-/
import Johnson.AtFull.ProofPlan.At.Tab1
import Johnson.AtFull.ProofPlan.At.Tab2
import Johnson.AtFull.ProofPlan.At.Tab3
import Johnson.AtFull.ProofPlan.At.BeforeL1
import Johnson.AtFull.ProofPlan.At.BeforeL2
import Johnson.AtFull.ProofPlan.At.BeforeL3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.ProofPlan

open VerifiableInference.Desc
open P2Law.OneWalk (beforeOk_tab)

theorem wp_beforeOkL : WP.beforeOk = true := by
  rw [beforeOk_tab WP wp_tab₁ wp_tab₂ wp_tab₃, wp_beforeL₁, wp_beforeL₂, wp_beforeL₃]
  rfl

end P2Law.ProofPlan

#print axioms P2Law.ProofPlan.wp_beforeOkL
