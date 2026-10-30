-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/HeadSeal.lean: one closed sentence on a literal: the part of the step's
name "seal.behind" before its first dot is "seal". A statement with its proof.

  split_seal   "seal.behind".splitOn "." = ["seal", "behind"]
  head_seal    ProofFile.headOf "seal.behind" = "seal"   (headOf: Johnson/Desc/ProofFile/Places.lean)
Why it wants a proof. String.splitOn goes by a recursion that neither rfl nor decide gets through.
Here the simplifier walks String.splitOnAux step by step, deciding each comparison of places and
characters: the way of namesFit in OnBytes/K/ServedFreeItem.lean.
No native evaluation is trusted.
Who spends it. A law that says which place of the plan's table of steps is the last one.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile

theorem split_seal : "seal.behind".splitOn "." = ["seal", "behind"] := by
  simp (decide := true) (maxSteps := 10000000) [String.splitOn, String.splitOnAux.eq_def]

/-- **The head of the seal's step's name.** -/
theorem head_seal : headOf "seal.behind" = "seal" := by
  unfold headOf
  rw [split_seal]
  rfl

end ProofFile
