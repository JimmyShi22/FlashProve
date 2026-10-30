-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/Sound.lean: helper lemmas for soundness with slots: bad values for a doomed prover.

`BatchSound.pick`, with `pick_within`, `pick_clean`: see its docstring.

Limits: this file does not prove (Snd-B) (`BatchInteractiveOracleProof.SndB`, Iop/Batch.lean) for any protocol.
-/
import Blocks.Batch.Kit
import Blocks.Wired
import Blocks.LowerKit
import Mathlib.Data.FinEnum
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Blocks

open Iop Prob

namespace BatchSound

/-! ## Bad values for a doomed prover -/

open Classical in
/-- Bad sets within the errors ε such that every full transcript without a bad value has the
property "lost" (for instance: the verifier rejects), if there are such sets; else empty sets. -/
def pick (s : Shape) (ε : Err s) (lost : Tr s → Prop) : BadFam s :=
  if h : ∃ B : BadFam s, B.Within ε ∧ ∀ τ, B.Clean τ → lost τ then h.choose else BadFam.empty s

theorem pick_within (s : Shape) (ε : Err s) (lost : Tr s → Prop) : (pick s ε lost).Within ε := by
  unfold pick
  split_ifs with h
  · exact h.choose_spec.1
  · exact BadFam.empty_within s ε

theorem pick_clean {s : Shape} {ε : Err s} {lost : Tr s → Prop} (h : Doomed s ε lost)
    {τ : Tr s} (hτ : (pick s ε lost).Clean τ) : lost τ := by
  have h' := Doomed.exists_badFam s ε lost h
  unfold pick at hτ
  rw [dif_pos h'] at hτ
  exact h'.choose_spec.2 τ hτ

end BatchSound

end Blocks
