-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/RngLkpProofs.lean: the statements of Cb/Gen/RngLkp.lean, proved.
-/
import Cb.Gen.RngLkp

set_option autoImplicit false

namespace Cb
open Cb.Rng Cb.Lkp

theorem inTable_tabMod : Spec.inTable_tabMod := by
  intro E _ n T q key hq hT
  refine forall_congr' fun b => forall_congr' fun _ => ?_
  constructor
  · rintro ⟨u, _, hu⟩
    exact ⟨u % q, Nat.mod_lt _ hq, hu⟩
  · rintro ⟨a, ha, hk⟩
    refine ⟨a, lt_of_lt_of_le ha hT, ?_⟩
    unfold tabMod
    rw [Nat.mod_eq_of_lt ha]
    exact hk

theorem inTable_pad : Spec.inTable_pad := by
  intro E _ n T q K v hq hT hK
  rw [inTable_tabMod E n T q (pad K v) hq hT]
  constructor
  · intro h b hb
    have := h b (lt_of_lt_of_le hb hK)
    unfold pad at this
    rwa [if_pos hb] at this
  · intro h b _
    unfold pad
    by_cases hb : b < K
    · rw [if_pos hb]
      exact h b hb
    · rw [if_neg hb]
      exact ⟨0, hq, by simp⟩

end Cb
