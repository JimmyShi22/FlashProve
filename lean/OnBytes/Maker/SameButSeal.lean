-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/SameButSeal.lean: two lists of draws that are equal but for the last one's digest
(OnBytes/TypedOracleCompiler/Run/ChainF.lean, `SameButSeal`) are alike draw by draw up to the digests
(OnBytes/TypedOracleCompiler/Laws/LawAlike.lean, `LAlike DrawnAlike`), the sides swapped.

What is not claimed. The converse.


-/
import OnBytes.TypedOracleCompiler.Run.ChainF
import OnBytes.TypedOracleCompiler.Laws.LawAlike

set_option autoImplicit false

namespace OnBytes.Maker

open OnBytes.TwoLaws TypedOracleCompiler.Run.PQ

theorem lAlike_of_sameButSeal : ∀ (as bs : List Fmt.Drawn), SameButSeal as bs →
    LAlike DrawnAlike bs as
  | [], [], _ => .nil
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim
  | a :: as, b :: bs, h => by
    obtain ⟨h1, h2⟩ := h
    refine .cons ?_ (lAlike_of_sameButSeal as bs h2)
    by_cases e : bs.isEmpty = true
    · rw [if_pos e] at h1
      exact ⟨h1.1.symm, h1.2.1.symm, h1.2.2.symm⟩
    · rw [if_neg e] at h1
      exact h1 ▸ DrawnAlike.refl _

end OnBytes.Maker
