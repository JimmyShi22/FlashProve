-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Local.lean: two lemmas on positions of a part of a list of rounds, as positions of the whole
(`posR_eq_right`, `read_posR_eq_iff`).
-/
import Blocks.LowerKit
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Blocks

open Iop

/-! ## Positions of a part, as positions of the whole -/

theorem posR_eq_right : ∀ {s t : Shape} (p : OPos t), posR (s := s) p = OPos.right (s := s) p
  | [], _, _ => rfl
  | _ :: s, _, p => congrArg Sum.inr (posR_eq_right (s := s) p)

/-- Two transcripts agree at a position of the second part if and only if their second parts agree
there. -/
theorem read_posR_eq_iff {s t : Shape} (τ τ' : Tr (s ++ t)) (p : OPos t) :
    τ.read (posR (s := s) p) = τ'.read (posR (s := s) p) ↔
    (Tr.snd (s := s) τ).read p = (Tr.snd (s := s) τ').read p := by
  rw [posR_eq_right]
  exact Tr.read_right_eq_iff τ τ' p

end Blocks
