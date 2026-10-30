-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ChalBits.lean: how many hash blocks of λ bits a verifier message needs.

With the universal sampler the compiler makes every verifier message from hash blocks
(Iop/Univ.lean: `Round.blocks` = ⌈log₂ (number of values)⌉ / λ + 2; / rounds down). `blocks_le`: see
its docstring; `blocks_le_of`: the same, for every K ≥ b / λ + 2. `B2.fin`: `Fin n` has at most 2^d
elements if n ≤ 2^d.

Notation: `lam`: λ; `B2 α b` (Blocks/Sizes.lean): `Nat.card α ≤ 2 ^ b`: a finite type has at most
2^b elements.
-/
import Blocks.Sizes
import Iop.WireOf

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
open Iop

/-! ## Lemmas -/

theorem B2.fin {n d : ℕ} (h : n ≤ 2 ^ d) : B2 (Fin n) d := by
  unfold B2
  rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  exact h

/-- a round whose verifier message has at most 2^b values needs at most b / λ + 2 blocks -/
theorem blocks_le {r : Round} {b : ℕ} (h : B2 r.Chal b) (lam : ℕ) : r.blocks lam ≤ b / lam + 2 := by
  unfold Round.blocks
  refine Nat.add_le_add_right (Nat.div_le_div_right ((Nat.clog_le_iff_le_pow (by decide)).2 ?_)) 2
  rw [← Nat.card_eq_fintype_card]
  exact h

theorem blocks_le_of {r : Round} {b K : ℕ} (lam : ℕ) (h : B2 r.Chal b) (hK : b / lam + 2 ≤ K) :
    r.blocks lam ≤ K :=
  le_trans (blocks_le h lam) hK

end Blocks
