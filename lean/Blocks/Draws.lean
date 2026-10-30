-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Draws.lean: lemmas for the challenge samplers of Blocks/ (`BS`, Iop/Draw.lean).
  `good_rep`, `good_app`: the bias condition `Shape.Draws.Good` for a round repeated n times before
  a list of rounds, and for two lists in a row. `Pow2.of_log`: see its statement.
`Shape.Draws.Good κ` asks `BS.Good` with κ^b of every round's sampler, b its number of blocks.
`BS.Good` with κ' says: every value has at most w preimages, and w · (number of values) ≤ κ' ·
(number of tuples of b blocks).
-/
import Blocks.Batch.Numbering
import Iop.DrawRule
import Iop.BatchWireDraw

set_option linter.unusedSectionVars false

namespace Blocks
open Iop

variable {lam : ℕ}

/-! ## Repeated rounds; two lists -/

theorem good_rep {κ : ENNReal} (r : Round) (h : BS lam r.Chal) (hg : h.Good (κ ^ h.b)) :
    ∀ (n : ℕ) {t : Shape} (d : t.Draws lam), Shape.Draws.Good κ t d →
      Shape.Draws.Good κ (List.replicate n r ++ t) (Shape.Draws.rep r h n d)
  | 0, _, _, hd => hd
  | n + 1, _, d, hd => ⟨hg, good_rep r h hg n d hd⟩

theorem good_app {κ : ENNReal} :
    ∀ {s t : Shape} (a : s.Draws lam) (b : t.Draws lam), Shape.Draws.Good κ s a →
      Shape.Draws.Good κ t b → Shape.Draws.Good κ (s ++ t) (Shape.Draws.app a b)
  | [], _, _, _, _, hb => hb
  | _ :: _, _, (_, as), b, ha, hb => ⟨ha.1, good_app as b ha.2 hb⟩

/-! ## Powers of two -/

section Rule
variable {F : Type} [Field F] {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
  (bE : BS lam E) (sl : ℕ)


theorem Pow2.of_log {n : ℕ} (h : n = 2 ^ Nat.log 2 n) : Pow2 n := ⟨⟨_, h⟩⟩




end Rule

end Blocks
