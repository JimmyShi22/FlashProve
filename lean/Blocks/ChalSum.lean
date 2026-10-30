-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/ChalSum.lean: an upper bound on the hash blocks asked for in one round. (Words of this
library: lean/GLOSSARY.md.)

With the universal sampler the compiler makes every verifier message from hash blocks of λ bits
(Iop/Univ.lean: `Round.blocks` = ⌈log₂ (number of values)⌉ / λ + 2).
 * `cost_le`: for a verifier message with at most 2^b values, written `B2 r.Chal b`
   (Blocks/Sizes.lean), `bl lam b` = b / λ + 3 bounds `r.blocks lam + 1`.
Why: the step to one hash function asks for K + 1 in every round, K the largest number of blocks of
a round. Its variant (Rom/OverOneN.lean), with the table `need` of
Compile/Batch/NeedTable.lean, asks, in round i of protocol t, for the blocks below nb t i (a
parameter of `need`) and one more, the chaining value.
Limits: this file does not bound the sum of these numbers over the rounds of a protocol.
-/
import Blocks.ChalBits

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
open Iop

/-! ## One round -/

/-- upper bound on the blocks, with the chaining value, for a round whose verifier message has at
most 2^b values -/
def bl (lam b : ℕ) : ℕ := b / lam + 3


theorem cost_le {r : Round} {b : ℕ} (h : B2 r.Chal b) (lam : ℕ) : r.blocks lam + 1 ≤ bl lam b :=
  Nat.add_le_add_right (blocks_le h lam) 1

end Blocks
