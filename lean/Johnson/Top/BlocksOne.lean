-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/BlocksOne.lean: an oracle whose answers are the bit strings of one block has one block
in every coding of the typed oracles in one hash function.

One theorem and two instances, with their proofs.
Main names:
  `Rom.OracleCoding.blocks_eq_one`: if the answers of the oracle o are in bijection with the strings of
    lam > 0 bits, then `m.blocks o = 1`, for every `m : Rom.OracleCoding S lam`: by `m.rng o` and a count
    (`Rom.blocks_eq_of_equiv`, Rom/CutKit.lean).
  `Compile.Batch.blocks_leaf`, `blocks_node`: the instances at the leaves and the inner nodes of the
    hash trees of Compile/Batch/Oracles.lean.

-/
import Rom.CutKit
import Compile.Batch.Oracles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Rom

theorem OracleCoding.blocks_eq_one {S : OSpec} {lam : ℕ} (m : OracleCoding S lam) (hl : 0 < lam) (o : S.ι)
    (e : S.Rng o ≃ (Fin lam → Bool)) : m.blocks o = 1 :=
  blocks_eq_of_equiv hl
    (((m.rng o).symm.trans e).trans (Equiv.funUnique (Fin 1) (Fin lam → Bool)).symm)

end Rom

namespace Compile.Batch
open Rom

theorem blocks_leaf {I X : Type} {lam K : ℕ} {L : Iop.BatchProtocol I X} (m : OracleCoding (spec lam K L) lam)
    (hl : 0 < lam) :
    m.blocks OracleName.leaf = 1 :=
  m.blocks_eq_one hl OracleName.leaf (Equiv.refl _)

theorem blocks_node {I X : Type} {lam K : ℕ} {L : Iop.BatchProtocol I X} (m : OracleCoding (spec lam K L) lam)
    (hl : 0 < lam) :
    m.blocks OracleName.node = 1 :=
  m.blocks_eq_one hl OracleName.node (Equiv.refl _)

end Compile.Batch

#print axioms Compile.Batch.blocks_leaf
#print axioms Compile.Batch.blocks_node
