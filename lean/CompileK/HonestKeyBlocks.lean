-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
CompileK/HonestKeyBlocks.lean: how many blocks an answer has is no choice of the coding: every
coding of the compiler's typed oracles into one oracle of λ > 0 bits cuts the answer of the oracle o
into `blk K o` blocks.

Statements (`Rom.Spec.honestKey_blocksSame`, `Compile.Batch.Spec.honestKey_blocks`) and proofs.
Nothing assumed beyond the hypotheses of the statements and whatever the arguments hold as proofs.
Typed oracle, typed query:
lean/GLOSSARY.md. Over one oracle a typed query costs as many strings (queries to the one oracle:
lean/GLOSSARY.md) as its answer has blocks (Rom/Cost.lean). So, for λ > 0, a count, in strings, of
what an honest party of a compiled scheme asks does not depend on the coding: for a statement "for
every coding" no condition on the coding is needed, and the two conditions "one block a leaf, one a
vertex" (`m.blocks OracleName.leaf = 1`, `m.blocks OracleName.node = 1`) that the library's statements carry hold of
themselves where λ > 0.

`blk K` (Compile/Batch/ImplOf.lean) is K + 1 at a chain oracle `OracleName.fb t` and a ghost name
`OracleName.fbw t k`, 0 at `OracleName.ann`, 1 at `OracleName.leaf`, `OracleName.node`, the request trees' two (`OracleName.rleaf`,
`OracleName.rnode`), `OracleName.g t`, the spare oracle `OracleName.other`.

Why: a coding (Rom/Family.lean: `OracleCoding`) has, for every oracle o, a one-to-one correspondence of the
answers of o with the tuples of (blocks o) strings of λ bits. So the number of answers is
2^(λ · blocks o): for λ > 0 the family of oracles fixes the number.

Limits: how a coding cuts an answer into blocks (which bits stand in which block) is its choice:
"standard" (Compile/Batch/NeedTable.lean: `Std`) asks more than the number. This file says nothing
on any program.
-/
import Compile.Batch.ImplOf
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

namespace Rom
namespace Spec

/-- States: for `0 < lam`, the number of blocks is fixed by the number of answers. -/
def honestKey_blocksSame : Prop :=
  ∀ (S : OSpec) (lam : ℕ) (m : OracleCoding S lam) (o : S.ι) (b : ℕ),
    0 < lam → (S.Rng o ≃ (Fin b → Fin lam → Bool)) → m.blocks o = b

end Spec

theorem honestKey_blocksSame : Spec.honestKey_blocksSame := by
  intro S lam m o b hl e
  have h : Fintype.card (Fin (m.blocks o) → Fin lam → Bool) =
      Fintype.card (Fin b → Fin lam → Bool) :=
    Fintype.card_congr ((m.rng o).symm.trans e)
  have h1 : ∀ n : ℕ, Fintype.card (Fin n → Fin lam → Bool) = 2 ^ (lam * n) :=
    fun n => by simp [pow_mul]
  rw [h1, h1] at h
  exact Nat.eq_of_mul_eq_mul_left hl (Nat.pow_right_injective (le_refl 2) h)

end Rom

namespace Compile.Batch
open Iop Rom
namespace Spec

/-- States: for `0 < lam`, every coding of the compiler's typed oracles has the same numbers of
blocks. -/
def honestKey_blocks : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (lam K : ℕ) (m : OracleCoding (spec lam K L) lam),
    0 < lam → ∀ o : OracleName, m.blocks o = blk K o

end Spec

theorem honestKey_blocks : Spec.honestKey_blocks := fun _ _ L lam K m hl o =>
  Rom.honestKey_blocksSame (spec lam K L) lam m o (blk K o) hl (rngEquiv lam K o)

end Compile.Batch
