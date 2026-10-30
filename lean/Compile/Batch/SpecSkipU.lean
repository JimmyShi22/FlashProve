-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecSkipU.lean: the prover that makes no query for an empty slot is the prover of the
compiled scheme without the work of the empty slots. Statement only. (Words of this library:
lean/GLOSSARY.md.)

`Spec.skipPp`: the two provers `Pp` (Compile/Batch/Star.lean: an empty slot of a batch is hashed
like a full one) and `PpU` (Compile/Batch/StarU.lean: no query and no tree for an empty slot, and
its leaf of the request tree is sampled) are in the relation `Rom.Skip`, with equal results. `Pp` is
the first program. The two conditions on the correspondence w at the start:
* `w.ρ 0 0`: both programs use the number 0 where a list of tokens has no entry (`headD 0`,
  `getD j 0`, the default of `rootOf`, `pathOf` and `ancOf`); it has to denote the same string on
  both sides;
* each token of a salted leaf in the tree of a copy in the key denotes the same string on both
  sides: both programs are given the same key.

Notation: `Rom.Skip Q w c₁ c₂` (Rom/Skip.lean): a `Prop` on a `Rom.Wd` and two programs (`Step`,
Rom/Defer.lean); "Q: what holds of the two results, with the correspondence at the end."; `w`: a
`Rom.Wd` (Rom/Skip.lean): "how the tokens of two programs correspond"; `w.ρ`: of type
`Tok → Tok → Prop`; `k`: an `IskH lam L`, `fr`: of type `ℕ → Bool`, `xs`: a `List X`: the arguments
of `Pp` (Compile/Batch/Star.lean) and of `PpU`.

Limits: it is a statement about the two programs as terms. It contains no probability, and what the
relation means for runs in mode I (Rom/Defer.lean) is proved in Rom/SkipRun.lean.

The proof is in Compile/Batch/SkipU.lean and the files that it imports.
-/
import Compile.Batch.StarU
import Rom.Skip

noncomputable section

namespace Compile.Batch
open Iop Rom

/-- `PpU` is `Pp` without the work of the empty slots, under two conditions on w. -/
def Spec.skipPp : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (k : IskH lam L) (fr : ℕ → Bool) (xs : List X) (w : Rom.Wd),
    w.ρ 0 0 → (∀ lf ∈ k.leaves, ∀ s s', some (s, s') ∈ lf.node.tree.salts → w.ρ s s ∧ w.ρ s' s') →
    Rom.Skip (fun _ a₁ a₂ => a₁ = a₂) w (Pp W WP p k fr xs) (PpU W WP p k fr xs)

end Compile.Batch
