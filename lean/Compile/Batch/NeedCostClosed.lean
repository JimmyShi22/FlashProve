-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/NeedCostClosed.lean: the trees of one execution cost at most twice `cTrees`, the count
in which the library's other explicit bounds are stated. For every wire record, with or without
proof-of-work bits (words of this library: lean/GLOSSARY.md).
    `tr_sum_le`      tr0 + n · trJ ≤ 2 · cTrees s A W n (`tr0`, `trJ`: Compile/Batch/NeedCostP.lean;
                     `cTrees`: the leaves of all trees of one execution with n slots:
                     Compile/Batch/Counts.lean; a tree costs its leaves and inner nodes)
Notation: `s`, `A`, `W`: a `Shape`, a `RoundSplits s`, a `RoundsQueryLayout lam K s A` (Iop/BatchWire.lean: a `WireRB`
for each round); `tr0`, `trJ`: the trees over the shared components, and over a slot's components,
of all rounds: the sums of `cost0 w` = tr w.depth0 and of `costJ w` = tr w.depthJ; `tr d`: the
leaves and the inner nodes of a tree of depth d (Compile/Batch/NeedCostTree.lean).
Limits: an upper bound. An inequality between numbers: nothing here bounds the queries of an
algorithm. The explicit bounds on the committer's and the prover's queries over one hash function,
if only the marked blocks are queried, are not in this library.
-/
import Compile.Batch.NeedCostP
import Compile.Batch.CountsGr

set_option autoImplicit false

open Rom Iop

namespace Compile.Batch
namespace Need
open Compile.Need (sumNb)

section One
variable {lam K : ℕ} (nbf : ℕ → ℕ)


variable {nbf}


/-- the trees of one execution with n slots: leaves and inner nodes -/
theorem tr_sum_le (n : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A),
      tr0 s A W + n * trJ s A W ≤ 2 * cTrees s A W n
  | [], _, _ => Nat.zero_le _
  | _ :: s, (_, A), (w, W) => by
      have ih := tr_sum_le n s A W
      have h0 : cost0 w ≤ 2 * 2 ^ w.depth0 := tr_le _
      have hJ : n * costJ w ≤ n * (2 * 2 ^ w.depthJ) := Nat.mul_le_mul_left _ (tr_le _)
      show (cost0 w + tr0 s A W) + n * (costJ w + trJ s A W) ≤
        2 * (n * 2 ^ w.depthJ + 2 ^ w.depth0 + cTrees s A W n)
      have e : n * (2 * 2 ^ w.depthJ) = 2 * (n * 2 ^ w.depthJ) := by ring
      rw [Nat.mul_add n]
      omega

variable (nbf)


end One

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (p : Params) (nb : Tag → ℕ → ℕ)


end Need
end Compile.Batch
