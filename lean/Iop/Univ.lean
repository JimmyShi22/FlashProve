-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Univ.lean: one challenge sampler for every round, from tuples of hash blocks of λ bits.

Definitions, and the statement `Spec.univGood` (proof: Iop/PullProofs.lean) (words of this library:
lean/GLOSSARY.md).

The map from the underlying uniform strings to the challenge is a part of the protocol. The
numbering of the values of `Chal` is given as data (`Shape.NumChal`, Iop/Num.lean), and the hash
blocks are read as a number by their binary value (`Num.blocks`). Here the whole challenge of a
round is computed at once, for 0 < λ: number the values of Chal, take k blocks with 2^(k λ) ≥ 2^λ *
card Chal, read them as one number and reduce it modulo card Chal. Every fibre has at most 2^(k λ) /
card Chal + 1 elements, so every round's error grows by the factor 1 + 2^-λ at most, whatever the
type of the challenge is.
-/
import Iop.Pull
import Iop.Wire
import Iop.Num

namespace Iop
open scoped ENNReal

/-- The number of hash blocks for a round. -/
def Round.blocks (lam : ℕ) (r : Round) : ℕ := Nat.clog 2 (Fintype.card r.Chal) / lam + 2

/-- The universal sampler of a round, for a numbering nc of the values of its challenge: the binary
value of the hash blocks, modulo the number of values. -/
def Sampler.univ (lam : ℕ) (r : Round) (nc : r.Chal ≃ Fin (Fintype.card r.Chal)) : Sampler r where
  Src := Fin (r.blocks lam) → Dig lam
  φ := fun s => nc.symm
    ⟨(Num.blocks lam (r.blocks lam) s).val % Fintype.card r.Chal, Nat.mod_lt _ Fintype.card_pos⟩
  w := Fintype.card (Fin (r.blocks lam) → Dig lam) / Fintype.card r.Chal + 1

/-- The universal samplers of all rounds, for given numberings. -/
def Samplers.univ (lam : ℕ) : (s : Shape) → s.NumChal → Samplers s
  | [], _ => PUnit.unit
  | r :: s, (nc, ncs) => (Sampler.univ lam r nc, Samplers.univ lam s ncs)

namespace Spec

/-- Statement: for 0 < λ the universal samplers satisfy `Samplers.Good`, with κ = 1 + 2^-λ for each
round and K = κ^(number of rounds). -/
def univGood : Prop :=
  ∀ (lam : ℕ), 0 < lam → ∀ (s : Shape) (pt : s.NumChal),
    (Samplers.univ lam s pt).Good (1 + (2 ^ lam : ℝ≥0∞)⁻¹) ((1 + (2 ^ lam : ℝ≥0∞)⁻¹) ^ s.length)

end Spec

end Iop
