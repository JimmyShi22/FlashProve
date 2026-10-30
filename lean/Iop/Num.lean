-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/Num.lean: numberings of finite types, as data.

The compiled scheme has to turn hash blocks into challenges and coins, and oracle positions into
leaves of a tree. For that it needs a numbering of each finite type concerned. A numbering is a
bijection with Fin (number of elements). No numbering of this file is obtained from a statement of
existence.

That is said of this file alone: `numPosOf` and
`numPosBOf` (CompileK/FitExists.lean) are numberings built from `Fintype.equivFin`: by choice, as
that file's head says.
Mathlib's class FinEnum builds computable numberings of products, sums, functions and so on from
those of the parts (Num.ofFinEnum).
-/
import Mathlib.Data.FinEnum
import Mathlib.Data.FinEnum.Option
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Iop.Shape

namespace Iop

/-- A numbering of a finite type. -/
abbrev Num (α : Type) [Fintype α] : Type := α ≃ Fin (Fintype.card α)

/-- The numbering that Mathlib's `FinEnum` computes. -/
def Num.ofFinEnum (α : Type) [FinEnum α] [Fintype α] : Num α :=
  FinEnum.equiv.trans (finCongr FinEnum.card_eq_fintypeCard)

instance : FinEnum Bool := FinEnum.ofEquiv (Fin 2) finTwoEquiv.symm

/-- The binary value of k blocks of lam bits, as a numbering: bit i of block j has the weight 2^i
(2^lam)^j. -/
def Num.blocks (lam k : ℕ) : Num (Fin k → Fin lam → Bool) :=
  ((Equiv.piCongrRight fun _ : Fin k =>
        ((Equiv.piCongrRight fun _ : Fin lam => finTwoEquiv.symm).trans
          (finFunctionFinEquiv (m := 2) (n := lam)))).trans
      (finFunctionFinEquiv (m := 2 ^ lam) (n := k))).trans
    (finCongr (by simp [Fintype.card_fin, Fintype.card_bool]))

/-! ## Numberings for a list of rounds

They are not fields of `Round` or `Round.IsPoint`: whoever builds a protocol supplies them as
further data. -/

/-- For each round a numbering of the values of its challenge: it fixes how hash blocks are turned
into a challenge. -/
def Shape.NumChal : Shape → Type
  | [] => Unit
  | r :: s => Num r.Chal × Shape.NumChal s

/-- For each round a numbering of its oracle positions: it fixes the leaf of the Merkle tree that
holds a position. -/
def Shape.NumPos : (s : Shape) → s.IsPoint → Type
  | [], _ => Unit
  | r :: s, (pt, pts) => (r.Pos ≃ Fin (@Fintype.card r.Pos pt.finPos)) × Shape.NumPos s pts

end Iop
