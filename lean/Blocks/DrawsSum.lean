-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/DrawsSum.lean: lemmas for counting the hash blocks that samplers read (Iop/Draw.lean:
`Shape.Draws.totB`, `Shape.Draws.maxB`). (θ, χ0, χ1, χ': Blocks/LevelDef.lean.)

With t = bE.b blocks for an element of E and at most one block for a position (which holds as soon
as ⌈log₂ n⌉ + sl < lam: `posK_le_one`):
  `levelsTot`: the levels (the recursive column test of Blocks/LevelDef.lean): for each level mu · t
  (sumcheck), rows · t (θ), and q positions; at a level that is not the last also χ0, χ1 and q times
  χ': 2 t + q t.
The numbers count blocks as `Shape.Draws.totB` does: blocks only, without the one more for each
round that a step to one hash function needs (the chaining value).
  `maxB_le_totB`: no round reads more blocks than all rounds together: so a bound on the sum also
  bounds the largest round.
Limits: `levelsTot` is a formula only. This file does not bound the blocks of the levels.
-/
import Blocks.Draws
import Blocks.ChalSum
import Blocks.SizesFr

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Iop

theorem Shape.Draws.maxB_le_totB {lam : ℕ} :
    ∀ (s : Shape) (d : s.Draws lam), Shape.Draws.maxB s d ≤ Shape.Draws.totB s d
  | [], _ => le_rfl
  | _ :: s, (_, ds) =>
    max_le (Nat.le_add_right _ _) (le_trans (Shape.Draws.maxB_le_totB s ds) (Nat.le_add_left _ _))

theorem Shape.Draws.totB_app {lam : ℕ} :
    ∀ {s t : Shape} (a : s.Draws lam) (b : t.Draws lam),
      Shape.Draws.totB (s ++ t) (Shape.Draws.app a b) = Shape.Draws.totB s a + Shape.Draws.totB t b
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (x, as), b => by
    show x.b + Shape.Draws.totB _ (Shape.Draws.app as b) = x.b + Shape.Draws.totB _ as + _
    rw [Shape.Draws.totB_app as b, Nat.add_assoc]

theorem Shape.Draws.maxB_app {lam : ℕ} :
    ∀ {s t : Shape} (a : s.Draws lam) (b : t.Draws lam),
      Shape.Draws.maxB (s ++ t) (Shape.Draws.app a b) =
        max (Shape.Draws.maxB s a) (Shape.Draws.maxB t b)
  | [], _, _, _ => (Nat.zero_max _).symm
  | _ :: _, _, (x, as), b => by
    show max x.b (Shape.Draws.maxB _ (Shape.Draws.app as b)) =
      max (max x.b (Shape.Draws.maxB _ as)) _
    rw [Shape.Draws.maxB_app as b, max_assoc]

theorem Shape.Draws.totB_rep {lam : ℕ} (r : Round) (h : BS lam r.Chal) :
    ∀ (n : ℕ) {t : Shape} (d : t.Draws lam),
      Shape.Draws.totB (List.replicate n r ++ t) (Shape.Draws.rep r h n d) =
        n * h.b + Shape.Draws.totB t d
  | 0, _, _ => by rw [Nat.zero_mul, Nat.zero_add]; rfl
  | n + 1, _, d => by
    show h.b + Shape.Draws.totB _ (Shape.Draws.rep r h n d) = _
    rw [Shape.Draws.totB_rep r h n d, Nat.add_mul, Nat.one_mul]
    omega

namespace BS
variable {lam : ℕ}

theorem piE_b {ι : Type} [FinEnum ι] [Fintype ι] {C : ι → Type} (s : ∀ i, BS lam (C i)) :
    (piE s).b = ∑ i, (s i).b :=
  Equiv.sum_comp (FinEnum.equiv (α := ι)).symm fun i => (s i).b

theorem fnE_b {ι C : Type} [FinEnum ι] [Fintype ι] (s : BS lam C) :
    (fnE (ι := ι) s).b = Fintype.card ι * s.b := by
  show FinEnum.card ι * s.b = _
  rw [FinEnum.card_eq_fintypeCard]

theorem posK_le_one {lam sl n : ℕ} (h : Nat.clog 2 n + sl < lam) : posK lam sl n ≤ 1 := by
  unfold posK
  split_ifs
  · exact Nat.zero_le _
  · rw [Nat.div_eq_of_lt h]

end BS
end Iop

namespace Blocks
open Iop

variable {lam : ℕ}

/-! ## The levels -/

section Levels
variable {F : Type} [Field F] {E : Type} [Field E] [Fintype E] [DecidableEq E] [Algebra F E]
  (bE : BS lam E) (sl : ℕ)

def levelsTot (lam sl t : ℕ) : LevSpec F → List (LevSpec F) → ℕ
  | a, [] => a.mu * t + (a.rows * t + (a.q * BS.posK lam sl a.code.n + 0))
  | a, b :: rest =>
    a.mu * t +
      (a.rows * t +
        ((a.q * BS.posK lam sl a.code.n + (t + (t + a.q * t))) + levelsTot lam sl t b rest))

theorem vecE_b (n : ℕ) : (DrawOf.bs bE sl : BS lam (Fin n → E)).b = n * bE.b := rfl

theorem vecPos_b (q n : ℕ) [Nonempty (Fin n)] :
    (DrawOf.bs bE sl : BS lam (Fin q → Fin n)).b = q * BS.posK lam sl n := rfl

end Levels

end Blocks
