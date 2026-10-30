-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Leaves.lean: sizes of the Merkle trees over the oracles of a list of rounds.

Numbers of leaves 2^depth and largest depth, as the generic wire record makes them
(Iop/WireOf.lean): depth = ⌈log₂ (number of positions of the prover message)⌉. (Words of this
library: lean/GLOSSARY.md.)
-/
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option linter.unusedSectionVars false

namespace Blocks
open Iop

/-- the depth of the tree over one prover message -/
def depthR {r : Round} (pt : r.IsPoint) : ℕ := Nat.clog 2 (@Fintype.card r.Pos pt.finPos)

/-- leaves of all trees of one execution -/
def leaves : (s : Shape) → s.IsPoint → ℕ
  | [], _ => 0
  | _ :: s, (pt, pts) => 2 ^ depthR pt + leaves s pts

/-- the largest depth -/
def depths : (s : Shape) → s.IsPoint → ℕ
  | [], _ => 0
  | _ :: s, (pt, pts) => max (depthR pt) (depths s pts)

theorem leaves_app :
    ∀ {s t : Shape} (a : s.IsPoint) (b : t.IsPoint),
      leaves (s ++ t) (pointApp a b) = leaves s a + leaves t b
  | [], _, _, _ => (Nat.zero_add _).symm
  | _ :: _, _, (pt, a), b => by
      show 2 ^ depthR pt + leaves _ (pointApp a b) = 2 ^ depthR pt + leaves _ a + leaves _ b
      rw [leaves_app a b, Nat.add_assoc]

theorem depths_app :
    ∀ {s t : Shape} (a : s.IsPoint) (b : t.IsPoint),
      depths (s ++ t) (pointApp a b) = max (depths s a) (depths t b)
  | [], _, _, _ => (Nat.zero_max _).symm
  | _ :: _, _, (pt, a), b => by
      show max (depthR pt) (depths _ (pointApp a b)) =
        max (max (depthR pt) (depths _ a)) (depths _ b)
      rw [depths_app a b, max_assoc]

theorem leaves_rep (r : Round) (h : r.IsPoint) : ∀ (n : ℕ) {t : Shape} (b : t.IsPoint),
    leaves (List.replicate n r ++ t) (pointRep r h n b) = n * 2 ^ depthR h + leaves t b
  | 0, _, _ => by simp [pointRep]
  | n + 1, _, b => by
      show 2 ^ depthR h + leaves _ (pointRep r h n b) = (n + 1) * 2 ^ depthR h + leaves _ b
      rw [leaves_rep r h n b]; ring

theorem depths_rep_le (r : Round) (h : r.IsPoint) : ∀ (n : ℕ) {t : Shape} (b : t.IsPoint),
    depths (List.replicate n r ++ t) (pointRep r h n b) ≤ max (depthR h) (depths t b)
  | 0, _, _ => le_max_right _ _
  | n + 1, _, b => max_le (le_max_left _ _) (depths_rep_le r h n b)

theorem depth_plain (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (d : Plain) :
    depthR (plainPoint Plain Chal d) = 0 := by
  show Nat.clog 2 (Fintype.card Empty) = 0
  simp

theorem depth_words (A : Type) [Fintype A] [DecidableEq A] (n : A → ℕ) (Sy : A → Type)
    (Plain Chal : Type) [Fintype Chal] [Nonempty Chal] (dSy : ∀ a, Sy a) (dPlain : Plain) :
    depthR (wordsPoint A n Sy Plain Chal dSy dPlain) = Nat.clog 2 (∑ a, n a) := by
  show Nat.clog 2 (Fintype.card (Σ a, Fin (n a))) = _
  simp

theorem depths_rep_zero (r : Round) (h : r.IsPoint) (h0 : depthR h = 0) :
    ∀ (n : ℕ) {t : Shape} (b : t.IsPoint),
      depths (List.replicate n r ++ t) (pointRep r h n b) = depths t b
  | 0, _, _ => rfl
  | n + 1, _, b => by
      show max (depthR h) (depths _ (pointRep r h n b)) = _
      rw [h0, depths_rep_zero r h h0 n b, Nat.zero_max]

end Blocks
