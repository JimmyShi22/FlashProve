-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Small.lean: round-by-round errors, bounded from inequalities between numbers.

`Small D ε` (in the docstrings: ε is small): every count of the list ε, times D, is at most the
number of values of the verifier message; then, for D > 0, every error of the list, as a
probability, is at most 1/D (`below_of_small`, Blocks/SmallJoin.lean). `small_app`: two small lists
in a row are small. For one level of the recursive column test of Blocks/LevelDef.lean (`LevSpec`):
`LevSmall E D a`, three conditions on the level's numbers, and `LevSmall.small_theta`, `small_last`,
`small_next`, which derive the inequality of `Small` for one count at each of the level's rounds
`rTheta`, `rLast`, `rNext`. (Words of this library: lean/GLOSSARY.md.)
Notation: `LevelsSmall E D a rest`: `LevSmall E D` of `a` and of every member of `rest`.
These errors are counts: any list `ε : Err s` (Iop/Rbr.lean), or the one count in each of the three
lemmas on a level. That rounds are sound at these counts is no statement of this file.
-/
import Blocks.LevelDef
import Iop.InteractiveOracleProof
import Mathlib.Data.FinEnum

set_option linter.unusedSectionVars false

namespace Blocks
open Iop Prob
open scoped ENNReal

def Small (D : ℕ) : {s : Shape} → Err s → Prop
  | [], _ => True
  | r :: _, (e, ε) => e * D ≤ Fintype.card r.Chal ∧ Small D ε

theorem small_app (D : ℕ) :
    ∀ {s t : Shape} (a : Err s) (b : Err t), Small D a → Small D b → Small D (Err.app a b)
  | [], _, _, _, _, hb => hb
  | _ :: _, _, (_, a), b, ha, hb => ⟨ha.1, small_app D a b ha.2 hb⟩

theorem small_aux (a c D k : ℕ) (hk : 0 < k) (h : a * D ≤ c) : a * c ^ (k - 1) * D ≤ c ^ k :=
  calc a * c ^ (k - 1) * D = (a * D) * c ^ (k - 1) := by ring
    _ ≤ c * c ^ (k - 1) := Nat.mul_le_mul_right _ h
    _ = c ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]

/-! ## The levels -/

section Levels
variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- What makes the errors of one level small: rows > 0; 2 mca D ≤ |E|; 2 (n - e)^q D ≤ n^q (with 4 D
≤ |E| besides: h4 of `LevSmall.small_next`). -/
structure LevSmall (D : ℕ) (a : LevSpec F) : Prop where
  rows_pos : 0 < a.rows
  theta : 2 * a.code.mca * D ≤ Fintype.card E
  pos : 2 * (a.code.n - a.code.e) ^ a.q * D ≤ a.code.n ^ a.q

def LevelsSmall (D : ℕ) : LevSpec F → List (LevSpec F) → Prop
  | a, [] => LevSmall E D a
  | a, b :: rest => LevSmall E D a ∧ LevelsSmall D b rest

theorem LevSmall.small_theta {D : ℕ} {a : LevSpec F} (h : LevSmall E D a) :
    2 * a.code.mca * Fintype.card E ^ (a.rows - 1) * D ≤ Fintype.card (a.rTheta E).Chal := by
  have hc : Fintype.card (a.rTheta E).Chal = Fintype.card E ^ a.rows := by
    show Fintype.card (Fin a.rows → E) = _
    simp
  rw [hc]
  exact small_aux _ _ _ _ h.rows_pos h.theta

theorem LevSmall.small_last {D : ℕ} {a : LevSpec F} (h : LevSmall E D a) :
    (a.code.n - a.code.e) ^ a.q * D ≤ Fintype.card (a.rLast E).Chal := by
  have hc : Fintype.card (a.rLast E).Chal = a.code.n ^ a.q := by
    show Fintype.card (Fin a.q → Fin a.code.n) = _
    simp
  rw [hc]
  exact le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by norm_num))) h.pos

theorem LevSmall.small_next {D : ℕ} {a : LevSpec F} (h : LevSmall E D a)
    (h4 : 4 * D ≤ Fintype.card E) (b : LevSpec F) :
    ((a.code.n - a.code.e) ^ a.q * Fintype.card E ^ (a.q + 2) +
          2 * a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) * D ≤
      Fintype.card (a.rNext E b).Chal := by
  have hc : Fintype.card (a.rNext E b).Chal = a.code.n ^ a.q * Fintype.card E ^ (a.q + 2) := by
    show Fintype.card ((Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E)) = _
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    ring
  rw [hc]
  have e2 : Fintype.card E ^ (a.q + 2) = Fintype.card E * Fintype.card E ^ (a.q + 1) :=
    pow_succ' _ _
  have a1 : 2 * (a.code.n - a.code.e) ^ a.q * D * Fintype.card E ^ (a.q + 2) ≤
      a.code.n ^ a.q * Fintype.card E ^ (a.q + 2) :=
    Nat.mul_le_mul_right _ h.pos
  have a2 : 4 * D * (a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) ≤
      Fintype.card E * (a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) :=
    Nat.mul_le_mul_right _ h4
  rw [e2] at a1 ⊢
  generalize Fintype.card E ^ (a.q + 1) = P at a1 a2 ⊢
  generalize (a.code.n - a.code.e) ^ a.q = A at a1 ⊢
  generalize a.code.n ^ a.q = N at a1 a2 ⊢
  generalize Fintype.card E = e at a1 a2 ⊢
  nlinarith [a1, a2]

end Levels

end Blocks
