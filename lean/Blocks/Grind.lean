-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Grind.lean: proof-of-work bits ("grinding") at the levels (the recursive column test of
Blocks/LevelDef.lean): which rounds get how many bits.

The form. Iop/GBits.lean: a number b of proof-of-work bits for each round. A round with b bits has
its verifier message sampled together with b further bits that must all be 0: the number of values
of the verifier message grows by the factor 2^b, the count of bad values does not.
  `pos_mul`, `pos_mul1`: an inequality on positions at D' gives the one at 2^b * D' with the factor
  2^b.
  `levels2G b a rest`: 0 at the rounds of the sumcheck and at θ; b at rNext and rLast
  (Blocks/Level2Def.lean). `levels2G_zero`: at b = 0 it is `GBits.zero`.
  `Lev2SmallG`, `Levels2SmallG`, `Lev2SmallG.of_pos`, `Lev2SmallG.small_theta`,
  `Lev2SmallG.small_last`, `Lev2SmallG.small_next`: what makes the errors of the levels small.

Notation: `D`, `D'`, `b`: natural numbers; `g`: a `GBits s` (Iop/GBits.lean): for each round a
number of proof-of-work bits. That rounds are sound at the counts of these lemmas is no statement of
this file.
Limits. Nothing at concrete parameters. Nothing on a compiled scheme: that a factor 2^-b on a
round's error may be counted at all is a statement about work in the compiled scheme (each attempt
with a nonce is a query), not about the interactive protocol, whose rounds keep their errors; it
belongs to the compiler (Compile/).
Rounds without proof-of-work bits gain nothing: the largest error over all rounds is what a bound
depends on.
-/
import Iop.GBits
import Blocks.Batch.KitHon
import Blocks.ErrSup
import Blocks.Level2Def
import Blocks.PfrHVZK_rs
import Blocks.Small
import Iop.Deco
import Iop.Late
import Mathlib.Data.FinEnum

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Blocks
open Iop

/-! ## 1. Helper lemmas -/

/-- An inequality at D' gives the one at 2^b * D' with the factor 2^b. -/
theorem pos_mul {A N D' : ℕ} (b c : ℕ) (h : A * (c * D') ≤ N) :
    A * (c * (2 ^ b * D')) ≤ 2 ^ b * N :=
  calc A * (c * (2 ^ b * D')) = 2 ^ b * (A * (c * D')) := by ring
    _ ≤ 2 ^ b * N := Nat.mul_le_mul_left _ h

theorem pos_mul1 {A N D' : ℕ} (b : ℕ) (h : A * D' ≤ N) : A * (2 ^ b * D') ≤ 2 ^ b * N :=
  calc A * (2 ^ b * D') = 2 ^ b * (A * D') := by ring
    _ ≤ 2 ^ b * N := Nat.mul_le_mul_left _ h

/-! ## 2. The levels -/

section Levels
variable {F : Type} [Field F] (E : Type) [Field E] [Fintype E] [DecidableEq E] [Algebra F E]

/-- The proof-of-work bits of the levels: b at the rounds that sample positions. -/
def levels2G (b : ℕ) : (a : Lev2 F) → (rest : List (Lev2 F)) → GBits (levels2Shape E a rest)
  | a, [] => GBits.rep (LinSh.rSC E) 0 a.mu (t := [a.rTheta E, a.rLast E]) (0, (b, ()))
  | a, c :: rest =>
    GBits.rep (LinSh.rSC E) 0 a.mu
      (t := a.rTheta E :: a.rNext E c :: levels2Shape E c rest) (0, (b, levels2G b c rest))

theorem levels2G_zero : ∀ (a : Lev2 F) (rest : List (Lev2 F)), levels2G E 0 a rest = GBits.zero _
  | a, [] => GBits.rep_zero (LinSh.rSC E) a.mu [a.rTheta E, a.rLast E]
  | a, c :: rest => by
    show GBits.rep (LinSh.rSC E) 0 a.mu (t := a.rTheta E :: a.rNext E c :: levels2Shape E c rest)
        (0, (0, levels2G E 0 c rest)) = _
    rw [levels2G_zero c rest]
    exact GBits.rep_zero (LinSh.rSC E) a.mu (a.rTheta E :: a.rNext E c :: levels2Shape E c rest)

/-- What makes the errors of one level small: as `LevSmall` (Blocks/Small.lean), with
the factor 2^b at the positions. -/
structure Lev2SmallG (D b : ℕ) (a : Lev2 F) : Prop where
  rows_pos : 0 < a.rows
  theta : 2 * a.code.mca * D ≤ Fintype.card E
  pos : 2 * (a.code.n - a.code.e) ^ a.q * D ≤ 2 ^ b * a.code.n ^ a.q

def Levels2SmallG (D b : ℕ) : Lev2 F → List (Lev2 F) → Prop
  | a, [] => Lev2SmallG E D b a
  | a, c :: rest => Lev2SmallG E D b a ∧ Levels2SmallG D b c rest

/-- the algebraic clauses at 2^b * D', the positions at D' -/
theorem Lev2SmallG.of_pos {D' b : ℕ} {a : Lev2 F} (hr : 0 < a.rows)
    (ht : 2 * a.code.mca * (2 ^ b * D') ≤ Fintype.card E)
    (hp : (a.code.n - a.code.e) ^ a.q * (2 * D') ≤ a.code.n ^ a.q) :
    Lev2SmallG E (2 ^ b * D') b a :=
  ⟨hr, ht, by
    have := pos_mul (A := (a.code.n - a.code.e) ^ a.q) b 2 hp
    calc
      2 * (a.code.n - a.code.e) ^ a.q * (2 ^ b * D') =
          (a.code.n - a.code.e) ^ a.q * (2 * (2 ^ b * D')) := by ring
      _ ≤ _ := this⟩

theorem Lev2SmallG.small_theta {D b : ℕ} {a : Lev2 F} (h : Lev2SmallG E D b a) :
    2 * a.code.mca * Fintype.card E ^ (a.rows - 1) * D ≤ Fintype.card (a.rTheta E).Chal := by
  have hc : Fintype.card (a.rTheta E).Chal = Fintype.card E ^ a.rows := by
    show Fintype.card (Fin a.rows → E) = _
    simp
  rw [hc]
  exact small_aux _ _ _ _ h.rows_pos h.theta

theorem Lev2SmallG.small_last {D b : ℕ} {a : Lev2 F} (h : Lev2SmallG E D b a) :
    (a.code.n - a.code.e) ^ a.q * D ≤ 2 ^ b * Fintype.card (a.rLast E).Chal := by
  have hc : Fintype.card (a.rLast E).Chal = a.code.n ^ a.q := by
    show Fintype.card (Fin a.q → Fin a.code.n) = _
    simp
  rw [hc]
  exact le_trans (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (by norm_num))) h.pos

theorem Lev2SmallG.small_next
    {D b : ℕ} {a : Lev2 F} (h : Lev2SmallG E D b a) (h4 : 4 * D ≤ Fintype.card E) (c : Lev2 F) :
    ((a.code.n - a.code.e) ^ a.q * Fintype.card E ^ (a.q + 2) +
          2 * a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) * D ≤
      2 ^ b * Fintype.card (a.rNext E c).Chal := by
  have hc : Fintype.card (a.rNext E c).Chal = a.code.n ^ a.q * Fintype.card E ^ (a.q + 2) := by
    show Fintype.card ((Fin a.q → Fin a.code.n) × E × E × (Fin a.q → E)) = _
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    ring
  rw [hc]
  have e2 : Fintype.card E ^ (a.q + 2) = Fintype.card E * Fintype.card E ^ (a.q + 1) :=
    pow_succ' _ _
  have a1 : 2 * (a.code.n - a.code.e) ^ a.q * D * Fintype.card E ^ (a.q + 2) ≤
      2 ^ b * a.code.n ^ a.q * Fintype.card E ^ (a.q + 2) :=
    Nat.mul_le_mul_right _ h.pos
  have a2 : 4 * D * (a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) ≤
      Fintype.card E * (a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) :=
    Nat.mul_le_mul_right _ h4
  have a3 : Fintype.card E * (a.code.n ^ a.q * Fintype.card E ^ (a.q + 1)) ≤
      2 ^ b * (Fintype.card E * (a.code.n ^ a.q * Fintype.card E ^ (a.q + 1))) :=
    Nat.le_mul_of_pos_left _ (by positivity)
  rw [e2] at a1 ⊢
  generalize Fintype.card E ^ (a.q + 1) = P at a1 a2 a3 ⊢
  generalize (a.code.n - a.code.e) ^ a.q = A at a1 ⊢
  generalize a.code.n ^ a.q = N at a1 a2 a3 ⊢
  generalize Fintype.card E = e at a1 a2 a3 ⊢
  generalize 2 ^ b = B at a1 a3 ⊢
  nlinarith [a1, a2, a3]

end Levels

end Blocks
