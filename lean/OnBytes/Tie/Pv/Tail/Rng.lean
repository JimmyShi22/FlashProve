-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Tail/Rng.lean: what it means that a typed round of the library is the round RNG of
a plan, and a bound 2 ^ -t for that round as a count of challenges.

A round of the library (Iop.Round, Iop/Shape.lean) holds types; a plan's entry (Fmt.Entry,
Fmt/Plan.lean) is a name and eleven numbers. In the round RNG the prover sends nothing and the
verifier draws a matrix with entries in {-1, 0, 1}. The format makes each entry from two drawn
bits (Fmt.tritAt, Fmt/Rules6.lean): 0 if the first bit is 0, else 1 or -1 by the second. That is
the rule of Prob.Coef.val (Prob/Window.lean), by `tritAt_eq`. So an entry is 0 with probability
1/2 and 1 or -1 with probability 1/4 each. A challenge of the library is uniform in a finite set,
so the set that has this law is: a coefficient, that is two bits, for each entry.
Run/DrawPage.lean reads a draw of n matrix entries in the same way (Run.DVal).
Definitions, statements and proofs.

Main names:
  `RngIs r e`: the round r sends nothing, has no oracle position, and draws, up to a bijection,
    a coefficient for each of the e.trits matrix entries; the entry e counts no byte, root,
    answer, field element or position.
  `RngIs.card_chal`, `RngIs.trits_eq`, `RngIs.not_of_trits_ne`: the round fixes the number of
    matrix entries: an entry with another number is refuted.
  `rngIs_draw`: the definition is met, by the library's round that draws a value.
  `tritAt_eq`: the format's entry number j of a word is the value of the coefficient made of
    the word's bits 2 j and 2 j + 1.
  `rngCount c t`: one part in 2 ^ t of 4 ^ (c * t) challenges. `rngCount_le`: it is at most
    that part. `rngCount_mul`: with c at least 1 it is that part exactly.

Limits: RngIs counts. "Up to a bijection" fixes the size of the challenge set, not which
coefficient belongs to which entry of the matrix. The oracle part itself is not asked to be
trivial, only to have no position. Of the entry, the name, the count, the work, the range of
positions and the number of batched rows are not read. It speaks of a round before proof of work
is added to a shape. Nothing here says that a bound is true of any protocol.
-/
import Fmt.Plan
import Fmt.Rules6
import Prob.Window
import Ior.Draw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail

open Iop

/-- The round r is the round RNG of the entry e. -/
def RngIs (r : Round) (e : Fmt.Entry) : Prop :=
  Nonempty (r.Plain ≃ Unit) ∧ Nonempty (r.Chal ≃ (Fin e.trits → Prob.Coef)) ∧ IsEmpty r.Pos ∧
    e.msg = 0 ∧ e.roots = 0 ∧ e.answers = 0 ∧ e.drawE = 0 ∧ e.drawNZ = 0 ∧ e.poss = 0

/-- There are 4 ^ n lists of n coefficients. -/
theorem card_coefs (n : ℕ) : Nat.card (Fin n → Prob.Coef) = 4 ^ n := by
  rw [Nat.card_fun, Nat.card_fin, Nat.card_eq_fintype_card]
  rfl

/-- The size of the challenge set. -/
theorem RngIs.card_chal {r : Round} {e : Fmt.Entry} (h : RngIs r e) :
    Nat.card r.Chal = 4 ^ e.trits := by
  obtain ⟨f⟩ := h.2.1
  rw [Nat.card_congr f, card_coefs]

/-- The round fixes the number of matrix entries. -/
theorem RngIs.trits_eq {r : Round} {e e' : Fmt.Entry} (h : RngIs r e) (h' : RngIs r e') :
    e.trits = e'.trits :=
  Nat.pow_right_injective (by omega : 2 ≤ 4) (h.card_chal.symm.trans h'.card_chal)

/-- An entry with another number of matrix entries is refuted. -/
theorem RngIs.not_of_trits_ne {r : Round} {e e' : Fmt.Entry} (h : RngIs r e)
    (hne : e'.trits ≠ e.trits) : ¬ RngIs r e' := fun h' => hne (h'.trits_eq h)

/-- The definition is met: the library's round that draws n coefficients. -/
theorem rngIs_draw (n : ℕ) (name : String) (w : ℕ) :
    RngIs (IOR.drawRound (Fin n → Prob.Coef)) { name := name, work := w, trits := n } :=
  ⟨⟨Equiv.refl _⟩, ⟨Equiv.refl _⟩, inferInstanceAs (IsEmpty Empty), rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The format's entry number j of a word is the value of the coefficient made of two of the
word's bits. -/
theorem tritAt_eq (w : UInt64) (j : ℕ) :
    Fmt.tritAt w j = Prob.Coef.val (w.toNat.testBit (2 * j), w.toNat.testBit (2 * j + 1)) := by
  unfold Fmt.tritAt
  cases w.toNat.testBit (2 * j) <;> cases w.toNat.testBit (2 * j + 1) <;> rfl

/-- One part in 2 ^ t of 4 ^ (c * t) challenges. -/
def rngCount (c t : ℕ) : ℕ := 4 ^ (c * t) / 2 ^ t

/-- It is at most that part. -/
theorem rngCount_le (c t : ℕ) : rngCount c t * 2 ^ t ≤ 4 ^ (c * t) :=
  Nat.div_mul_le_self _ _

/-- With a column or more the division is exact. -/
theorem rngCount_mul (c t : ℕ) (hc : 1 ≤ c) : rngCount c t * 2 ^ t = 4 ^ (c * t) := by
  have h4 : (4 : ℕ) ^ (c * t) = 2 ^ (2 * (c * t) - t) * 2 ^ t := by
    rw [← pow_add, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
    congr 1
    have : t ≤ c * t := Nat.le_mul_of_pos_left t hc
    omega
  unfold rngCount
  rw [h4, Nat.mul_div_cancel _ (Nat.pow_pos (by omega))]

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.RngIs.trits_eq
#print axioms OnBytes.Tie.Pv.Tail.RngIs.not_of_trits_ne
#print axioms OnBytes.Tie.Pv.Tail.rngIs_draw
#print axioms OnBytes.Tie.Pv.Tail.tritAt_eq
#print axioms OnBytes.Tie.Pv.Tail.rngCount_le
#print axioms OnBytes.Tie.Pv.Tail.rngCount_mul
