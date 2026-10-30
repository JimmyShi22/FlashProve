-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/ErrCap.lean: the greatest list of errors whose every entry, as a share of its round's
challenges, is at most 1 / 2^k.

Why. A chain's blocks each carry a list of errors, and a theorem on the whole asks that all of them
are shares of at most one bound (`Err.Below`, Iop/InteractiveOracleProof.lean). If each block carries the cap, that
holds by the make. And whoever has proved a block's law at errors of its own that are below the
bound has it at the cap, since "the prover has lost" is monotone in the errors (`Doomed.mono_err`,
Iop/Rbr.lean).
  `Err.cap k s`: at each round of s the whole number (the number of the round's challenges) / 2^k.
  `Err.cap_below`: it is below (2^k)⁻¹. `Err.cap_below_inv`: the same bound written 2⁻¹ ^ k.
  `Err.le_cap_of_below` | `_inv`: every list below that bound is at most the cap, entry by entry.
What is counted. ALL of a round's challenges, as `Err.Below` counts them. Where a round's written
challenge carries bits of a proof of work, these bits are part of the challenge: the cap is taken
against the written challenges with them, and that only the challenges which pass the test of the
work can help a prover is a matter of the count that is held against the cap, not of the cap. So w
bits of work are credited as w of the k bits. The library has a second way of counting, with the
work outside the challenge (`Err.BelowG`, Iop/Grind.lean): the cap is not made for that one: held
against a bound in that form, at bits of work other than 0, it would count the work twice or not at
all.
Limits. Arithmetic on lists of numbers: no protocol occurs. A block that carries the cap has a law
only if somebody proves one at errors below the bound: the cap prices nothing by itself, and a
block's own count does not stand in the block. k is a letter: at k = 0 the cap is all challenges,
and every law holds at it for nothing. At a round with fewer than 2^k challenges the cap is 0: a
round without a draw gets 0, rightly; any other such round has a law at the cap only if no challenge
is bad (so a small example has none at a large k). No code is made for `Err.cap`: it is for
statements, not for a record that a program evaluates.
Terms: lean/GLOSSARY.md.

-/
import Iop.InteractiveOracleProof

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped ENNReal

namespace Iop

/-- At each round the whole number (the number of the round's challenges) / 2^k. -/
noncomputable def Err.cap (k : ℕ) : (s : Shape) → Err s
  | [] => ()
  | r :: s => (Fintype.card r.Chal / 2 ^ k, Err.cap k s)

theorem Err.cap_entry (k n : ℕ) :
    ((n / 2 ^ k : ℕ) : ℝ≥0∞) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ * (n : ℝ≥0∞) := by
  have h0 : ((2 : ℝ≥0∞) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : ((2 : ℝ≥0∞) ^ k) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h1 : ((n / 2 ^ k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k ≤ (n : ℝ≥0∞) := by
    have h2 : n / 2 ^ k * 2 ^ k ≤ n := Nat.div_mul_le_self n (2 ^ k)
    calc ((n / 2 ^ k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k
        = ((n / 2 ^ k * 2 ^ k : ℕ) : ℝ≥0∞) := by push_cast; ring
      _ ≤ (n : ℝ≥0∞) := by exact_mod_cast h2
  calc ((n / 2 ^ k : ℕ) : ℝ≥0∞)
      = ((n / 2 ^ k : ℕ) : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k * ((2 : ℝ≥0∞) ^ k)⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel h0 ht, mul_one]
    _ ≤ (n : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ k)⁻¹ := mul_le_mul_left h1 _
    _ = ((2 : ℝ≥0∞) ^ k)⁻¹ * (n : ℝ≥0∞) := mul_comm _ _

/-- The cap is below (2^k)⁻¹. -/
theorem Err.cap_below (k : ℕ) : ∀ s : Shape, Err.Below (Err.cap k s) ((2 : ℝ≥0∞) ^ k)⁻¹
  | [] => trivial
  | r :: s => ⟨Err.cap_entry k (Fintype.card r.Chal), Err.cap_below k s⟩

theorem Err.entry_le_cap (k n e : ℕ) (h : (e : ℝ≥0∞) ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ * (n : ℝ≥0∞)) :
    e ≤ n / 2 ^ k := by
  have h0 : ((2 : ℝ≥0∞) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have ht : ((2 : ℝ≥0∞) ^ k) ≠ ⊤ := ENNReal.pow_ne_top (by norm_num)
  have h1 : (e : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k ≤ (n : ℝ≥0∞) := by
    calc (e : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k
        ≤ ((2 : ℝ≥0∞) ^ k)⁻¹ * (n : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k := mul_le_mul_left h _
      _ = (n : ℝ≥0∞) * (((2 : ℝ≥0∞) ^ k)⁻¹ * (2 : ℝ≥0∞) ^ k) := by ring
      _ = (n : ℝ≥0∞) := by rw [ENNReal.inv_mul_cancel h0 ht, mul_one]
  have h2 : e * 2 ^ k ≤ n := by
    have h3 : ((e * 2 ^ k : ℕ) : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      have e4 : ((e * 2 ^ k : ℕ) : ℝ≥0∞) = (e : ℝ≥0∞) * (2 : ℝ≥0∞) ^ k := by push_cast; ring
      rw [e4]
      exact h1
    exact_mod_cast h3
  exact (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (pow_ne_zero _ (by norm_num)))).2 h2

/-- Every list below (2^k)⁻¹ is at most the cap. -/
theorem Err.le_cap_of_below (k : ℕ) :
    ∀ {s : Shape} (ε : Err s), Err.Below ε ((2 : ℝ≥0∞) ^ k)⁻¹ → Err.le ε (Err.cap k s)
  | [], _, _ => trivial
  | r :: _, (e, ε), h =>
    ⟨Err.entry_le_cap k (Fintype.card r.Chal) e h.1, Err.le_cap_of_below k ε h.2⟩

/-- The same two with the bound written 2⁻¹ ^ k. -/
theorem Err.cap_below_inv (k : ℕ) (s : Shape) : Err.Below (Err.cap k s) ((2 : ℝ≥0∞)⁻¹ ^ k) := by
  rw [← ENNReal.inv_pow]
  exact Err.cap_below k s

theorem Err.le_cap_of_below_inv (k : ℕ) {s : Shape} (ε : Err s)
    (h : Err.Below ε ((2 : ℝ≥0∞)⁻¹ ^ k)) : Err.le ε (Err.cap k s) := by
  rw [← ENNReal.inv_pow] at h
  exact Err.le_cap_of_below k ε h

end Iop

#print axioms Iop.Err.cap_below
#print axioms Iop.Err.le_cap_of_below
#print axioms Iop.Err.cap_below_inv
#print axioms Iop.Err.le_cap_of_below_inv
