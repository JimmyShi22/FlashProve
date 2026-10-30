-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Joined/Worst.lean: the greatest error of a list of round errors, as a probability: the least
number that the compiler's bound can take for εs. Definitions and proofs; arithmetic only.

A second form of the compiler's verifier side, beside the library's own, which is unchanged. It is
made for a key file's and a proof file's three hash chains, joined by seals; that it writes what is
hashed as the prover's files have it is not shown in this folder.

Why. The compiler takes the errors of a protocol through "every error, as a probability, is at most
εs" (`Err.Below`, Iop/InteractiveOracleProof.lean), with εs a free number. A statement whose error is to be computed
from a description needs that number as a function of the list of errors.

Main names:
  `worst ε`: the greatest of the numbers e / (number of values of the round's verifier message);
  `below_worst`: `Err.Below ε (worst ε)`; `worst_le`: it is the least such number;
  `worst_app`: of two lists in a row it is the greater of the two;
  `worst3 N ε₁ ε₂ ε₃`: for three chains of rounds of which the second stands in shared rounds and
    pays N times, N the number of slots; `bound n εs lam`: n εs + 2 (n + 1)² / 2^lam.

Limits: no number is evaluated here.

Terms: lean/GLOSSARY.md.

-/
import Iop.Compose

noncomputable section

namespace Compile.Joined
open Iop Prob
open scoped ENNReal

/-- the greatest error of the list, as a probability; 0 for no round -/
def worst : {s : Shape} → Err s → ℝ≥0∞
  | [], _ => 0
  | r :: _, (e, ε) => max ((e : ℝ≥0∞) / (Fintype.card r.Chal : ℝ≥0∞)) (worst ε)

/-- Every error of the list, as a probability, is at most `worst`. -/
theorem below_worst : ∀ {s : Shape} (ε : Err s), Err.Below ε (worst ε)
  | [], _ => trivial
  | r :: _, (_, ε) =>
    ⟨(ENNReal.div_le_iff (card_ne_zero' r.Chal) (card_ne_top' r.Chal)).1 (le_max_left _ _),
      Err.Below.mono_bound (le_max_right _ _) (below_worst ε)⟩

/-- `worst` is the least bound on all errors of the list. -/
theorem worst_le : ∀ {s : Shape} {ε : Err s} {c : ℝ≥0∞}, Err.Below ε c → worst ε ≤ c
  | [], _, _, _ => zero_le _
  | r :: _, (_, _), _, h =>
    max_le ((ENNReal.div_le_iff (card_ne_zero' r.Chal) (card_ne_top' r.Chal)).2 h.1) (worst_le h.2)

/-- Two lists in a row: the greater of the two. -/
theorem worst_app : ∀ {s t : Shape} (a : Err s) (b : Err t),
    worst (Err.app a b) = max (worst a) (worst b)
  | [], _, _, b => (max_eq_right (zero_le _)).symm
  | r :: _, _, (e, a), b => by
    show max _ (worst (Err.app a b)) = max (max _ (worst a)) (worst b)
    rw [worst_app a b, max_assoc]

/-- The number for three chains of rounds in a row, of which the second pays N times. -/
def worst3 (N : ℕ) {s₁ s₂ s₃ : Shape} (ε₁ : Err s₁) (ε₂ : Err s₂) (ε₃ : Err s₃) : ℝ≥0∞ :=
  max (worst ε₁) (max ((N : ℝ≥0∞) * worst ε₂) (worst ε₃))

theorem below_worst3_fst (N : ℕ) {s₁ s₂ s₃ : Shape} (ε₁ : Err s₁) (ε₂ : Err s₂) (ε₃ : Err s₃) :
    Err.Below ε₁ (worst3 N ε₁ ε₂ ε₃) :=
  Err.Below.mono_bound (le_max_left _ _) (below_worst ε₁)

theorem below_worst3_thd (N : ℕ) {s₁ s₂ s₃ : Shape} (ε₁ : Err s₁) (ε₂ : Err s₂) (ε₃ : Err s₃) :
    Err.Below ε₃ (worst3 N ε₁ ε₂ ε₃) :=
  Err.Below.mono_bound (le_trans (le_max_right _ _) (le_max_right _ _)) (below_worst ε₃)

theorem le_worst3_snd (N : ℕ) {s₁ s₂ s₃ : Shape} (ε₁ : Err s₁) (ε₂ : Err s₂) (ε₃ : Err s₃) :
    (N : ℝ≥0∞) * worst ε₂ ≤ worst3 N ε₁ ε₂ ε₃ :=
  le_trans (le_max_left _ _) (le_max_right _ _)

/-- the bound of the compiler's soundness theorem for an algorithm with at most n queries -/
def bound (n : ℕ) (εs : ℝ≥0∞) (lam : ℕ) : ℝ≥0∞ :=
  (n : ℝ≥0∞) * εs + 2 * ((n + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam

end Compile.Joined
