-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/KeySumRead.lean: FROM THE PROGRAM's WORDS TO A READING: two small lemmas for whoever fills the letter same of the key file's sentences (Johnson/Desc/Key/KeyWords.lean: KRead.same; KeyMeaning23.lean: SameLaws) by
«ρ a = ρ b», ρ a reading of a machine element as an element of a field (or of any commutative semiring K).
  sumE_read          ρ (sumE n f) = Σ_{i < n} ρ (f i), where ρ sends zeroE to 0 and addE to +
  sameLaws_of_read   «ρ a = ρ b» meets SameLaws, where ρ sends addE to + and mulE to ·: SO SameLaws HAS A MEMBER BESIDE Eq WHEREVER SUCH A ρ IS
What is not claimed. That any ρ has these three laws AT EVERY WORD (at words at or above the prime that is what is owed). Nothing on soundness.

-/
import Johnson.Desc.Key.KeyMeaning23
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes

theorem sumE_read {K : Type} [AddCommMonoid K] (ρ : E → K) (h0 : ρ zeroE = 0) (hadd : ∀ a b, ρ (addE a b) = ρ a + ρ b) (n : Nat) (f : Nat → E) :
    ρ (sumE n f) = ∑ i ∈ Finset.range n, ρ (f i) := by
  induction n with
  | zero =>
    simp only [sumE, List.range_zero, List.foldl_nil, Finset.range_zero, Finset.sum_empty]
    exact h0
  | succ n ih => rw [sumE_succ, hadd, ih, Finset.sum_range_succ]

theorem sameLaws_of_read {K : Type} [Add K] [Mul K] (ρ : E → K) (hadd : ∀ a b, ρ (addE a b) = ρ a + ρ b) (hmul : ∀ a b, ρ (mulE a b) = ρ a * ρ b) :
    SameLaws fun a b => ρ a = ρ b :=
  ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k, fun h k => by rw [hadd, hadd, h, k], fun h k => by rw [hmul, hmul, h, k]⟩

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.sumE_read
#print axioms VerifiableInference.Desc.Key.sameLaws_of_read
