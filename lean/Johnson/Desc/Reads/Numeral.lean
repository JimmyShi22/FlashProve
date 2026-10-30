-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Numeral.lean: every reading takes the programs' numerals to the numbers of K.

All of this file is a tool: it holds for all readings into commutative rings, and names no
description of the protocol.

Why. The tie of the uses to the text, clause (T) of Reads/Stated.lean, compares coefficients behind
a reading. A kind's text writes its coefficients as numerals (256 ^ l, the policy's C). The
relation's clause has them as numbers of K. A reading (`Reading`, OnBytes/Model/HideLaws.lean) is
asked to keep 0, 1, sums, differences and products. Here the numerals follow from these, so that
they need not be asked apart.

What is here.
  `toNat_fOfNat`, `fOfNat_succ`, `ofNat_succ`: the programs' numeral of n + 1 is their sum of the
    numeral of n and 1.
  `reading_ofNat`: a reading takes the programs' numeral of n to n.
  `ofNat_prime`, `reading_prime`: the numeral of the programs' prime p = 2 ^ 64 - 2 ^ 32 + 1 is
    their 0, so p is 0 in K.
  `sq_ne_one`: where 1 ≠ 0 in K, 256 ^ 2 is not 1 in K, because p = 65535 * 281479271677952 + 1.

Three closed equations on words are found by the kernel's own evaluation.

Of OnBytes/Model/ this file names `Reading`, and the numerals `ofNat` and `fOfNat`
(OnBytes/Model/Frame.lean). It uses the law of the words' sum in OnBytes/Field/WordEq.lean.

Limits. It does not say that a reading is one-to-one. It says nothing on multiples and negatives.
Nothing on soundness.


-/
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes (E addE addF oneE zeroE)
open OnBytes.Model (Reading ofNat fOfNat)

/-- As a number, the word of the numeral n is n modulo p. -/
theorem toNat_fOfNat (n : ℕ) : (fOfNat n).toNat = n % 18446744069414584321 := by
  show (Fmt.Fld.two.red n).toNat = _
  rw [Fmt.Fld.toNat_red, OnBytes.p_two]

/-- On words: the numeral of n, plus 1, is the numeral of n + 1. -/
theorem fOfNat_succ (n : ℕ) : addF (fOfNat n) 1 = fOfNat (n + 1) := by
  have e : fOfNat (n + 1) = Fmt.Fld.two.red (n + 1) := rfl
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [e]
  refine OnBytes.eq_red ?_
  rw [OnBytes.toNat_addF, toNat_fOfNat, h1]
  omega

/-- The numeral of n + 1 is the programs' sum of the numeral of n and 1. -/
theorem ofNat_succ (n : ℕ) : ofNat (n + 1) = addE (ofNat n) oneE := by
  have e : addE (ofNat n) oneE = E.mk3 (addF (fOfNat n) 1) (addF 0 0) (addF 0 0) := rfl
  have h0 : addF 0 0 = 0 := by decide +kernel
  rw [e, fOfNat_succ, h0]
  rfl

variable {K : Type} [CommRing K]

/-- **A reading takes the programs' numeral of n to n.** -/
theorem reading_ofNat (ρ : Reading K) : ∀ n : ℕ, ρ.val (ofNat n) = (n : K)
  | 0 => by
    have e : ofNat 0 = zeroE := by decide +kernel
    rw [e, ρ.zero, Nat.cast_zero]
  | n + 1 => by rw [ofNat_succ, ρ.add, reading_ofNat ρ n, ρ.one, Nat.cast_succ]

/-- The programs' numeral of the prime p = 2 ^ 64 - 2 ^ 32 + 1 is their 0. -/
theorem ofNat_prime : ofNat 18446744069414584321 = zeroE := by decide +kernel

/-- Where there is a reading, p is 0 in K. -/
theorem reading_prime (ρ : Reading K) : ((18446744069414584321 : ℕ) : K) = 0 := by
  rw [← reading_ofNat ρ, ofNat_prime, ρ.zero]

/-- Where there is a reading and 1 ≠ 0 in K, 256 ^ 2 is not 1 in K. -/
theorem sq_ne_one (ρ : Reading K) (h1 : (1 : K) ≠ 0) : (256 : K) ^ 2 ≠ 1 := by
  intro h
  have hp := reading_prime ρ
  push_cast at hp
  exact h1 (by linear_combination hp - 281479271677952 * h)

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.toNat_fOfNat
#print axioms VerifiableInference.Reads.fOfNat_succ
#print axioms VerifiableInference.Reads.ofNat_succ
#print axioms VerifiableInference.Reads.reading_ofNat
#print axioms VerifiableInference.Reads.ofNat_prime
#print axioms VerifiableInference.Reads.reading_prime
#print axioms VerifiableInference.Reads.sq_ne_one
