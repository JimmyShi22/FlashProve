-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/ZeroE.lean: in the program's arithmetic on words, a product with the element 0 of E is
the element 0, at EVERY other factor, and so is every power of 0 with an exponent above 0.

An element of E is three words (OnBytes/Base.lean); the type admits words that are not below the
prime. The laws here are equations of words, not of residues, and ask nothing of the other factor's
words.

Main theorems: `mulF_zero_left`, `mulF_zero_right`, `addF_zero_zero`, `mulE_zero_left`,
`mulE_zero_right`, `powLoopE_zeroE`, `powE_zeroE`.

Limits: equations on the program's own functions `mulF`, `addF`, `mulE` and `powE` where a factor,
both summands or the base is 0. Nothing on a product of two elements that are not 0; nothing on
residues modulo the prime; nothing on 0 to the power 0. `powLoopE_zeroE` asks an exponent that is
not 0 and at least as many steps as the exponent. For proofs only.


Terms: lean/GLOSSARY.md.
-/
import OnBytes.Field.ExtEq

set_option autoImplicit false

namespace OnBytes

theorem mulF_zero_left (y : UInt64) : mulF 0 y = 0 :=
  UInt64.toNat_inj.1 (by rw [toNat_mulF, UInt64.toNat_zero, Nat.zero_mul, Nat.zero_mod])

theorem mulF_zero_right (y : UInt64) : mulF y 0 = 0 :=
  UInt64.toNat_inj.1 (by rw [toNat_mulF, UInt64.toNat_zero, Nat.mul_zero, Nat.zero_mod])

theorem addF_zero_zero : addF 0 0 = 0 :=
  UInt64.toNat_inj.1 (by rw [toNat_addF, UInt64.toNat_zero, Nat.add_zero, Nat.zero_mod])

/-- **0 times x is 0**, at every x. -/
theorem mulE_zero_left (x : E) : mulE zeroE x = zeroE := by
  unfold mulE mulE0 mulE1 mulE2 mulW0 mulW1 mulW2 twiceF zeroE
  simp only [E.c0_mk3, E.c1_mk3, E.c2_mk3, mulF_zero_left, addF_zero_zero]

/-- **x times 0 is 0**, at every x. -/
theorem mulE_zero_right (x : E) : mulE x zeroE = zeroE := by
  unfold mulE mulE0 mulE1 mulE2 mulW0 mulW1 mulW2 twiceF zeroE
  simp only [E.c0_mk3, E.c1_mk3, E.c2_mk3, mulF_zero_right, addF_zero_zero]

/-- The loop of `powE` at the base 0: with an exponent above 0, and steps enough, the result is 0,
whatever it started from. -/
theorem powLoopE_zeroE : ∀ (k e : Nat) (r : E), e ≠ 0 → e ≤ k → powLoopE k zeroE e r = zeroE
  | 0, e, _, h0, hk => absurd (Nat.le_zero.1 hk) h0
  | k + 1, e, r, h0, hk => by
    rw [powLoopE_step k zeroE e r h0, mulE_zero_left]
    by_cases h2 : e / 2 = 0
    · have h1 : e % 2 = 1 := by omega
      rw [h2, powLoopE_zero, if_pos h1, mulE_zero_right]
    · exact powLoopE_zeroE k (e / 2) _ h2 (by omega)

/-- **0 to a power above 0 is 0.** -/
theorem powE_zeroE (c : Nat) : powE zeroE (c + 1) = zeroE :=
  powLoopE_zeroE (c + 1) (c + 1) oneE (Nat.succ_ne_zero c) (Nat.le_refl _)

end OnBytes
