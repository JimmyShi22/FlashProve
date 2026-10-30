-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoNatVal.lean.
Natural numbers as elements of the byte-level verifier's field, under a reading.

States, for every reading in a commutative ring:
  ofNat_val: the element that stands for the natural number n reads as n.
  scaleNat_val: an element times a natural number reads as the number times the element's reading.
By: the field's prime is 0 in every ring that has a reading (Fo.prime_zero).

-/
import OnBytes.Tie.Pv.Lookup.Port.FoTwins

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model

variable {K : Type} [CommRing K] (ρ : Reading K)

include ρ in
private theorem nat_word (n : ℕ) : ((fOfNat n).toNat : K) = (n : K) := by
  unfold fOfNat
  have hp : pW.toNat = 18446744069414584321 := by decide
  have hlt : n % pW.toNat < 2 ^ 64 := lt_trans (Nat.mod_lt _ (by rw [hp]; norm_num)) (by
    rw [hp]; norm_num)
  rw [toNat_word _ hlt, hp]
  conv_rhs => rw [← Nat.div_add_mod n 18446744069414584321]
  rw [Nat.cast_add, Nat.cast_mul, prime_zero ρ, zero_mul, zero_add]

/-- A natural number as an element, read. -/
theorem ofNat_val (n : ℕ) : ρ.val (ofNat n) = (n : K) := by
  unfold ofNat
  rw [ofF_val, nat_word ρ]

/-- An element times a natural number, read. -/
theorem scaleNat_val (x : E) (v : ℕ) : ρ.val (scaleNat x v) = (v : K) * ρ.val x := by
  unfold scaleNat
  rw [scale_val, nat_word ρ]

end Fo
