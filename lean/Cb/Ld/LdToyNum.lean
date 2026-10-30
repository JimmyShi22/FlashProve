-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdToyNum.lean: for toys: numbers in the field with 101 elements, by name.

In standard terms: small lemmas of arithmetic: two different small numbers stay different in a ring
of characteristic p, and so in the field `K` = ZMod 101 (Cb/Ld/LdRelToy.lean), over which some of
this folder's small example instances (toys) are written.

Definitions and small theorems. No statement of a protocol.

Why: a toy over ZMod 101 can settle "5 ≠ 7" or "28 < 101" by "decide". Over a large field the same
line makes Lean enumerate the field. If a toy file is to be carried over to the fields of
Cb/Gl/GlField.lean by a change of names, it cites the lemmas below; Cb/GlVal/GlToyNum.lean has the
same names over these fields (namespace Cb.Gl).

Main names:
In the namespace of the toys (`Cb.LdToy`):
  `pK`: the characteristic (here 101); a toy file that is to be carried over writes `pK` for the
    numeral.
  `natK_ne`, `intK_ne`: the two generic lemmas (`nat_cast_ne`, `int_cast_ne`) at K, with bounds that
    hold here and in Cb/GlVal/GlToyNum.lean: m, n < 2^6; |m|, |n| < 2^5.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdRelToy
import Mathlib.Algebra.CharP.Basic

set_option autoImplicit false

namespace Cb

theorem nat_cast_ne (R : Type) [AddGroupWithOne R] (p : ℕ) [CharP R p] {m n : ℕ} (hm : m < p)
    (hn : n < p) (h : m ≠ n) : (m : R) ≠ (n : R) := fun e =>
  h (by
    have h1 := (CharP.natCast_eq_natCast R p).1 e
    rwa [Nat.ModEq, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h1)

theorem int_cast_ne (R : Type) [AddGroupWithOne R] (p : ℕ) [CharP R p] {m n : ℤ}
    (hd : |m - n| < (p : ℤ)) (h : m ≠ n) : (m : R) ≠ (n : R) := fun e =>
  h (by
    have h1 : (p : ℤ) ∣ m - n := (Int.modEq_iff_dvd.1 ((CharP.intCast_eq_intCast R p).1 e).symm)
    exact sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd h1 hd))

namespace LdToy

/-- the characteristic -/
abbrev pK : ℕ := 101

instance : CharP K pK := ZMod.charP 101

theorem lt_pK {n : ℕ} (h : n < 2 ^ 6) : n < pK := lt_trans h (by norm_num)
theorem lt_pKz {n : ℤ} (h : n < 2 ^ 6) : n < (pK : ℤ) := lt_trans h (by norm_num)

theorem natK_ne {m n : ℕ} (hm : m < 2 ^ 6) (hn : n < 2 ^ 6) (h : m ≠ n) : (m : K) ≠ (n : K) :=
  nat_cast_ne K pK (lt_pK hm) (lt_pK hn) h

theorem intK_ne {m n : ℤ} (hm : |m| < 2 ^ 5) (hn : |n| < 2 ^ 5) (h : m ≠ n) : (m : K) ≠ (n : K) :=
  int_cast_ne K pK (lt_pKz (lt_of_le_of_lt (abs_sub m n) (by linarith))) h

theorem ne01 : (0 : K) ≠ 1 := zero_ne_one
theorem ne10 : (1 : K) ≠ 0 := one_ne_zero
theorem ne57 : (5 : K) ≠ 7 := by
  simpa using natK_ne (m := 5) (n := 7) (by norm_num) (by norm_num) (by norm_num)
theorem ne75 : (7 : K) ≠ 5 := ne57.symm
theorem ne65 : (6 : K) ≠ 5 := by
  simpa using natK_ne (m := 6) (n := 5) (by norm_num) (by norm_num) (by norm_num)
theorem ne56 : (5 : K) ≠ 6 := ne65.symm
theorem ne67 : (6 : K) ≠ 7 := by
  simpa using natK_ne (m := 6) (n := 7) (by norm_num) (by norm_num) (by norm_num)
theorem ne76 : (7 : K) ≠ 6 := ne67.symm

end LdToy
end Cb
