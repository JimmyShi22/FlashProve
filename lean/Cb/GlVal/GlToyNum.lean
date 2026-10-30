-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyNum.lean: for toys, named lemmas say that small numbers are below p = 2^64 - 2^32 + 1
and stay different in the two fields. A toy is a small example instance.

Definitions and small theorems. No statement of a protocol.
This file is the analogue of Cb/Ld/LdToyNum.lean (the field K with 101 elements, namespace
`Cb.LdToy`) for the fields F (the integers modulo p) and E = F[x] / (x^3 - 2) of Cb/Gl/GlField.lean
(namespace `Cb.Gl`), under the same names; `natKF_ne` and `intKF_ne` are added, over F. Nothing here
enumerates a field.

Main names:
  `pK`: the characteristic p.
  `lt_pK`, `lt_pKz`: n < 2^6 ⇒ n < `pK`, for a natural number, for an integer.
  `natK_ne`, `intK_ne`: over E: m, n < 2^6, m ≠ n ⇒ (m : E) ≠ n; integers with |m|, |n| < 2^5.
    `natKF_ne`, `intKF_ne`: the same over F.
  `ne01`, `ne10`, `ne57`, `ne75`, `ne65`, `ne67`, `ne56`, `ne76`: 0 ≠ 1, 1 ≠ 0, 5 ≠ 7 and so on, in
    E.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyBase
import Cb.Ld.LdToyNum

set_option autoImplicit false

namespace Cb.Gl

/-- The characteristic. -/
abbrev pK : ℕ := p

theorem lt_pK {n : ℕ} (h : n < 2 ^ 6) : n < pK := small (lt_trans h (by norm_num))
theorem lt_pKz {n : ℤ} (h : n < 2 ^ 6) : n < (pK : ℤ) := by
  have h1 : (2 ^ 6 : ℕ) ≤ pK := (small (by norm_num : 2 ^ 6 < 2 ^ 32)).le
  have h2 : ((2 ^ 6 : ℕ) : ℤ) ≤ (pK : ℤ) := Int.ofNat_le.2 h1
  exact lt_of_lt_of_le h (by simpa using h2)

theorem natK_ne {m n : ℕ} (hm : m < 2 ^ 6) (hn : n < 2 ^ 6) (h : m ≠ n) : (m : E) ≠ (n : E) :=
  nat_cast_ne E pK (lt_pK hm) (lt_pK hn) h
theorem natKF_ne {m n : ℕ} (hm : m < 2 ^ 6) (hn : n < 2 ^ 6) (h : m ≠ n) : (m : F) ≠ (n : F) :=
  nat_cast_ne F pK (lt_pK hm) (lt_pK hn) h

theorem intK_ne {m n : ℤ} (hm : |m| < 2 ^ 5) (hn : |n| < 2 ^ 5) (h : m ≠ n) : (m : E) ≠ (n : E) :=
  int_cast_ne E pK (lt_pKz (lt_of_le_of_lt (abs_sub m n) (by linarith))) h
theorem intKF_ne {m n : ℤ} (hm : |m| < 2 ^ 5) (hn : |n| < 2 ^ 5) (h : m ≠ n) : (m : F) ≠ (n : F) :=
  int_cast_ne F pK (lt_pKz (lt_of_le_of_lt (abs_sub m n) (by linarith))) h

theorem ne01 : (0 : E) ≠ 1 := zero_ne_one
theorem ne10 : (1 : E) ≠ 0 := one_ne_zero
theorem ne57 : (5 : E) ≠ 7 := n57E
theorem ne75 : (7 : E) ≠ 5 := n57E.symm
theorem ne65 : (6 : E) ≠ 5 := n65E
theorem ne56 : (5 : E) ≠ 6 := n65E.symm
theorem ne67 : (6 : E) ≠ 7 := n67E
theorem ne76 : (7 : E) ≠ 6 := n67E.symm

end Cb.Gl
