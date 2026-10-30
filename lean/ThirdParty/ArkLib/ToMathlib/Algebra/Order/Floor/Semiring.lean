/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/ToMathlib/Algebra/Order/Floor/Semiring.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* All 2 declarations of the file are kept. ArkLib's comment at the top of the file is unchanged.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.Algebra.Order.Floor.Semiring

/-!
# The rounding `⌈z⌉₊ - 1`

In a floor semiring, `⌈z⌉₊ - 1` (natural subtraction) is the largest natural number strictly
below `z` when `z > 0`. This file records the two facts about it that parameter recipes use: it is
strictly below `z` for `0 < z`, and it is at least `1` for `1 < z`.

## Main statements

* `Nat.cast_ceil_sub_one_lt`: `((⌈z⌉₊ - 1 : ℕ) : R) < z` for `0 < z`.
* `Nat.one_le_ceil_sub_one`: `1 ≤ ⌈z⌉₊ - 1` for `1 < z`.
-/

namespace Nat

variable {R : Type*} [Semiring R] [LinearOrder R] [FloorSemiring R]

/-- For `1 < z`, the natural number `⌈z⌉₊ - 1` is at least `1`.

The hypothesis `1 < z` is needed: at `z = 1` the value is `0`. -/
theorem one_le_ceil_sub_one {z : R} (hz : 1 < z) : 1 ≤ ⌈z⌉₊ - 1 := by
  have h : 1 + 1 ≤ ⌈z⌉₊ := Nat.add_one_le_ceil_iff.2 (by exact_mod_cast hz)
  omega

variable [IsStrictOrderedRing R]

/-- For `0 < z`, the natural number `⌈z⌉₊ - 1` is strictly below `z`.

The hypothesis `0 < z` is needed: at `z = 0` both sides are `0`. -/
theorem cast_ceil_sub_one_lt {z : R} (hz : 0 < z) : ((⌈z⌉₊ - 1 : ℕ) : R) < z := by
  have h1 : 1 ≤ ⌈z⌉₊ := Nat.one_le_ceil_iff.2 hz
  have h := Nat.ceil_lt_add_one hz.le
  rw [← Nat.sub_add_cancel h1, Nat.cast_add, Nat.cast_one] at h
  exact lt_of_add_lt_add_right h

end Nat
