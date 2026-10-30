-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/PowEq.lean: power and inverse on machine words are those of Fmt/FieldE.lean.

Main theorems: `powF_eq`, `invF_eq`. They hold for all words and all exponents. Nothing is claimed
here on whether these are the operations of a field.
-/
import OnBytes.Field.MulEq

namespace OnBytes

/-- The power of Fmt/ with the exponent 0 is 1 modulo m. -/
theorem powMod_zero (b m : Nat) : Fmt.powMod b 0 m = 1 % m :=
  (Fmt.powMod.eq_def b 0 m).trans (dif_pos rfl)

/-- One step of the power of Fmt/, for an exponent that is not 0. -/
theorem powMod_pos (b e m : Nat) (h : e ≠ 0) : Fmt.powMod b e m =
    if e % 2 = 1 then b * Fmt.powMod (b * b % m) (e / 2) m % m
    else Fmt.powMod (b * b % m) (e / 2) m :=
  (Fmt.powMod.eq_def b e m).trans (dif_neg h)

/-- 1 modulo p is 1. -/
theorem one_mod_p : 1 % 18446744069414584321 = 1 := rfl

/-- Two ways to put a factor into a product modulo m. -/
theorem mul_mod_swap (r x y m : Nat) : r * x % m * y % m = r * (x * y % m) % m := by
  rw [Nat.mul_mod (r * x % m) y m, Nat.mod_mod, ← Nat.mul_mod, Nat.mul_mod r (x * y % m) m,
    Nat.mod_mod, ← Nat.mul_mod, Nat.mul_assoc]

/-- As a number, what the loop of `powF` returns is r times the power of Fmt/ (`Fmt.powMod x e p`),
modulo p, if the loop's bound is at least e and r is below p. -/
theorem toNat_powLoopF : ∀ (k : Nat) (x : UInt64) (e : Nat) (r : UInt64), e ≤ k →
    r.toNat < 18446744069414584321 → (powLoopF k x e r).toNat =
      r.toNat * Fmt.powMod x.toNat e 18446744069414584321 % 18446744069414584321
  | 0, x, e, r, he, hr => by
      have e0 : e = 0 := Nat.le_zero.1 he
      subst e0
      rw [powMod_zero, one_mod_p, Nat.mul_one, Nat.mod_eq_of_lt hr]
      rfl
  | k + 1, x, e, r, he, hr => by
      by_cases e0 : e = 0
      · subst e0
        rw [powMod_zero, one_mod_p, Nat.mul_one, Nat.mod_eq_of_lt hr]
        rfl
      · have hk : e / 2 ≤ k := by omega
        have step : powLoopF (k + 1) x e r =
            powLoopF k (mulF x x) (e / 2) (if e % 2 = 1 then mulF r x else r) := by
          show (if e = 0 then r else _) = _
          rw [if_neg e0]
        rw [step, powMod_pos _ _ _ e0]
        by_cases odd : e % 2 = 1
        · have hr' : (mulF r x).toNat < 18446744069414584321 := by
            rw [toNat_mulF]
            exact Nat.mod_lt _ (by decide)
          rw [if_pos odd, if_pos odd, toNat_powLoopF k _ _ _ hk hr', toNat_mulF, toNat_mulF,
            mul_mod_swap]
        · rw [if_neg odd, if_neg odd, toNat_powLoopF k _ _ _ hk hr, toNat_mulF]

/-- The power on words is the power of Fmt/FieldE.lean. -/
theorem powF_eq (a : UInt64) (e : Nat) : powF a e = Fmt.Fld.two.pow a e := by
  unfold powF Fmt.Fld.pow
  apply eq_red
  rw [toNat_powLoopF e a e 1 (Nat.le_refl e) (by decide), p_two]
  have h1 : (1 : UInt64).toNat = 1 := rfl
  rw [h1, Nat.one_mul]

/-- The inverse on words is the inverse of Fmt/FieldE.lean. -/
theorem invF_eq (a : UInt64) : invF a = Fmt.Fld.two.inv a := by
  unfold invF Fmt.Fld.inv
  exact powF_eq a _

end OnBytes

#print axioms OnBytes.powF_eq
#print axioms OnBytes.invF_eq
