-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/WordEq.lean: sum, difference and negative on machine words are those of
Fmt/FieldE.lean.

Main theorems: `okF_eq`, `addF_eq`, `subF_eq`, `negF_eq`. Each holds for all words, also for words
that are not below p. Tools for the files that import this one: `toNat_normF`, `eq_red`.

Whether these are the operations of a field: OnBytes/Slice/ProgField.lean, not here.
-/
import Fmt.FieldEFast
import OnBytes.Field.Word

namespace OnBytes

/-- As a number, the word `pW` is p = 2^64 - 2^32 + 1. -/
theorem toNat_pW : pW.toNat = 18446744069414584321 := rfl

/-- As a number, the word `epsW` is 2^32 - 1. -/
theorem toNat_epsW : epsW.toNat = 4294967295 := rfl

/-- The prime of the second field of Fmt/ is p. -/
theorem p_two : Fmt.Fld.two.p = 18446744069414584321 := rfl

/-- A word that, as a number, is n modulo p is the element that Fmt/ makes of n. -/
theorem eq_red {x : UInt64} {n : Nat} (h : x.toNat = n % 18446744069414584321) :
    x = Fmt.Fld.two.red n := by
  apply UInt64.toNat_inj.1
  rw [Fmt.Fld.toNat_red, p_two, h]

/-- As a number, `normF a` is a modulo p. -/
theorem toNat_normF (a : UInt64) : (normF a).toNat = a.toNat % 18446744069414584321 := by
  have ha := a.toNat_lt
  unfold normF
  by_cases h : a < pW
  · rw [if_pos h]
    rw [UInt64.lt_iff_toNat_lt, toNat_pW] at h
    omega
  · rw [if_neg h, UInt64.toNat_sub, toNat_pW]
    rw [UInt64.lt_iff_toNat_lt, toNat_pW] at h
    omega

/-- `okF` is the test of Fmt/. -/
theorem okF_eq (a : UInt64) : okF a = Fmt.Fld.two.ok a := by
  unfold okF Fmt.Fld.ok
  rw [p_two]
  apply decide_eq_decide.2
  rw [UInt64.lt_iff_toNat_lt, toNat_pW]

/-- As a number, `addF a b` is a + b modulo p. -/
theorem toNat_addF (a b : UInt64) :
    (addF a b).toNat = (a.toNat + b.toNat) % 18446744069414584321 := by
  have hx := toNat_normF a
  have hy := toNat_normF b
  unfold addF
  by_cases h : normF a < pW - normF b
  · simp only [if_pos h]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, toNat_pW] at h
    rw [UInt64.toNat_add]
    omega
  · simp only [if_neg h]
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, toNat_pW] at h
    rw [UInt64.toNat_sub, UInt64.toNat_sub, toNat_pW]
    omega

/-- As a number, `subF a b` is a - b modulo p, spelled without a negative number. -/
theorem toNat_subF (a b : UInt64) : (subF a b).toNat =
    (a.toNat + (18446744069414584321 - b.toNat % 18446744069414584321)) % 18446744069414584321 := by
  have hx := toNat_normF a
  have hy := toNat_normF b
  unfold subF
  by_cases h : normF a < normF b
  · simp only [if_pos h]
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.toNat_add, UInt64.toNat_sub, toNat_pW]
    omega
  · simp only [if_neg h]
    rw [UInt64.lt_iff_toNat_lt] at h
    rw [UInt64.toNat_sub]
    omega

/-- As a number, `negF a` is -a modulo p, spelled without a negative number. -/
theorem toNat_negF (a : UInt64) : (negF a).toNat =
    (18446744069414584321 - a.toNat % 18446744069414584321) % 18446744069414584321 := by
  have hx := toNat_normF a
  unfold negF
  by_cases h : normF a = 0
  · simp only [if_pos h]
    rw [h] at hx
    have h0 : (0 : UInt64).toNat = 0 := rfl
    omega
  · simp only [if_neg h]
    have h0 : (normF a).toNat ≠ 0 := fun e => h (UInt64.toNat_inj.1 e)
    rw [UInt64.toNat_sub, toNat_pW]
    omega

/-- The sum on words is the sum of Fmt/FieldE.lean. -/
theorem addF_eq (a b : UInt64) : addF a b = Fmt.Fld.two.add a b := eq_red (toNat_addF a b)

/-- The difference on words is the difference of Fmt/FieldE.lean. -/
theorem subF_eq (a b : UInt64) : subF a b = Fmt.Fld.two.sub a b := eq_red (toNat_subF a b)

/-- The negative on words is the negative of Fmt/FieldE.lean. -/
theorem negF_eq (a : UInt64) : negF a = Fmt.Fld.two.neg a := eq_red (toNat_negF a)

end OnBytes

#print axioms OnBytes.okF_eq
#print axioms OnBytes.addF_eq
#print axioms OnBytes.subF_eq
#print axioms OnBytes.negF_eq
