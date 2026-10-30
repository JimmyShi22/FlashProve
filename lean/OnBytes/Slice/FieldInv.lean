-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FieldInv.lean: powers and inverses on machine words are those of the field.

OnBytes/Slice/Field.lean reads a word as an element of `Cb.Gl.F`, the integers modulo
p = 2^64 - 2^32 + 1, and a triple of words as an element of `Cb.Gl.E`, the cubic extension with
X^3 = 2. It proves that sums, differences and products go to the field's own. This file adds the
power and the two inverses of Fmt/FieldE.lean. It then gathers the extension's laws for 0, 1, sum,
difference, product and negative in one statement: the reading respects the record of operations
of Fmt/M1PscOps.lean. That record holds no inverse and no product by an element of the base field.

How the inverses are computed in Fmt/FieldE.lean. In the base field the inverse of a is the power
a^(p - 2), found by repeated squaring. In the extension it is the triple of cofactors of a, divided
by the norm of a. Both give 0 at 0, as the inverse of a field does in Mathlib.

Main definition: `opsK`, the operations of any field as a record.
Main theorems: `powMod_eq` (repeated squaring computes b^e modulo m), `toF_pow`, `toF_inv`,
`toE_invE`, `toE_hom`. They hold for all words, also for words from p on.

Not claimed. Nothing on the other field of the format. Nothing on running time.
-/
import OnBytes.Slice.Field
import Fmt.FieldEFast
import Fmt.M1PscOps

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## Powers -/

/-- Repeated squaring computes the power modulo m. This holds for every m, also for 0 and 1. -/
theorem powMod_eq (b e m : ℕ) : Fmt.powMod b e m = b ^ e % m := by
  induction e using Nat.strong_induction_on generalizing b with
  | _ e ih =>
    by_cases h0 : e = 0
    · subst h0
      rw [pow_zero]
      exact (Fmt.powMod.eq_def b 0 m).trans (dif_pos rfl)
    · have step : Fmt.powMod b e m =
          if e % 2 = 1 then b * Fmt.powMod (b * b % m) (e / 2) m % m
          else Fmt.powMod (b * b % m) (e / 2) m :=
        (Fmt.powMod.eq_def b e m).trans (dif_neg h0)
      have half_lt : e / 2 < e := Nat.div_lt_self (Nat.pos_of_ne_zero h0) (by decide)
      have square : (b * b % m) ^ (e / 2) % m = b ^ (2 * (e / 2)) % m := by
        rw [← Nat.pow_mod, pow_mul, pow_two]
      rw [step, ih (e / 2) half_lt, square]
      by_cases odd : e % 2 = 1
      · have he : 2 * (e / 2) + 1 = e := by omega
        rw [if_pos odd, Nat.mul_mod_mod, ← pow_succ', he]
      · have he : 2 * (e / 2) = e := by omega
        rw [if_neg odd, he]

/-- The power on words is read as the power in the base field. -/
theorem toF_pow (a : UInt64) (e : ℕ) : toF (Fmt.Fld.two.pow a e) = toF a ^ e := by
  unfold Fmt.Fld.pow
  rw [toF_red, powMod_eq, two_p, ZMod.natCast_mod]
  exact Nat.cast_pow _ _

/-! ## The inverse in the base field -/

/-- In the base field the power with exponent p - 2 is the inverse, and 0 at 0. -/
theorem pow_p_sub_two (x : Cb.Gl.F) : x ^ (Code.pGold - 2) = x⁻¹ := by
  have three_le : 3 ≤ Code.pGold := by
    rw [Code.pGold_eq]
    decide
  by_cases hx : x = 0
  · have hne : Code.pGold - 2 ≠ 0 := by omega
    rw [hx, inv_zero]
    exact zero_pow hne
  · have fermat : x ^ (Code.pGold - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx
    have split : Code.pGold - 1 = Code.pGold - 2 + 1 := by omega
    rw [split, pow_succ] at fermat
    exact eq_inv_of_mul_eq_one_left fermat

/-- The inverse on words is read as the inverse in the base field. -/
theorem toF_inv (a : UInt64) : toF (Fmt.Fld.two.inv a) = (toF a)⁻¹ := by
  unfold Fmt.Fld.inv
  rw [toF_pow, two_p]
  exact pow_p_sub_two (toF a)

/-! ## The inverse in the extension field -/

/-- The three cofactors on words are read as the library's cofactors. -/
theorem toE_adjE (a : Fmt.Ext3) : toE (Fmt.Fld.two.adjE a) = Code.Cubic.adj (toE a) := by
  apply Code.Cubic.ext <;>
    simp only [toE, Fmt.Fld.adjE, Code.Cubic.adj, toF_sub, toF_mul, toF_cW, pow_two]

/-- The norm on words is read as the library's norm. -/
theorem toF_normE (a : Fmt.Ext3) : toF (Fmt.Fld.two.normE a) = Code.Cubic.nrm (toE a) := by
  have h0 : toF (Fmt.Fld.two.adjE a).1 = (Code.Cubic.adj (toE a)).c0 :=
    congrArg Code.Cubic.c0 (toE_adjE a)
  have h1 : toF (Fmt.Fld.two.adjE a).2.1 = (Code.Cubic.adj (toE a)).c1 :=
    congrArg Code.Cubic.c1 (toE_adjE a)
  have h2 : toF (Fmt.Fld.two.adjE a).2.2 = (Code.Cubic.adj (toE a)).c2 :=
    congrArg Code.Cubic.c2 (toE_adjE a)
  calc toF (Fmt.Fld.two.normE a)
      = toF a.1 * toF (Fmt.Fld.two.adjE a).1 + 2 * (toF a.2.2 * toF (Fmt.Fld.two.adjE a).2.1
          + toF a.2.1 * toF (Fmt.Fld.two.adjE a).2.2) := by
        unfold Fmt.Fld.normE
        simp only [toF_add, toF_mul, toF_cW]
    _ = toF a.1 * (Code.Cubic.adj (toE a)).c0 + 2 * (toF a.2.1 * (Code.Cubic.adj (toE a)).c2
          + toF a.2.2 * (Code.Cubic.adj (toE a)).c1) := by
        rw [h0, h1, h2, add_comm (toF a.2.2 * (Code.Cubic.adj (toE a)).c1)]
    _ = Code.Cubic.nrm (toE a) := rfl

/-- The inverse on triples of words is read as the inverse in the extension field. -/
theorem toE_invE (a : Fmt.Ext3) : toE (Fmt.Fld.two.invE a) = (toE a)⁻¹ := by
  unfold Fmt.Fld.invE
  rw [toE_scaleE, toF_inv, toF_normE, toE_adjE, Code.Cubic.inv_eq, Algebra.smul_def, mul_comm]

/-! ## The record of operations -/

/-- The operations of a field, in the record of Fmt/M1PscOps.lean. That record has two products,
because the format has a plain one and a faster one; a field has one, which fills both
places. -/
def opsK (K : Type) [Field K] : Fmt.M1.FOps K :=
  ⟨0, 1, (· + ·), (· - ·), (· * ·), (· * ·), (- ·)⟩

/-- Reading a triple of words as an element of the extension field respects every operation of
the record. -/
theorem toE_hom : Fmt.M1.FOps.Hom (Fmt.M1.opsOf .two) (opsK Cb.Gl.E) toE where
  zero := toE_zeroE
  one := toE_oneE
  add := toE_addE
  sub := toE_subE
  mul := toE_mulE
  mulF := fun x y => (congrArg toE (Fmt.mulEF_eq .two x y)).trans (toE_mulE x y)
  neg := toE_negE

end OnBytes.Slice

#print axioms OnBytes.Slice.powMod_eq
#print axioms OnBytes.Slice.toF_pow
#print axioms OnBytes.Slice.toF_inv
#print axioms OnBytes.Slice.toE_invE
#print axioms OnBytes.Slice.toE_hom
