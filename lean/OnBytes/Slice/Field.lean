-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Field.lean: the library's arithmetic on words (Fmt/FieldE.lean) is the arithmetic of
the field.

The format has two fields. This file is about its second (`Fmt.Fld.two`). The library's
Fmt/FieldE.lean keeps an element of the field with p = 2^64 - 2^32 + 1 elements in a 64-bit word,
and an element of its cubic extension (X^3 = 2) in a triple of words. It computes through natural
numbers: the words' values are added or multiplied and reduced modulo p. This is not the program's
arithmetic, which works on 64-bit words (OnBytes/Field/); OnBytes/Slice/ProgField.lean ties that one
to this one. The library's theory speaks of `Cb.Gl.F`, the integers modulo p, and of `Cb.Gl.E`, the
ring of triples over it with X^3 = 2, which is a field. This file reads a word as an element of F
and a triple as an element of E, and proves that each operation of Fmt/FieldE.lean goes to the
operation of the same name.

Main definitions: `toF`, `toE`, `ofF`, `ofE`.
Main theorems: `toF_add`, `toF_sub`, `toF_neg`, `toF_mul`, `toE_addE`, `toE_subE`, `toE_negE`,
`toE_mulE`, `toE_scaleE`; `toF_inj` and `toE_inj` (on words below p the reading is injective);
`toF_ofF` and `toE_ofE` (every element is read from some word).

The inverses and powers are in OnBytes/Slice/FieldInv.lean.
Not claimed. Nothing on the format's first field.
-/
import Fmt.FieldE
import Cb.Gl.GlField

set_option autoImplicit false

namespace OnBytes.Slice
open Code

/-- A word, read as an element of the base field. Words from p on are reduced. -/
def toF (a : UInt64) : Cb.Gl.F := (a.toNat : Cb.Gl.F)

/-- A triple of words, read as an element of the extension field. -/
def toE (a : Fmt.Ext3) : Cb.Gl.E := ⟨toF a.1, toF a.2.1, toF a.2.2⟩

/-- The word below p that is read as x. -/
def ofF (x : Cb.Gl.F) : UInt64 := UInt64.ofNat x.val

/-- The triple of words below p that is read as x. -/
def ofE (x : Cb.Gl.E) : Fmt.Ext3 := (ofF x.c0, ofF x.c1, ofF x.c2)

/-- The format's second prime is the library's. -/
theorem two_p : Fmt.Fld.two.p = Code.pGold := Code.pGold_eq.symm

/-- A natural number, reduced to a word, is read as its residue class. -/
theorem toF_red (n : ℕ) : toF (Fmt.Fld.two.red n) = (n : Cb.Gl.F) := by
  have h1 : n % Fmt.Fld.two.p < 2 ^ 64 :=
    Nat.lt_trans (Nat.mod_lt _ Fmt.Fld.two.p_pos) Fmt.Fld.two.p_lt
  unfold toF Fmt.Fld.red
  rw [UInt64.toNat_ofNat_of_lt' h1, two_p]
  exact ZMod.natCast_mod n Code.pGold

/-- p minus a residue is read as the negative. -/
theorem cast_p_sub (n : ℕ) :
    ((Fmt.Fld.two.p - n % Fmt.Fld.two.p : ℕ) : Cb.Gl.F) = -(n : Cb.Gl.F) := by
  rw [two_p, Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ Code.pGold_prime.pos)), ZMod.natCast_self,
    ZMod.natCast_mod, zero_sub]

theorem toF_add (a b : UInt64) : toF (Fmt.Fld.two.add a b) = toF a + toF b := by
  unfold Fmt.Fld.add
  rw [toF_red]
  exact Nat.cast_add _ _

theorem toF_neg (a : UInt64) : toF (Fmt.Fld.two.neg a) = -toF a := by
  unfold Fmt.Fld.neg
  rw [toF_red]
  exact cast_p_sub _

theorem toF_sub (a b : UInt64) : toF (Fmt.Fld.two.sub a b) = toF a - toF b := by
  unfold Fmt.Fld.sub
  rw [toF_red, Nat.cast_add, cast_p_sub, ← sub_eq_add_neg]
  rfl

theorem toF_mul (a b : UInt64) : toF (Fmt.Fld.two.mul a b) = toF a * toF b := by
  unfold Fmt.Fld.mul
  rw [toF_red]
  exact Nat.cast_mul _ _

/-- The constant c with X^3 = c is 2. -/
theorem toF_cW : toF Fmt.Fld.two.cW = 2 := by
  unfold Fmt.Fld.cW
  rw [toF_red]
  show ((2 : ℕ) : Cb.Gl.F) = 2
  exact Nat.cast_ofNat

theorem toF_zero : toF 0 = 0 := by
  show ((0 : ℕ) : Cb.Gl.F) = 0
  exact Nat.cast_zero

theorem toF_one : toF 1 = 1 := by
  show ((1 : ℕ) : Cb.Gl.F) = 1
  exact Nat.cast_one

/-- On words below p the reading is injective. -/
theorem toF_inj (a b : UInt64) (ha : Fmt.Fld.two.ok a = true) (hb : Fmt.Fld.two.ok b = true)
    (h : toF a = toF b) : a = b := by
  have ha' : a.toNat < Code.pGold := two_p ▸ of_decide_eq_true ha
  have hb' : b.toNat < Code.pGold := two_p ▸ of_decide_eq_true hb
  have h2 : a.toNat % Code.pGold = b.toNat % Code.pGold := (ZMod.natCast_eq_natCast_iff' _ _ _).1 h
  rw [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at h2
  exact UInt64.toNat_inj.1 h2

/-- Every element of the base field is read from its word. -/
theorem toF_ofF (x : Cb.Gl.F) : toF (ofF x) = x := by
  have h1 : x.val < 2 ^ 64 := Nat.lt_trans (ZMod.val_lt x) (two_p ▸ Fmt.Fld.two.p_lt)
  unfold toF ofF
  rw [UInt64.toNat_ofNat_of_lt' h1]
  exact ZMod.natCast_zmod_val x

/-- The word of an element is below p. -/
theorem ok_ofF (x : Cb.Gl.F) : Fmt.Fld.two.ok (ofF x) = true := by
  have h1 : x.val < 2 ^ 64 := Nat.lt_trans (ZMod.val_lt x) (two_p ▸ Fmt.Fld.two.p_lt)
  unfold Fmt.Fld.ok ofF
  rw [UInt64.toNat_ofNat_of_lt' h1, two_p]
  exact decide_eq_true (ZMod.val_lt x)

theorem toE_zeroE : toE Fmt.Fld.zeroE = 0 := by
  apply Cubic.ext <;> exact toF_zero

theorem toE_oneE : toE Fmt.Fld.oneE = 1 := by
  apply Cubic.ext
  · exact toF_one
  · exact toF_zero
  · exact toF_zero

/-- A word as an element of the extension field is the image of the base field's element. -/
theorem toE_ofF (a : UInt64) : toE (Fmt.Fld.ofF a) = algebraMap Cb.Gl.F Cb.Gl.E (toF a) := by
  apply Cubic.ext <;> simp [toE, Fmt.Fld.ofF, toF_zero, Algebra.algebraMap_eq_smul_one]

theorem toE_addE (a b : Fmt.Ext3) : toE (Fmt.Fld.two.addE a b) = toE a + toE b := by
  apply Cubic.ext <;> exact toF_add _ _

theorem toE_subE (a b : Fmt.Ext3) : toE (Fmt.Fld.two.subE a b) = toE a - toE b := by
  apply Cubic.ext <;> exact toF_sub _ _

theorem toE_negE (a : Fmt.Ext3) : toE (Fmt.Fld.two.negE a) = -toE a := by
  apply Cubic.ext <;> exact toF_neg _

theorem toE_mulE (a b : Fmt.Ext3) : toE (Fmt.Fld.two.mulE a b) = toE a * toE b := by
  apply Cubic.ext <;>
    simp only [toE, Fmt.Fld.mulE, toF_add, toF_mul, toF_cW, Cubic.mul_c0, Cubic.mul_c1,
      Cubic.mul_c2]

theorem toE_scaleE (s : UInt64) (a : Fmt.Ext3) :
    toE (Fmt.Fld.two.scaleE s a) = toF s • toE a := by
  apply Cubic.ext <;>
    simp only [toE, Fmt.Fld.scaleE, toF_mul, Cubic.smul_c0, Cubic.smul_c1, Cubic.smul_c2]

/-- On triples of words below p the reading is injective. -/
theorem toE_inj (a b : Fmt.Ext3) (ha : Fmt.Fld.two.okE a = true) (hb : Fmt.Fld.two.okE b = true)
    (h : toE a = toE b) : a = b := by
  simp only [Fmt.Fld.okE, Bool.and_eq_true] at ha hb
  have h0 : toF a.1 = toF b.1 := congrArg Cubic.c0 h
  have h1 : toF a.2.1 = toF b.2.1 := congrArg Cubic.c1 h
  have h2 : toF a.2.2 = toF b.2.2 := congrArg Cubic.c2 h
  exact Prod.ext (toF_inj _ _ ha.1.1 hb.1.1 h0)
    (Prod.ext (toF_inj _ _ ha.1.2 hb.1.2 h1) (toF_inj _ _ ha.2 hb.2 h2))

/-- Every element of the extension field is read from its triple. -/
theorem toE_ofE (x : Cb.Gl.E) : toE (ofE x) = x := by
  apply Cubic.ext <;> exact toF_ofF _

end OnBytes.Slice

#print axioms OnBytes.Slice.toE_mulE
#print axioms OnBytes.Slice.toE_inj
