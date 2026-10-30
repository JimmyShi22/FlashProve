-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ProgField.lean: the program's arithmetic on machine words, read in the field.

The program computes in the base field and in its cubic extension with the functions of
OnBytes/Field/Word.lean and OnBytes/Field/Ext.lean. The files OnBytes/Field/WordEq.lean, MulEq.lean,
PowEq.lean and ExtEq.lean prove that each of them returns the same words as the function of
Fmt/FieldE.lean, and OnBytes/Slice/Field.lean and FieldInv.lean read those in the fields
`Cb.Gl.F` and `Cb.Gl.E`. This file puts the two steps together: each function of the program goes
to the operation of the field.

How the program's values are read. A word is read by `toF`. An element of the program's type `E`
is read by `readE`, which goes through the triple of words that Fmt/ uses. `readV v i` is entry i
of an array of such elements and `readL l i` entry i of a list; both are 0 beyond the end. The
other files on the program use `readE` and the laws below, so that they do not depend on how `E`
is built. Three laws of OnBytes/Slice/ProgCodes.lean tie these readings to those of Fmt/'s triples.

The file also says what a test of the program on words means in the field. If two elements of the
program are equal, they are read as one element of the field; if all three words are 0, the element
is 0. These two need no hypothesis. The other direction holds for words below p, the prime of the
base field.

Main definitions: `readE`, `readV`, `readL`, `readP` (a list as a point).
Main theorems: `toF_addF`, `toF_subF`, `toF_negF`, `toF_mulF`, `toF_powF`, `toF_invF`;
`readE_add`, `readE_sub`, `readE_neg`, `readE_scale`, `readE_mul`, `readE_inv`, `readE_maddE`,
`readE_maddS`, `readE_pow`; `readE_ofTriple`, `readE_mk3`; `readE_of_beq`, `readE_of_isZeroE`,
`isZeroE_iff`, `beq_iff_readE`.

Not claimed. Nothing on a block of the program. Nothing on running time.
-/
import OnBytes.Field.ExtEq
import OnBytes.Slice.FieldInv

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The base field -/

/-- The program's sum of words is the field's. -/
theorem toF_addF (a b : F) : toF (addF a b) = toF a + toF b := by
  rw [addF_eq, toF_add]

/-- The program's difference of words is the field's. -/
theorem toF_subF (a b : F) : toF (subF a b) = toF a - toF b := by
  rw [subF_eq, toF_sub]

/-- The program's negative of a word is the field's. -/
theorem toF_negF (a : F) : toF (negF a) = -toF a := by
  rw [negF_eq, toF_neg]

/-- The program's product of words is the field's. -/
theorem toF_mulF (a b : F) : toF (mulF a b) = toF a * toF b := by
  rw [mulF_eq, toF_mul]

/-- The program's power of a word is the field's. -/
theorem toF_powF (a : F) (e : ℕ) : toF (powF a e) = toF a ^ e := by
  rw [powF_eq, toF_pow]

/-- The program's inverse of a word is the field's; 0 goes to 0. -/
theorem toF_invF (a : F) : toF (invF a) = (toF a)⁻¹ := by
  rw [invF_eq, toF_inv]

/-- The program's double of a word is twice the field's element. -/
theorem toF_twiceF (a : F) : toF (twiceF a) = 2 * toF a := by
  rw [twiceF_eq, toF_mul, toF_cW]

/-- A word and its residue modulo p are read as one element. -/
theorem toF_normF (a : F) : toF (normF a) = toF a := by
  unfold toF
  rw [toNat_normF, ← Code.pGold_eq]
  exact ZMod.natCast_mod _ _

/-! ## How an element of the program is read -/

/-- An element of the program, read in the extension field. -/
def readE (x : E) : Cb.Gl.E := toE x.triple

/-- Entry i of an array of elements of the program, read in the extension field; 0 beyond the
end. -/
def readV (v : Array E) (i : ℕ) : Cb.Gl.E := readE (v.getD i zeroE)

/-- Entry i of a list of elements of the program, read in the extension field; 0 beyond the end. -/
def readL (l : List E) (i : ℕ) : Cb.Gl.E := readE (l.getD i zeroE)

/-- The first n entries of a list of elements of the program, as a point. -/
def readP (n : ℕ) (l : List E) : Fin n → Cb.Gl.E := fun i => readL l i.val

/-- How an element of the program is read: through its three words. -/
theorem readE_def (x : E) : readE x = toE x.triple := rfl

/-- A coordinate of a point that is read from a list. -/
theorem readP_apply (n : ℕ) (l : List E) (i : Fin n) : readP n l i = readL l i.val := rfl

/-- The element that a triple of words spells is read as the triple. -/
theorem readE_ofTriple (t : Fmt.Ext3) : readE (E.ofTriple t) = toE t := by
  rw [readE_def, E.triple_ofTriple]

/-- An element is read coordinate by coordinate. -/
theorem readE_mk3 (a b c : F) : readE (E.mk3 a b c) = ⟨toF a, toF b, toF c⟩ := rfl

/-- The first coordinate of what is read is the first word, read. -/
theorem readE_c0 (x : E) : (readE x).c0 = toF x.c0 := rfl

/-- The second coordinate of what is read is the second word, read. -/
theorem readE_c1 (x : E) : (readE x).c1 = toF x.c1 := rfl

/-- The third coordinate of what is read is the third word, read. -/
theorem readE_c2 (x : E) : (readE x).c2 = toF x.c2 := rfl

/-! ## The extension field -/

/-- The program's zero is read as 0. -/
theorem readE_zero : readE zeroE = 0 := by
  rw [readE_def, zeroE_triple]
  exact toE_zeroE

/-- The program's one is read as 1. -/
theorem readE_one : readE oneE = 1 := by
  rw [readE_def, oneE_triple]
  exact toE_oneE

/-- A word as an element of the extension field is the image of the base field's element. -/
theorem readE_ofF (a : F) : readE (OnBytes.ofF a) = algebraMap Cb.Gl.F Cb.Gl.E (toF a) := by
  rw [readE_def, ofF_triple]
  exact toE_ofF a

/-- The program's sum is read as the sum. -/
theorem readE_add (a b : E) : readE (addE a b) = readE a + readE b := by
  rw [readE_def, readE_def, readE_def, addE_triple, toE_addE]

/-- The program's difference is read as the difference. -/
theorem readE_sub (a b : E) : readE (subE a b) = readE a - readE b := by
  rw [readE_def, readE_def, readE_def, subE_triple, toE_subE]

/-- The program's negative is read as the negative. -/
theorem readE_neg (a : E) : readE (negE a) = -readE a := by
  rw [readE_def, readE_def, negE_triple, toE_negE]

/-- The program's multiple by a word is read as the multiple. -/
theorem readE_scale (s : F) (a : E) : readE (scaleE s a) = toF s • readE a := by
  rw [readE_def, readE_def, scaleE_triple, toE_scaleE]

/-- The program's product is read as the product. -/
theorem readE_mul (a b : E) : readE (mulE a b) = readE a * readE b := by
  rw [readE_def, readE_def, readE_def, mulE_triple, toE_mulE]

/-- The program's inverse is read as the inverse; 0 goes to 0. -/
theorem readE_inv (a : E) : readE (invE a) = (readE a)⁻¹ := by
  rw [readE_def, readE_def, invE_triple, toE_invE]

/-- a + s x, with all three in the extension field. -/
theorem readE_maddE (a s x : E) : readE (maddE a s x) = readE a + readE s * readE x := by
  rw [readE_def, readE_def, readE_def, readE_def, maddE_triple, toE_addE, toE_mulE]

/-- a + s x, with s in the base field. -/
theorem readE_maddS (a : E) (s : F) (x : E) :
    readE (maddS a s x) = readE a + toF s • readE x := by
  rw [readE_def, readE_def, readE_def, maddS_triple, toE_addE, toE_scaleE]

/-- The loop of the power, if the bound on its steps is at least the exponent. -/
theorem readE_powLoopE : ∀ (k : ℕ) (x : E) (e : ℕ) (r : E), e ≤ k →
    readE (powLoopE k x e r) = readE r * readE x ^ e
  | 0, x, e, r, he => by
      have e0 : e = 0 := Nat.le_zero.1 he
      rw [e0, powLoopE_zero, pow_zero, mul_one]
  | k + 1, x, e, r, he => by
      by_cases e0 : e = 0
      · rw [e0, powLoopE_zero, pow_zero, mul_one]
      · have hk : e / 2 ≤ k := by omega
        have sq : (readE x * readE x) ^ (e / 2) = readE x ^ (2 * (e / 2)) := by
          rw [pow_mul, pow_two]
        rw [powLoopE_step k x e r e0, readE_powLoopE k _ _ _ hk, readE_mul, sq]
        by_cases odd : e % 2 = 1
        · have he2 : 2 * (e / 2) + 1 = e := by omega
          rw [if_pos odd, readE_mul, mul_assoc, ← pow_succ', he2]
        · have he2 : 2 * (e / 2) = e := by omega
          rw [if_neg odd, he2]

/-- The program's power is read as the power. -/
theorem readE_pow (a : E) (e : ℕ) : readE (powE a e) = readE a ^ e := by
  unfold powE
  rw [readE_powLoopE e a e oneE (Nat.le_refl e), readE_one, one_mul]

/-! ## Arrays and lists -/

/-- Every entry of the empty list is read as 0. -/
theorem readL_nil (i : ℕ) : readL [] i = 0 := readE_zero

/-- The first entry of a list. -/
theorem readL_cons_zero (a : E) (l : List E) : readL (a :: l) 0 = readE a := rfl

/-- A later entry of a list. -/
theorem readL_cons_succ (a : E) (l : List E) (i : ℕ) : readL (a :: l) (i + 1) = readL l i := rfl

/-- An entry that a list does not have is read as 0. -/
theorem readL_of_le (l : List E) (i : ℕ) (h : l.length ≤ i) : readL l i = 0 := by
  unfold readL
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]
  exact readE_zero

/-- An array made from a list is read as the list. -/
theorem readV_toArray (l : List E) (i : ℕ) : readV l.toArray i = readL l i := by
  unfold readV readL
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- An array is read as its list. -/
theorem readV_eq_readL (v : Array E) (i : ℕ) : readV v i = readL v.toList i :=
  readV_toArray v.toList i

/-- An entry that an array does not have is read as 0. -/
theorem readV_of_le (v : Array E) (i : ℕ) (h : v.size ≤ i) : readV v i = 0 := by
  rw [readV_eq_readL]
  exact readL_of_le _ _ (by rw [Array.length_toList]; exact h)

/-! ## What the tests on words mean -/

/-- Equal elements of the program are read as one element of the field. -/
theorem readE_of_beq (a b : E) (h : (a == b) = true) : readE a = readE b :=
  congrArg readE (beq_iff_eq.1 h)

/-- On words below p the reading is injective. -/
theorem readE_inj (a b : E) (ha : okE a = true) (hb : okE b = true) (h : readE a = readE b) :
    a = b := by
  rw [okE_triple] at ha hb
  have ht : a.triple = b.triple := toE_inj a.triple b.triple ha hb h
  rw [← E.ofTriple_triple a, ht, E.ofTriple_triple]

/-- On words below p, two elements of the program are equal exactly if they are read as one
element of the field. -/
theorem beq_iff_readE (a b : E) (ha : okE a = true) (hb : okE b = true) :
    (a == b) = true ↔ readE a = readE b :=
  ⟨readE_of_beq a b, fun h => beq_iff_eq.2 (readE_inj a b ha hb h)⟩

/-- The test for three words 0, as an equation of elements. -/
theorem isZeroE_eq (a : E) : isZeroE a = true ↔ a = zeroE := by
  unfold isZeroE
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨⟨h0, h1⟩, h2⟩
    exact E.ext3 h0 h1 h2
  · intro h
    rw [h]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- If all three words are 0, the element is 0. -/
theorem readE_of_isZeroE (a : E) (h : isZeroE a = true) : readE a = 0 := by
  rw [(isZeroE_eq a).1 h]
  exact readE_zero

/-- On words below p, all three words are 0 exactly if the element is 0. -/
theorem isZeroE_iff (a : E) (ha : okE a = true) : isZeroE a = true ↔ readE a = 0 :=
  ⟨readE_of_isZeroE a,
    fun h => (isZeroE_eq a).2 (readE_inj a zeroE ha rfl (h.trans readE_zero.symm))⟩

end OnBytes.Slice

#print axioms OnBytes.Slice.toF_addF
#print axioms OnBytes.Slice.toF_subF
#print axioms OnBytes.Slice.toF_negF
#print axioms OnBytes.Slice.toF_mulF
#print axioms OnBytes.Slice.toF_powF
#print axioms OnBytes.Slice.toF_invF
#print axioms OnBytes.Slice.toF_twiceF
#print axioms OnBytes.Slice.toF_normF
#print axioms OnBytes.Slice.readE_def
#print axioms OnBytes.Slice.readP_apply
#print axioms OnBytes.Slice.readE_ofTriple
#print axioms OnBytes.Slice.readE_mk3
#print axioms OnBytes.Slice.readE_c0
#print axioms OnBytes.Slice.readE_c1
#print axioms OnBytes.Slice.readE_c2
#print axioms OnBytes.Slice.readE_zero
#print axioms OnBytes.Slice.readE_one
#print axioms OnBytes.Slice.readE_ofF
#print axioms OnBytes.Slice.readE_add
#print axioms OnBytes.Slice.readE_sub
#print axioms OnBytes.Slice.readE_neg
#print axioms OnBytes.Slice.readE_scale
#print axioms OnBytes.Slice.readE_mul
#print axioms OnBytes.Slice.readE_inv
#print axioms OnBytes.Slice.readE_maddE
#print axioms OnBytes.Slice.readE_maddS
#print axioms OnBytes.Slice.readE_powLoopE
#print axioms OnBytes.Slice.readE_pow
#print axioms OnBytes.Slice.readL_nil
#print axioms OnBytes.Slice.readL_cons_zero
#print axioms OnBytes.Slice.readL_cons_succ
#print axioms OnBytes.Slice.readL_of_le
#print axioms OnBytes.Slice.readV_toArray
#print axioms OnBytes.Slice.readV_eq_readL
#print axioms OnBytes.Slice.readV_of_le
#print axioms OnBytes.Slice.readE_of_beq
#print axioms OnBytes.Slice.readE_inj
#print axioms OnBytes.Slice.beq_iff_readE
#print axioms OnBytes.Slice.isZeroE_eq
#print axioms OnBytes.Slice.readE_of_isZeroE
#print axioms OnBytes.Slice.isZeroE_iff
