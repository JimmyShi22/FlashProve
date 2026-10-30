-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Field/ExtEq.lean: the operations of the cubic extension on machine words are those of
Fmt/FieldE.lean at its second field.

Fmt/ spells an element as a triple of words; `E.triple` takes an element to that triple.

Main theorems: `zeroE_triple`, `oneE_triple`, `ofF_triple`, `okE_triple`, `addE_triple`,
`subE_triple`, `negE_triple`, `scaleE_triple`, `mulE_triple`, `adjE_triple`, `normE_triple`,
`invE_triple`, `maddE_triple`, `maddS_triple`, `foldPairE_triple`. They hold for all words, also
for words that are not below p. For the power, which Fmt/FieldE.lean does not have: `powE_zero`,
`powLoopE_zero` and `powLoopE_step` say how it is made of products.

Whether these are the operations of a field: OnBytes/Slice/ProgField.lean, not here.
-/
import OnBytes.Field.Ext
import OnBytes.Field.PowEq

namespace OnBytes

/-- As a number, the constant c of Fmt/ with X^3 = c is 2. -/
theorem toNat_cW : Fmt.Fld.two.cW.toNat = 2 := by
  rw [Fmt.Fld.cW, Fmt.Fld.toNat_red]
  rfl

/-- Twice an element is its product with the constant c of Fmt/. -/
theorem twiceF_eq (a : UInt64) : twiceF a = Fmt.Fld.two.mul Fmt.Fld.two.cW a := by
  unfold twiceF Fmt.Fld.mul
  apply eq_red
  rw [toNat_addF, toNat_cW]
  congr 1
  omega

/-- The triple of an element that is given by its coordinates a, b, c is (a, b, c). -/
theorem triple_mk3 (a b c : UInt64) : (E.mk3 a b c).triple = (a, b, c) := rfl

/-- The first word of the triple is `c0`. -/
theorem triple_fst (x : E) : x.triple.1 = x.c0 := rfl

/-- The second word of the triple is `c1`. -/
theorem triple_snd (x : E) : x.triple.2.1 = x.c1 := rfl

/-- The third word of the triple is `c2`. -/
theorem triple_trd (x : E) : x.triple.2.2 = x.c2 := rfl

/-- Two elements with the same three words are equal. -/
theorem triple_inj {x y : E} (h : x.triple = y.triple) : x = y :=
  congrArg E.ofTriple h

/-- The element 0 is that of Fmt/FieldE.lean. -/
theorem zeroE_triple : zeroE.triple = Fmt.Fld.zeroE := rfl

/-- The element 1 is that of Fmt/FieldE.lean. -/
theorem oneE_triple : oneE.triple = Fmt.Fld.oneE := rfl

/-- An element of the base field as an element of E is that of Fmt/FieldE.lean. -/
theorem ofF_triple (a : UInt64) : (ofF a).triple = Fmt.Fld.ofF a := rfl

/-- The test that all three words are below p is that of Fmt/FieldE.lean. -/
theorem okE_triple (a : E) : okE a = Fmt.Fld.two.okE a.triple := by
  unfold okE Fmt.Fld.okE
  simp only [okF_eq, triple_fst, triple_snd, triple_trd]

/-- The sum in E is that of Fmt/FieldE.lean. -/
theorem addE_triple (a b : E) : (addE a b).triple = Fmt.Fld.two.addE a.triple b.triple := by
  unfold addE Fmt.Fld.addE
  simp only [addF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- The difference in E is that of Fmt/FieldE.lean. -/
theorem subE_triple (a b : E) : (subE a b).triple = Fmt.Fld.two.subE a.triple b.triple := by
  unfold subE Fmt.Fld.subE
  simp only [subF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- The negative in E is that of Fmt/FieldE.lean. -/
theorem negE_triple (a : E) : (negE a).triple = Fmt.Fld.two.negE a.triple := by
  unfold negE Fmt.Fld.negE
  simp only [negF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- The product of an element of the base field and one of E is that of Fmt/FieldE.lean. -/
theorem scaleE_triple (s : UInt64) (a : E) :
    (scaleE s a).triple = Fmt.Fld.two.scaleE s a.triple := by
  unfold scaleE Fmt.Fld.scaleE
  simp only [mulF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- The product in E is that of Fmt/FieldE.lean. -/
theorem mulE_triple (a b : E) : (mulE a b).triple = Fmt.Fld.two.mulE a.triple b.triple := by
  unfold mulE mulE0 mulE1 mulE2 mulW0 mulW1 mulW2 Fmt.Fld.mulE
  simp only [twiceF_eq, addF_eq, mulF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- The three cofactors are those of Fmt/FieldE.lean. -/
theorem adjE_triple (a : E) : (adjE a).triple = Fmt.Fld.two.adjE a.triple := by
  unfold adjE Fmt.Fld.adjE
  simp only [twiceF_eq, subF_eq, mulF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- The norm's last step, from an element a and any three words c in the cofactors' place. -/
theorem normStep (a c : E) :
    addF (mulF a.c0 c.c0) (twiceF (addF (mulF a.c2 c.c1) (mulF a.c1 c.c2))) =
      Fmt.Fld.two.add (Fmt.Fld.two.mul a.triple.1 c.triple.1)
        (Fmt.Fld.two.mul Fmt.Fld.two.cW (Fmt.Fld.two.add (Fmt.Fld.two.mul a.triple.2.2 c.triple.2.1)
          (Fmt.Fld.two.mul a.triple.2.1 c.triple.2.2))) := by
  simp only [twiceF_eq, addF_eq, mulF_eq, triple_fst, triple_snd, triple_trd]

/-- The norm is that of Fmt/FieldE.lean. -/
theorem normE_triple (a : E) : normE a = Fmt.Fld.two.normE a.triple := by
  unfold normE Fmt.Fld.normE
  rw [← adjE_triple]
  exact normStep a (adjE a)

/-- The inverse in E is that of Fmt/FieldE.lean. -/
theorem invE_triple (a : E) : (invE a).triple = Fmt.Fld.two.invE a.triple := by
  unfold invE Fmt.Fld.invE
  rw [scaleE_triple, invF_eq, normE_triple, adjE_triple]

/-- `maddE a s x` is a + s x in the operations of Fmt/FieldE.lean, with all three in E. -/
theorem maddE_triple (a s x : E) : (maddE a s x).triple =
    Fmt.Fld.two.addE a.triple (Fmt.Fld.two.mulE s.triple x.triple) := by
  unfold maddE mulE0 mulE1 mulE2 mulW0 mulW1 mulW2 Fmt.Fld.addE Fmt.Fld.mulE
  simp only [twiceF_eq, addF_eq, mulF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- `maddS a s x` is a + s x in the operations of Fmt/FieldE.lean, with s in the base field. -/
theorem maddS_triple (a : E) (s : UInt64) (x : E) : (maddS a s x).triple =
    Fmt.Fld.two.addE a.triple (Fmt.Fld.two.scaleE s x.triple) := by
  unfold maddS Fmt.Fld.addE Fmt.Fld.scaleE
  simp only [addF_eq, mulF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- `foldPairE a b g` is a + g (b - a) in the operations of Fmt/FieldE.lean. -/
theorem foldPairE_triple (a b g : E) : (foldPairE a b g).triple =
    Fmt.Fld.two.addE a.triple (Fmt.Fld.two.mulE g.triple (Fmt.Fld.two.subE b.triple a.triple)) := by
  unfold foldPairE mulW0 mulW1 mulW2 Fmt.Fld.addE Fmt.Fld.mulE Fmt.Fld.subE
  simp only [twiceF_eq, addF_eq, subF_eq, mulF_eq, triple_mk3, triple_fst, triple_snd, triple_trd]

/-- `foldPairE a b g` is a + g (b - a) in the operations of this directory. -/
theorem foldPairE_def (a b g : E) : foldPairE a b g = addE a (mulE g (subE b a)) := by
  apply triple_inj
  rw [foldPairE_triple, addE_triple, mulE_triple, subE_triple]

/-! ## The power -/

/-- The loop of `powE` at the exponent 0 returns what it was given. -/
theorem powLoopE_zero (k : Nat) (x r : E) : powLoopE k x 0 r = r := by
  cases k <;> rfl

/-- One step of the loop of `powE`, for an exponent that is not 0. -/
theorem powLoopE_step (k : Nat) (x : E) (e : Nat) (r : E) (h : e ≠ 0) : powLoopE (k + 1) x e r =
    powLoopE k (mulE x x) (e / 2) (if e % 2 = 1 then mulE r x else r) := by
  show (if e = 0 then r else _) = _
  rw [if_neg h]

/-- The power with the exponent 0 is 1. -/
theorem powE_zero (a : E) : powE a 0 = oneE := rfl

end OnBytes

#print axioms OnBytes.mulE_triple
#print axioms OnBytes.invE_triple
#print axioms OnBytes.maddE_triple
#print axioms OnBytes.maddS_triple
