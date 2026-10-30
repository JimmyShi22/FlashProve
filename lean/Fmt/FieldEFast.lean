-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/FieldEFast.lean: the product in the cubic extension with one reduction per coordinate; and a
product with an element of the base field is a scaling. Both are theorems on the functions of
Fmt/FieldE.lean.

Fmt/FieldE.lean computes on 64-bit words: in F = Z / p for the format's two values of p (`Fld.p`,
Fmt/Rules1.lean), and in E = F[X] / (X^3 - c), where an element is a triple of words (`Ext3`); what
is not claimed of these: part 4.

Why. Fmt/FieldE.lean's `mulE` reduces modulo p after each of its sums and products: seventeen
reductions. A protocol's decision multiplies in E some hundred thousand times. No Mathlib. The file
imports Fmt/FieldE.lean alone.

1. What the file contains. Definitions that can be evaluated.
   `Fld.mulEF f a b`, `Fld.maddS f a p w`, `Fld.maddE f a s x`.

2. What is checked when the file compiles. Four tests (#guard).

3. Theorems.
   `mulEF_eq`: mulEF f a b = mulE f a b, for both fields and all words (also words that are not
     below p).
   `mulE_ofF`: mulE f (ofF s) a = scaleE f s a: three products in the place of eleven (nine of
     coordinates, two by c).
   `mulE_comm`, `mulE_ofF'`, `maddS_eq`, `maddE_eq`, `Fld.toNat_red`, `Fld.red_congr`.
   Many statements of this library are written twice: a definition in the namespace `Spec` states a
   proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

4. What is not claimed. How fast anything is: that is measured outside this file. That these are
field operations.
-/
import Fmt.FieldE

namespace Fmt
namespace Fld

theorem toNat_red (f : Fld) (n : Nat) : (f.red n).toNat = n % f.p := by
  unfold red
  exact UInt64.toNat_ofNat_of_lt' (Nat.lt_trans (Nat.mod_lt _ f.p_pos) f.p_lt)

theorem red_congr (f : Fld) {m n : Nat} (h : m % f.p = n % f.p) : f.red m = f.red n := by
  unfold red
  rw [h]

/-- The product in E, one reduction per coordinate. -/
def mulEF (f : Fld) (a b : Ext3) : Ext3 :=
  (f.red (a.1.toNat * b.1.toNat + f.c * (a.2.1.toNat * b.2.2.toNat + a.2.2.toNat * b.2.1.toNat)),
   f.red (a.1.toNat * b.2.1.toNat + a.2.1.toNat * b.1.toNat + f.c * (a.2.2.toNat * b.2.2.toNat)),
   f.red (a.1.toNat * b.2.2.toNat + a.2.1.toNat * b.2.1.toNat + a.2.2.toNat * b.1.toNat))

end Fld

def Spec.mulEF_eq : Prop := ∀ (f : Fld) (a b : Ext3), f.mulEF a b = f.mulE a b

theorem mulEF_eq : Spec.mulEF_eq := by
  intro f a b
  unfold Fld.mulEF Fld.mulE Fld.add Fld.mul Fld.cW
  simp only [Fld.toNat_red]
  refine Prod.ext (Fld.red_congr f ?_) (Prod.ext (Fld.red_congr f ?_) (Fld.red_congr f ?_))
    <;> simp [Nat.add_mod, Nat.mul_mod]

def Spec.mulE_ofF : Prop := ∀ (f : Fld) (s : UInt64) (a : Ext3), f.mulE (Fld.ofF s) a = f.scaleE s a

theorem mulE_ofF : Spec.mulE_ofF := by
  intro f s a
  rw [← mulEF_eq f]
  unfold Fld.mulEF Fld.ofF Fld.scaleE Fld.mul
  simp

def Spec.mulE_comm : Prop := ∀ (f : Fld) (a b : Ext3), f.mulE a b = f.mulE b a

theorem mulE_comm : Spec.mulE_comm := by
  intro f a b
  rw [← mulEF_eq f a b, ← mulEF_eq f b a]
  unfold Fld.mulEF
  refine Prod.ext (congrArg f.red ?_) (Prod.ext (congrArg f.red ?_) (congrArg f.red ?_))
  · rw [Nat.mul_comm a.1.toNat, Nat.mul_comm a.2.1.toNat, Nat.mul_comm a.2.2.toNat,
      Nat.add_comm (b.2.2.toNat * a.2.1.toNat)]
  · rw [Nat.mul_comm a.1.toNat, Nat.mul_comm a.2.1.toNat,
      Nat.mul_comm a.2.2.toNat, Nat.add_comm (b.2.1.toNat * a.1.toNat)]
  · rw [Nat.mul_comm a.1.toNat, Nat.mul_comm a.2.1.toNat, Nat.mul_comm a.2.2.toNat]
    simp only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

def Spec.mulE_ofF' : Prop :=
  ∀ (f : Fld) (a : Ext3) (s : UInt64), f.mulE a (Fld.ofF s) = f.scaleE s a

theorem mulE_ofF' : Spec.mulE_ofF' := fun f a s =>
  (mulE_comm f a (Fld.ofF s)).trans (mulE_ofF f s a)

/-- a + p w, p in the base field: one reduction per coordinate -/
def Fld.maddS (f : Fld) (a : Ext3) (p : UInt64) (w : Ext3) : Ext3 :=
  (f.red (a.1.toNat + p.toNat * w.1.toNat),
    f.red (a.2.1.toNat + p.toNat * w.2.1.toNat),
    f.red (a.2.2.toNat + p.toNat * w.2.2.toNat))

def Spec.maddS_eq : Prop :=
  ∀ (f : Fld) (a : Ext3) (p : UInt64) (w : Ext3), f.maddS a p w = f.addE a (f.scaleE p w)

theorem maddS_eq : Spec.maddS_eq := by
  intro f a p w
  unfold Fld.maddS Fld.addE Fld.scaleE Fld.add Fld.mul
  simp only [Fld.toNat_red]
  refine Prod.ext (Fld.red_congr f ?_) (Prod.ext (Fld.red_congr f ?_) (Fld.red_congr f ?_))
    <;> simp [Nat.add_mod]

/-- a + s x in E: one reduction per coordinate -/
def Fld.maddE (f : Fld) (a s x : Ext3) : Ext3 :=
  (f.red (a.1.toNat +
        (s.1.toNat * x.1.toNat + f.c * (s.2.1.toNat * x.2.2.toNat + s.2.2.toNat * x.2.1.toNat))),
    f.red (a.2.1.toNat +
        (s.1.toNat * x.2.1.toNat + s.2.1.toNat * x.1.toNat + f.c * (s.2.2.toNat * x.2.2.toNat))),
    f.red (a.2.2.toNat +
        (s.1.toNat * x.2.2.toNat + s.2.1.toNat * x.2.1.toNat + s.2.2.toNat * x.1.toNat)))

def Spec.maddE_eq : Prop := ∀ (f : Fld) (a s x : Ext3), f.maddE a s x = f.addE a (f.mulE s x)

theorem maddE_eq : Spec.maddE_eq := by
  intro f a s x
  rw [← mulEF_eq f s x]
  unfold Fld.maddE Fld.addE Fld.mulEF Fld.add
  simp only [Fld.toNat_red]
  refine Prod.ext (Fld.red_congr f ?_) (Prod.ext (Fld.red_congr f ?_) (Fld.red_congr f ?_))
    <;> simp [Nat.add_mod]

/-! ## Tests -/

#guard [Fld.one, Fld.two].all fun f => [(((5, 6, 7) : Ext3), ((8, 9, 10) : Ext3)), ((18446744073709551615, 18446744073709551615, 18446744073709551615), (18446744073709551615, 1, 18446744073709551615)),
  ((12345678901234567, 2, 998877665544332211), (2305843009213693950, 18446744069414584320, 3)), ((0, 0, 0), (1, 2, 3))].all fun x => f.mulEF x.1 x.2 == f.mulE x.1 x.2
#guard [Fld.one, Fld.two].all fun f => f.mulE (Fld.ofF 12345678901234567) (5, 6, 18446744069414584320) == f.scaleE 12345678901234567 (5, 6, 18446744069414584320)
#guard [Fld.one, Fld.two].all fun f => f.maddS (18446744073709551615, 6, 7) 18446744073709551615 (5, 18446744069414584320, 3) == f.addE (18446744073709551615, 6, 7) (f.scaleE 18446744073709551615 (5, 18446744069414584320, 3))
#guard [Fld.one, Fld.two].all fun f => f.maddE (18446744073709551615, 6, 7) (12345678901234567, 2, 998877665544332211) (5, 18446744069414584320, 3) == f.addE (18446744073709551615, 6, 7) (f.mulE (12345678901234567, 2, 998877665544332211) (5, 18446744069414584320, 3))

end Fmt
