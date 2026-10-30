-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyBase4.lean: a Reed-Solomon code of length 8 and dimension 4 over the field with p =
2^64 - 2^32 + 1 elements, read over its cubic extension, as a small test instance: its distance is
at least 5, and at the radius 1 it decodes uniquely and has mutual correlated agreement, all proved.

A second code for toys over p = 2^64 - 2^32 + 1: on the same eight positions, hiding three.
Definitions, statements (`Cb.Gl.Spec.gl_toy84`, `Cb.Gl.Spec.toyStd84_third`) and proofs. A guard
against empty theorems; no parameter of a protocol. The analogue of Cb/GlVal/GlToyBase.lean and
Cb/GlVal/GlToyMsg.lean for this code.

Why: a toy of the test at two instances needs encodings that bear 3 positions (a message stands in
the shared test and in a test of each of two slots: 1 + 2 · 1). Over the field with 101 elements
that is the code of Cb/Ld/LdRelToy7d4.lean (seven points, dimension 4, distance 4).

Main names:
  `C84`: `rs 3 3 1 3 1 2`: the subgroup of order 8; dimension 4: one message symbol, three symbols
    of randomness (they fill the dimension); distance 5; radius 1 in its data.
  `Spec.gl_toy84`: for every R: `GlC (toyLd84 R) 5 3` (Cb/Gl/GlLd.lean), so: laws, distance 5,
    transparent, reads what it declares, zero knowledge at 3 positions; 3 · 1 < 5; lists of at most
    one member and at most 2 exceptional values at the radius 1.
  `list84`, `mca84`: the last two for every code at these eight positions with the laws and the
    distance 5.
  `toyPlace84`, `toyStd84 Dt μ plc`: the standard oracle message (`StdM E P84`,
    Cb/Obj/LdObjectToyKit.lean) at the radius 1; the pad's coefficient is the one value 1.
  `Spec.toyStd84_third`: for every finite Dt and every injective placement:
    `(toyStd84 Dt μ plc).Third 5 3` (Cb/Obj/LdObjectThirdStd.lean).

Notation: `rs a k msg r e mca` (Cb/Gl/GlCodes.lean; `Code.RS.code`, Code/RS.lean): length 2^a;
dimension k + 1; msg message symbols; r uniform coordinates behind them; e: the proximity parameter;
mca: the count for mutual correlated agreement. `F`, `E`: the field with p elements; its cubic
extension (Cb/Gl/GlField.lean).

Limits: against Cb/Ld/LdRelToy7d4.lean: there the code is read at the radius 2, not below half its
distance 4; here at the radius 1, within a third of 5. A toy built on this file exercises less. This
file says nothing on real parameters.
Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyBase
import Cb.Obj.LdObjectThirdStd

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop Cb.Ood

/-- The code that hides three positions. -/
def C84 : Code.Enc F := rs 3 3 1 3 1 2

/-- Its positions. -/
abbrev P84 : Type := (Reading.one C84).P

/-- Rows R under `C84`, read as they stand. -/
@[reducible] def toyLd84 (R : Type) [Fintype R] [DecidableEq R] : LdCode E P84 :=
  (Reading.one C84).ld E fun _ => R

namespace Spec

def gl_toy84 : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R], GlC (toyLd84 R) 5 3 ∧ (toyLd84 R).Laws ∧
    (toyLd84 R).Dist 5 ∧ (toyLd84 R).Transparent ∧ (toyLd84 R).Reads ∧ (toyLd84 R).Zk 3 ∧
    3 * 1 < 5 ∧ (toyLd84 R).ListAt 1 1 ∧ (toyLd84 R).MCAat 1 2

end Spec

theorem core84 : C84.Core := gl_rs_core 3 3 1 3 1 2 (by norm_num) (by norm_num) (by norm_num)
theorem d84 : C84.d = 5 := rfl
theorem dist84 : HasDist C84.G C84.d := rs_hasDist 1 3 1 2 (by norm_num) (by norm_num)
theorem card84 : Fintype.card P84 = 8 := Fintype.card_fin 8
instance neP84 : Nonempty P84 := ⟨(⟨0, by norm_num⟩ : Fin (2 ^ 3))⟩

theorem list84 (D : LdCode E P84) (hL : D.Laws) (hD : D.Dist 5) : D.ListAt 1 1 :=
  ld_list_unique E P84 D 5 1 hL hD (by norm_num)
theorem mca84 (D : LdCode E P84) (hL : D.Laws) (hD : D.Dist 5) : D.MCAat 1 2 :=
  ld_mca_third E P84 D 5 1 hL hD (by norm_num)

theorem glC84 (R : Type) [Fintype R] [DecidableEq R] : GlC (toyLd84 R) 5 3 :=
  .base (gl_code_one 3 3 1 3 R (by norm_num) (by norm_num) (by norm_num))

theorem gl_toy84 : Spec.gl_toy84 := fun R _ _ =>
  have h := glC_code P84 (toyLd84 R) 5 3 (glC84 R)
  ⟨glC84 R, h.1, h.2.2.2.1, h.2.1, h.2.2.1, h.2.2.2.2, by norm_num,
    list84 _ h.1 h.2.2.2.1, mca84 _ h.1 h.2.2.2.1⟩

/-- Each row holds one message symbol. -/
def toyPlace84 (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd84 R).J where
  toFun r := ⟨(), (r, (0 : Fin 1))⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, r, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    rfl

/-- The standard oracle message under the code that hides three, radius 1. -/
@[reducible] def toyStd84 (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM E P84 where
  Cm := toyLd84 (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace84 (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Unit
  b := fun _ => 1
  e := 1

def Spec.toyStd84_third : Prop :=
  ∀ (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ] (plc : Dt → μ → Bool),
    Function.Injective plc → (toyStd84 Dt μ plc).Third 5 3

theorem toyStd84_third : Spec.toyStd84_third := by
  intro Dt μ _ _ _ _ plc hp
  obtain ⟨-, hL, hD, hT, -, hZ, -, -, -⟩ := gl_toy84 (Dt ⊕ Unit)
  exact ⟨hL, hD, (by norm_num : 3 * 1 < 5), hT, hZ, hp, fun _ _ _ => rfl, fun _ => one_ne_zero⟩

end Cb.Gl
