-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyMsg.lean: a small test instance of an oracle message over a Reed-Solomon code of
length 8, read at the radius 1, within a third of its distance 6. Conditions that tests within a
third of the distance put on such a message (`StdM.Third`) are proved for it, for every injective
placement.

For the guard on the offline phase within a third, over p = 2^64 - 2^32 + 1.
Definitions, a statement (`Cb.Gl.Spec.toyStd8_third`) and its proof. No parameter of a protocol. The
analogue, over the two fields of Cb/Gl/GlField.lean, of `toyStd7` (Cb/Obj/LdObjectLinToy.lean), but
at the radius 1.

The code of Cb/GlVal/GlToyBase.lean (Reed-Solomon over F on the subgroup of order 8, one message
symbol and two symbols of randomness a row, distance 6, read over E; the encoding hides 2 long
positions), rows Dt ⊕ Unit (data, one pad), at the radius 1: 3 · 1 < 6.
The pad's coefficient is the one value 1 (the toy over 101 elements draws it among all values other
than 0; here nothing may enumerate the field (see "Why the numerals" in the head of
Cb/GlVal/GlToyBase.lean), and no condition asks for more than: different values, none of them 0).

Main names:
  `toyStd8 Dt μ plc`: the standard oracle message (`StdM E P8`, Cb/Obj/LdObjectToyKit.lean).
  `Spec.toyStd8_third`: for every finite Dt and every injective placement:
    `(toyStd8 Dt μ plc).Third 6 2` (Cb/Obj/LdObjectThirdStd.lean): laws, distance 6, 3 e < d,
    transparent, hides 2 positions, placement, pad.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToyBase
import Cb.Obj.LdObjectThirdStd

set_option autoImplicit false

namespace Cb.Gl
open Iop Prob Hiop Blocks Cb.Ood

/-- Each row holds one message symbol. -/
def toyPlace8 (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd8 R).J where
  toFun r := ⟨(), (r, (0 : Fin 1))⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, r, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    rfl

/-- The standard oracle message at the eight positions, radius 1. -/
@[reducible] def toyStd8 (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM E P8 where
  Cm := toyLd8 (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace8 (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Unit
  b := fun _ => 1
  e := 1

def Spec.toyStd8_third : Prop :=
  ∀ (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ] (plc : Dt → μ → Bool),
    Function.Injective plc → (toyStd8 Dt μ plc).Third 6 2

theorem toyStd8_third : Spec.toyStd8_third := by
  intro Dt μ _ _ _ _ plc hp
  obtain ⟨-, hL, hD, hT, -, hZ, -, -, -⟩ := gl_toy8 (Dt ⊕ Unit)
  exact ⟨hL, hD, (by norm_num : 3 * 1 < 6), hT, hZ, hp, fun _ _ _ => rfl, fun _ => one_ne_zero⟩

end Cb.Gl
