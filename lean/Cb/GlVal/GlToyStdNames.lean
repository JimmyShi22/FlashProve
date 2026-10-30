-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/GlVal/GlToyStdNames.lean: abbreviations: the Reed-Solomon code of length 8 and dimension 4 of
Cb/GlVal/GlToyBase4.lean, and a small test instance of an oracle message over it, under further
names, with restatements of the facts on them, some at weaker bounds.

For toys: the code that hides three over p = 2^64 - 2^32 + 1, and its standard oracle message, under
the names that the toys over the field with 101 elements use.
Abbreviations and restatements; nothing new is proved.
Toy files over `ZMod 101` cite Cb/Ld/LdRelToy.lean (five points: `toyLd`; `P5`:
Cb/Ld/LdSumPackToy.lean; `toyPlace`: Cb/Ld/LdTowerToyKit.lean), Cb/Ld/LdRelToy7d4.lean (seven
points, dimension 4: `P74`, `toyLd74`, `ld_toy74`), Cb/Obj/LdObjectOnBToy.lean (`toyPlace74`,
`toyStd74`, `toyStd74_ok`), Cb/Obj/LdObjectCtbToy.lean (`finNS_toy74`). Here, in namespace `Cb.Gl`,
all these names mean the one code of Cb/GlVal/GlToyBase4.lean (eight points, dimension 4, distance
5, hides 3), read at the radius 1, so that a toy file that cites these names can be stated over `F`
and `E` (Cb/Gl/GlField.lean) under the same names. The digits in the names are those files'; they
say nothing about this code.
The statements keep the shapes of those files': where a clause there is a bound, its number is kept
(distance at least 4; lists of at most 3; 3 hidden positions; but at most 2 exceptional values,
there 29): these bounds hold a fortiori; where the statement there says that the radius is not below
half the distance, counts the field, or bounds locality, the place holds "3 · 1 < 5", or "True".

`toyLd`, `ld_toy`: Cb/GlVal/GlToySend.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.GlVal.GlToySend
import Cb.Obj.LdObjectCtbToy

set_option autoImplicit false

namespace Cb.Gl
open Code Prob Blocks Iop Hiop Cb.Ood

abbrev P5 : Type := P84
abbrev P74 : Type := P84
abbrev toyLd74 (R : Type) [Fintype R] [DecidableEq R] : LdCode E P74 := toyLd84 R
abbrev toyPlace (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd R).J := toyPlace84 R
abbrev toyPlace74 (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd74 R).J := toyPlace84 R
abbrev toyStd74 (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM E P74 :=
  toyStd84 Dt μ plc

/-- In the shape of `ld_toy74` of Cb/Ld/LdRelToy7d4.lean. -/
theorem ld_toy74 (R : Type) [Fintype R] [DecidableEq R] :
    (toyLd74 R).Laws ∧ (toyLd74 R).Dist 4 ∧ 3 * 1 < 5 ∧ (toyLd74 R).ListAt 1 3 ∧
    (toyLd74 R).MCAat 1 2 ∧ True ∧ (toyLd74 R).Zk 3 ∧ (toyLd74 R).Transparent ∧ True := by
  obtain ⟨hG, hL, -, hT, -, hZ, h3, hLi, hM⟩ := gl_toy84 R
  exact ⟨hL, (glC_code P84 _ 4 3 (glC_mono P84 _ 5 3 4 3 hG (by norm_num) le_rfl)).2.2.2.1, h3,
    fun f => le_trans (hLi f) (by norm_num), hM, trivial, hZ, hT, trivial⟩

/-- In the shape of `toyStd74_ok` of Cb/Obj/LdObjectOnBToy.lean. -/
theorem toyStd74_ok (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) :
    (toyStd74 Dt μ plc).OK 3 3 ∧
    (toyStd74 Dt μ plc).Cm.Dist 4 ∧
    (toyStd74 Dt μ plc).Cm.Transparent := by
  obtain ⟨hL, hD, -, hl, -, -, hz, ht, -⟩ := ld_toy74 (Dt ⊕ Unit)
  exact ⟨⟨hL, hl, hz, hp, fun _ _ _ => rfl, fun _ => one_ne_zero⟩, hD, ht⟩

theorem finNS_toy74 (R : Type) [Fintype R] [DecidableEq R] : (toyLd74 R).FinNS := finNS_reading _ _
theorem finNS_toy74x (R : Type) (i₁ : Fintype R) (i₂ : DecidableEq R) : (@toyLd74 R i₁ i₂).FinNS :=
  @finNS_toy74 R i₁ i₂

end Cb.Gl
