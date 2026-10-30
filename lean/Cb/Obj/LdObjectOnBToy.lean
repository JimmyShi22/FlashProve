-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectOnBToy.lean: the standard oracle message of the toys at the seven-point code of
dimension 4 of Cb/Ld/LdRelToy7d4.lean (`LdToy74.toyStd74`, with `toyStd74_ok`), and two counts.








Definitions and proofs.

























Main names:
  `toyStd74 Dt μ plc`: rows Dt ⊕ Unit (data, one pad) under that code (one message symbol, three
    symbols of randomness; distance 4), at the radius 2: not below half the distance.
  `toyStd74_ok`: for plc injective, `M.OK 3 3`, distance 4, transparent.
  `stdLnB_toy_num`: for μ of m elements, two counts written out in powers of 101.

Limits: no security: these are the numbers of a toy.




Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectOnBStdV
import Cb.Obj.LdObjectToyConf7
import Cb.Ld.LdRelToy7d4
import Cb.Ld.LdSendToy

set_option autoImplicit false

namespace Cb
namespace LdToy74
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy LdToy7

/-- each row holds one message symbol -/
def toyPlace74 (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd74 R).J where
  toFun r := ⟨(), (r, (0 : Fin 1))⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, r, i⟩
    have h : i.val < 1 := i.isLt
    have hi : i = (0 : Fin 1) := Fin.ext (show i.val = 0 from Nat.lt_one_iff.1 h)
    subst hi
    rfl

/-- The standard oracle message at the code of dimension 4. -/
@[reducible] def toyStd74 (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM K P74 where
  Cm := toyLd74 (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace74 (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Bn
  b := fun β => β.1
  e := 2

theorem toyStd74_ok (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) :
    (toyStd74 Dt μ plc).OK 3 3 ∧
    (toyStd74 Dt μ plc).Cm.Dist 4 ∧
    (toyStd74 Dt μ plc).Cm.Transparent := by
  obtain ⟨hL, hD, -, hl, -, -, hz, ht, -⟩ := ld_toy74 (Dt ⊕ Unit)
  exact ⟨⟨hL, hl, hz, hp, fun _ _ h => Subtype.ext h, fun β => β.2⟩, hD, ht⟩

instance : Nonempty P74 := ⟨(0 : Fin 7)⟩

end LdToy74

open Iop Prob Hiop Blocks Cb.Ood IOR LdToy LdToy7 LdToy74

theorem stdLnB_toy_num (μ : Type) [Fintype μ] [DecidableEq μ] (m : ℕ) (hm : Fintype.card μ = m) :
    max (Fintype.card μ * Fintype.card K ^ (Fintype.card μ - 1) * Fintype.card Bn)
        (Fintype.card K ^ Fintype.card μ) =
      max (m * 101 ^ (m - 1) * 100) (101 ^ m) ∧
    Fintype.card ((μ → K) × Bn) = 101 ^ m * 100 := by
  have hB : Fintype.card Bn = 100 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ZMod.card]
  rw [Fintype.card_prod, Fintype.card_fun, hB, ZMod.card, hm]
  exact ⟨rfl, rfl⟩

end Cb
