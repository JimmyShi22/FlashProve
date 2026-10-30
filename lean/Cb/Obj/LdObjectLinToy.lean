-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectLinToy.lean: the standard oracle message of the toys at the seven-point code of
Cb/Ld/LdRelToy7.lean (`LdToy7.toyStd7`, with `toyStd7_ok`): dimension 3, distance 5.









Definitions and proofs.



















Main names:
  `toyStd7 Dt μ plc`: rows Dt ⊕ Unit (data, one pad) under that code (one message symbol, two
    symbols of randomness), at the radius 3: beyond half the distance.
  `toyStd7_ok`: for plc injective, `M.OK 7 2`, distance 5, transparent.
  `LdToy7.bn100`: `Bn` has 100 elements.














Limits: no security: these are the numbers of a toy.




Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectLinStd
import Cb.Obj.LdObjectToyConf
import Cb.Ld.LdRelToy7

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

namespace LdToy7
open LdToy

instance neP7 : Nonempty P7 := ⟨(⟨0, by decide⟩ : Fin 7)⟩
theorem msg7 : C7.msg = 1 := rfl

/-- each row holds one message symbol -/
def toyPlace7 (R : Type) [Fintype R] [DecidableEq R] : R ≃ (toyLd7 R).J where
  toFun r := ⟨(), (r, ⟨0, by rw [msg7]; exact Nat.one_pos⟩)⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨⟩, r, i⟩
    have hi : i.val = 0 := by
      have h : i.val < 1 := i.2
      omega
    exact congrArg (fun j => (⟨(), (r, j)⟩ : (toyLd7 R).J)) (Fin.ext hi.symm)

/-- The standard oracle message at seven points. -/
@[reducible] def toyStd7 (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM K P7 where
  Cm := toyLd7 (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace7 (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Bn
  b := fun β => β.1
  e := 3

theorem toyStd7_ok (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ]
    (plc : Dt → μ → Bool) (hp : Function.Injective plc) :
    (toyStd7 Dt μ plc).OK 7 2 ∧
    (toyStd7 Dt μ plc).Cm.Dist 5 ∧
    (toyStd7 Dt μ plc).Cm.Transparent := by
  obtain ⟨hL, hD, -, hl, -, -, hz, ht, -⟩ := ld_toy7 (Dt ⊕ Unit)
  exact ⟨⟨hL, hl, hz, hp, fun _ _ h => Subtype.ext h, fun β => β.2⟩, hD, ht⟩

end LdToy7

open LdToy LdToy7

theorem LdToy7.bn100 : Fintype.card Bn = 100 := by
  rw [Fintype.card_subtype_compl, ZMod.card, Fintype.card_subtype_eq]

end Cb
