-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectToyConf.lean: the toy's standard oracle messages over the five-point code.


In standard terms: a small example of oracle messages under a Reed-Solomon code with encoder over
the field with 101 elements. Example instances of the sub-protocols are built over them, to show
that the hypotheses of theorems can be met.


Definitions, statements and proofs. Shared by the guards on the object's sub-protocols; no parameter
of a protocol.

Main names:












  `LdToy.toyStd Dt μ plc`: the oracle messages (`StdM`, Cb/Obj/LdObjectToyKit.lean). Rows Dt ⊕ Unit
    (data, one pad) under the five-point code of Cb/Ld/LdRelToy.lean, distance 4, at the radius 2:
    not below half the distance; the pad's coefficient runs over the 100 non-zero elements.
  `Spec.toyStd_ok`: for plc injective, `M.OK 2 1` (lists of at most 2; one long position is hidden),
    distance 4, transparent.

Limits: no security.


Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectConfMore
import Cb.Obj.LdObjectToyKit
import Cb.Ld.LdTowerToyKit
import Cb.Ld.LdSendToy
import Cb.Ld.LdSumPackToy

set_option autoImplicit false

namespace Cb
namespace LdToy
open Iop Prob Hiop Blocks Cb.Ood

/-- the one entry of a row's message part -/
def plE5 : Unit ⊕ Empty ≃ Fin C5.msg where
  toFun _ := ⟨0, by rw [msg5]; exact Nat.one_pos⟩
  invFun _ := Sum.inl ()
  left_inv := by rintro (⟨⟩ | e) <;> [rfl; exact e.elim]
  right_inv := fun i => Fin.ext (by
    have h : i.val < 1 := i.2
    show 0 = i.val
    omega)

/-- The toy's standard oracle message. -/
@[reducible] def toyStd (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ]
    [DecidableEq μ] (plc : Dt → μ → Bool) : StdM K P5 where
  Cm := toyLd (Dt ⊕ Unit)
  Dt := Dt
  place := toyPlace (Dt ⊕ Unit)
  μ := μ
  plc := plc
  B := Bn
  b := fun β => β.1
  e := 2

end LdToy

namespace Spec
open LdToy Iop Prob Hiop Blocks Cb.Ood

def toyStd_ok : Prop :=
  ∀ (Dt μ : Type) [Fintype Dt] [DecidableEq Dt] [Fintype μ] [DecidableEq μ] (plc : Dt → μ → Bool),
    Function.Injective plc →
    (toyStd Dt μ plc).OK 2 1 ∧
    (toyStd Dt μ plc).Cm.Dist 4 ∧
    (toyStd Dt μ plc).Cm.Transparent ∧
    ¬ 2 * (toyStd Dt μ plc).e < 4

end Spec

open Iop Prob Hiop Blocks Cb.Ood

open LdToy in
theorem toyStd_ok : Spec.toyStd_ok := by
  intro Dt μ _ _ _ _ plc hp
  obtain ⟨hL, hD, -, hl, -, -, hz, ht, -⟩ := ld_toy (Dt ⊕ Unit)
  exact ⟨⟨hL, hl, hz, hp, fun _ _ h => Subtype.ext h, fun β => β.2⟩, hD, ht, by norm_num⟩

end Cb
