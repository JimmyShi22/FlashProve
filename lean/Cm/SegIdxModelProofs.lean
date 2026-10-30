-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/SegIdxModelProofs.lean: lemmas on units, widths and logarithms for the weight tensors of the
model as index atoms (Cm/TargetSegIdxModel.lean).

All statements are at one fixed set of parameters: the reference sizes `ppref`
(Inst/Model/Program.lean), `kRef` column bits (Inst/Model/Layout.lean).

Notation: `UnitS` (Inst/Model/Layout.lean): a structure:
`coords : List Coord`, `nU : ℕ`; `Kind` (Inst/Model/Layout.lean): "for each coordinate one of three
kinds: low, high, whole"; `Src` (Cm/SegIdx.lean): where a bit comes from: a variable of the cube,
the negation of a variable, or a constant.
Terms: lean/GLOSSARY.md.
-/
import Cm.SegIdxModel
import Cm.SegIdxTensorProofs
import Cm.IndexRefProofs

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Cm
open Cb Blocks Finset Code Inst.Model Inst.Model.Layout

theorem widths2 {R₁ R₂ : ℕ} {k₁ k₂ : Kind} {σ₁ σ₂ : List Src} (h₁ : k₁ ≠ .whole) (h₂ : k₂ ≠ .whole)
    (p₁ : 0 < R₁) (p₂ : 0 < R₂) (l₁ : R₁ ≤ 2 ^ σ₁.length) (l₂ : R₂ ≤ 2 ^ σ₂.length) :
    WidthsOK [⟨R₁, k₁⟩, ⟨R₂, k₂⟩] [σ₁, σ₂] :=
  ⟨⟨p₁, l₁, fun h => absurd h h₁⟩, ⟨p₂, l₂, fun h => absurd h h₂⟩, trivial⟩

theorem widths3 {R₁ R₂ R₃ : ℕ} {k₁ k₂ k₃ : Kind} {σ₁ σ₂ σ₃ : List Src} (h₁ : k₁ ≠ .whole)
    (h₂ : k₂ ≠ .whole) (h₃ : k₃ ≠ .whole) (p₁ : 0 < R₁) (p₂ : 0 < R₂) (p₃ : 0 < R₃)
    (l₁ : R₁ ≤ 2 ^ σ₁.length) (l₂ : R₂ ≤ 2 ^ σ₂.length) (l₃ : R₃ ≤ 2 ^ σ₃.length) :
    WidthsOK [⟨R₁, k₁⟩, ⟨R₂, k₂⟩, ⟨R₃, k₃⟩] [σ₁, σ₂, σ₃] :=
  ⟨⟨p₁, l₁, fun h => absurd h h₁⟩, ⟨p₂, l₂, fun h => absurd h h₂⟩,
    ⟨p₃, l₃, fun h => absurd h h₃⟩, trivial⟩

/-! ### The units of a layer -/

theorem unitL {L m : ℕ} {U : UnitS} (hL : L < 48) (hU : (layerUnits ppref L)[m]? = some U) :
    (units ppref)[first ppref L + m]? = some U :=
  Bridge.unit_at ppref hL hU

theorem fOf_pos (L : ℕ) : 0 < fOf L := by
  unfold fOf
  split_ifs <;> decide

theorem unit_g {L : ℕ} (hL : L < 48) :
    (units ppref)[first ppref L + 3]? = some (uGU ppref (fOf L)) := by
  refine unitL hL ?_
  unfold fOf layerUnits
  split_ifs <;> rfl

theorem unit_u {L : ℕ} (hL : L < 48) :
    (units ppref)[first ppref L + 4]? = some (uGU ppref (fOf L)) := by
  refine unitL hL ?_
  unfold fOf layerUnits
  split_ifs <;> rfl

theorem unit_d {L : ℕ} (hL : L < 48) :
    (units ppref)[first ppref L + (if hasExperts L then 7 else 5)]? = some (uD ppref (fOf L)) := by
  refine unitL hL ?_
  unfold fOf layerUnits
  split_ifs <;> rfl

theorem unit_x {L m : ℕ} {U : UnitS} (hL : L < 48) (hx : hasExperts L)
    (hU : ([uQK ppref, uV ppref, uO ppref] ++
        [uGU ppref ppref.fe, uGU ppref ppref.fe, uGUr ppref, uGUr ppref, uD ppref ppref.fe,
          uDr ppref, uR ppref])[m]? = some U) :
    (units ppref)[first ppref L + m]? = some U := by
  refine unitL hL ?_
  unfold layerUnits
  rw [if_pos hx]
  exact hU

/-! ### Coordinates of kind whole -/

theorem clog64 : Nat.clog 2 64 = 6 := by decide +kernel
theorem clog128 : Nat.clog 2 128 = 7 := by decide +kernel
theorem clogV : Nat.clog 2 202048 = 18 := by decide +kernel

theorem widthsQK {σx σj : List Src} (hx : σx.length = 13) (hj : 5120 ≤ 2 ^ σj.length) :
    WidthsOK (uQK ppref).coords [σx.take 6, σx.drop 6, σj] := by
  have h6 : (σx.take 6).length = 6 := by rw [List.length_take, hx]; rfl
  have h7 : (σx.drop 6).length = 7 := by rw [List.length_drop, hx]
  exact ⟨⟨by decide, by rw [h6]; decide, fun _ => h6.trans clog64.symm⟩,
    ⟨by decide, by rw [h7]; decide, fun _ => h7.trans clog128.symm⟩,
    ⟨by decide, hj, fun h => by cases h⟩,
    trivial⟩

theorem widthsTok {k : Kind} (hk : k ≠ .whole) {σt σj : List Src}
    (ht : σt.length = 18) (hj : 5120 ≤ 2 ^ σj.length) :
    WidthsOK [⟨ppref.V, .whole⟩, ⟨ppref.d, k⟩] [σt, σj] :=
  ⟨⟨by decide, by rw [ht]; decide, fun _ => ht.trans clogV.symm⟩,
    ⟨(by decide : 0 < ppref.d), hj, fun h => absurd h hk⟩,
    trivial⟩

end Cm
