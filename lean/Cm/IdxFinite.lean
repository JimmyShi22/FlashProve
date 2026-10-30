-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cm/IdxFinite.lean: there are finitely many indices.

An index (`Idx`, Cm/RelBase.lean) is an integer matrix of a fixed shape, and well-formedness puts
every entry in [-128, 128). `coinBound` (ZKCP/CoinsFirst.lean) asks for a finite family of
algorithms; with this instance the committers at all indices are such a family.
This file imports Cm/RelBase.lean alone.

-/
import Cm.RelBase

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Cm

open Inst.Model.Layout (kRef hRef)

/-- Every entry of an index lies in [-128, 128). -/
theorem Idx.entry_bounds (i : Idx) (r : Fin hRef) (c : Fin (2 ^ kRef)) :
    -2 ^ 7 ≤ i.val r c ∧ i.val r c < 2 ^ 7 := by
  have h : -2 ^ 7 ≤ ext i.val r.val c.val ∧ ext i.val r.val c.val < 2 ^ 7 :=
    i.property.1 r.val r.isLt c.val c.isLt
  have e : ext i.val r.val c.val = i.val r c := dif_pos ⟨r.isLt, c.isLt⟩
  rw [e] at h
  exact h

/-- There are finitely many indices: an index is determined by its entries, each moved up by 128 to
a number below 256. -/
instance Idx.finite : Finite Idx :=
  Finite.of_injective
    (fun (i : Idx) (r : Fin hRef) (c : Fin (2 ^ kRef)) =>
      (⟨(i.val r c + 128).toNat, by have h := i.entry_bounds r c; omega⟩ : Fin 256))
    fun i j h => Subtype.ext (funext fun r => funext fun c => by
      have h1 := i.entry_bounds r c
      have h2 := j.entry_bounds r c
      have h3 : (i.val r c + 128).toNat = (j.val r c + 128).toNat :=
        congrArg Fin.val (congrFun (congrFun h r) c)
      omega)

end Cm
