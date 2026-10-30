-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/LayerDict.lean: three fields of the record "a group of layers is in order", in the
names of Inst/Model/FF/Objects.lean.

Johnson/Road/Rows/LayerTop.lean cuts LayerOrd into five fields. The chain of a layers' sub-proof's
own rounds claims at its start that families of vectors on the cube of the positions vanish. This
file says that three of the fields are such claims, on the cells cellsOf DF (cellsAt y (castM Mz)):
 - NormField: the library's defects dJ of (J1) to (J9), by number k < 17 and norm ν < nNu;
 - HotField: the defects d10 of (J10), by routed layer;
 - EmbField: nothing in a group that is not the first.

Main theorems: normField_iff, hotField_iff, embField_later.

What is not claimed. That the cells which a chain reads off the committed messages are these cells;
that a chain claims these families. The program does not import this file.


-/
import Inst.Model.FF.Objects
import Johnson.Road.Rows.LayerTop

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows.Norms

open OnBytes.Model.Layer (Lay Scales)
open Inst.Model (Mat)
open Inst.Model.All (DF)
open Inst.Model.FFSeg (dJ d10)

variable (h : Model.Layer.Shape) (sc : Scales) (y : Lay) (g : ℕ) (Mz : Mats ℤ) (Wi : Mat)
  (x : Cm.Seg.XI)

/-- The identities (J1) to (J9) at every valid name: all defects dJ vanish on the cube of the
positions. -/
theorem normField_iff : NormField h sc y g Mz Wi x ↔
    ∀ k ν, k < 17 → ν < DF.nNu → ∀ i, i < 2 ^ DF.lT →
      dJ (scl := sclOf h sc g 4) DF (cellsOf DF (cellsAt y (castM Mz))) k ν i = 0 :=
  ⟨fun H k ν hk hν i hi => H k ν i ⟨hk, hν, hi⟩, fun H k ν i hv => H k ν hv.1 hv.2.1 i hv.2.2⟩

/-- The identity (J10) at every valid name: all defects d10 vanish on the cube of the positions. -/
theorem hotField_iff : HotField h sc y g Mz Wi x ↔
    ∀ l, l < DF.ne → ∀ i, i < 2 ^ DF.lT →
      d10 DF (cellsOf DF (cellsAt y (castM Mz))) l i = 0 :=
  ⟨fun H l hl i hi => H l i ⟨hl, hi⟩, fun H l i hv => H l hv.1 i hv.2⟩

/-- In a group that is not the first no name of (J11) is valid. -/
theorem embField_later (hg : g ≠ 0) : EmbField h sc y g Mz Wi x := fun _ _ hv =>
  absurd (of_decide_eq_true hv.1) hg

end OnBytes.Road.Rows.Norms
