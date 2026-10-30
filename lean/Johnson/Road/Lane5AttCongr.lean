-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Lane5AttCongr.lean

What the library's relation of an attention segment (Inst.Model.AttSeg.RFraw,
Inst/Model/Att/Trace.lean) reads of its table of scales and of its table functions. For all sizes.

* "rfraw_sh": of the table of scales it reads the shift of the first layer alone.
* "rfraw_exp": of the table functions it reads Exp at the rows below u0 alone.

It imports the library alone, and says nothing of a program.
-/
import Inst.Model.Att.Trace

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.L5

open Inst.Model (Scl Tables LayerScale)
open Inst.Model.AttSeg (Dim Raw RFraw lut keyVec castT)

/-- A table of scales that holds a shift and nothing else. -/
@[reducible] def sclSh (sh : ℕ) : Scl :=
  ⟨fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, ⟨0, 0, 0⟩, ⟨0, 0, 0⟩, 0, sh⟩, ⟨0, 0, 0⟩⟩

/-- The relation at a table of scales is the relation at the shift of that table's first layer. -/
theorem rfraw_sclSh (scl : Scl) (D : Dim) (tb : Tables) (F : Type) [CommRing F] (t : Raw → ℤ) :
    RFraw (scl := scl) D tb F t = RFraw (scl := sclSh (scl.κ 0).sh) D tb F t := rfl

/-- **Of the table of scales the relation reads the shift of the first layer alone.** -/
theorem rfraw_sh {scl scl' : Scl} (h : (scl.κ 0).sh = (scl'.κ 0).sh) (D : Dim) (tb : Tables)
    (F : Type) [CommRing F] (t : Raw → ℤ) :
    RFraw (scl := scl) D tb F t = RFraw (scl := scl') D tb F t :=
  (rfraw_sclSh scl D tb F t).trans
    ((congrArg (fun sh => RFraw (scl := sclSh sh) D tb F t) h).trans
      (rfraw_sclSh scl' D tb F t).symm)

section Exp
variable [scl : Scl] {D : Dim} {tb tb' : Tables}

/-- The number of rows of a call's table does not depend on the table functions. -/
theorem lut_rows_tb : ∀ c : Fin 4, (lut D tb c).rows = (lut D tb' c).rows
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

/-- A row of a call's table reads Exp at the rows below u0 alone. -/
theorem lut_row_tb (h : ∀ ι : ℕ, ι < D.u0 → tb.Exp ι = tb'.Exp ι) (ι : ℕ) :
    ∀ c : Fin 4, (lut D tb c).row ι = (lut D tb' c).row ι
  | 0 => rfl
  | 1 => by
    by_cases hι : ι < D.u0
    · simp only [lut, Inst.Model.tau2, if_pos hι, h ι hι]
    · simp only [lut, Inst.Model.tau2, if_neg hι]
  | 2 => rfl
  | 3 => rfl

/-- A key vector does not depend on the table functions. -/
theorem keyVec_tb {R : Type} [CommRing R] (u : Raw → R) (X : ℕ) :
    ∀ c : Fin 4, keyVec D tb u c X = keyVec D tb' u c X
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

/-- **Of the table functions the relation reads Exp at the rows below u0 alone.** -/
theorem rfraw_exp (h : ∀ ι : ℕ, ι < D.u0 → tb.Exp ι = tb'.Exp ι) {F : Type} [CommRing F]
    {t : Raw → ℤ} (H : RFraw D tb F t) : RFraw D tb' F t := by
  refine ⟨H.1, fun c X hX => ?_, H.2.2⟩
  obtain ⟨ι, hι, e⟩ := H.2.1 c X hX
  refine ⟨ι, ?_, ?_⟩
  · rw [← lut_rows_tb (tb := tb) (tb' := tb') c]
    exact hι
  · rw [← keyVec_tb (tb := tb) (tb' := tb'), ← lut_row_tb h ι c]
    exact e

end Exp

end OnBytes.Road.L5

#print axioms OnBytes.Road.L5.rfraw_sh
#print axioms OnBytes.Road.L5.rfraw_exp
