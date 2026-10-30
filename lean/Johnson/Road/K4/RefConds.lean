-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefConds.lean: THE CONDITIONS ON SIZES THAT THE VALUE OF
Johnson/Road/K4/ValueSlots.lean (`Plan4L`) CARRIES AS FIELDS, AT THE LIBRARY's REFERENCE SIZES
`Dim.ref`, kW := `kRef`, hW := `hRef`. One record's worth of small statements. So these fields can
be met together at these sizes.

WHICH ARE CLOSED NUMBERS (evaluations by Lean's kernel, or cited): h5: 9 ≤ lL + lF + lT (26) · h6:
9 ≤ lL - 1 + (lFe + lT) (24) · hfe: fe ≤ f · hf: f = 2 fe · hh: nq + nkv ≤ 64 (48) · hH: the
weights' units end within hRef rows (`units_total`, Inst/Model/LayoutSanity.lean) ·
`Dim.ChOK` is `ref_chOK` (Inst/Model/FF/Objects.lean).
WHICH HANG ON THE GROUP g, at L0 := g * 4: h0: L0 is even: for every g · hLay: L0 + nl ≤ layers: for
g < 12.
WHICH IS NOT A FACT ON SIZES: the condition that the theorems on the queries' and keys'
products ask beside `Dim.ChOK` (in each layer of the group the two scales kq and kk are equal, or
both at least 16) reads the section's table of scales. It is no closed number, and it is no open
debt: under the table that `sclOf` makes of a scale file that has passed the verifier's own tests,
at an admitted layout and a group of it, it is `hk_of_scalesHeld`
(Johnson/Road/FormsKeysRef.lean).

The sizes: see the head of Johnson/Road/K4/PubLinesRec.lean: `Dim.ref` has the sizes of the text
model of Llama 4 Maverick at a window of 1024 positions, in groups of four layers.

Limits. Numbers alone.
-/
import Johnson.Road.K4.ValueSlots
import Inst.Model.LayoutSanity

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Inst.Model (ppref)
open Inst.Model.Layout (kRef hRef off units)
open Inst.Model.FFSeg (Dim lF lFe)

theorem ref_h5 : 9 ≤ Dim.ref.lL + lF Dim.ref + Dim.ref.lT := by decide +kernel

theorem ref_h6 : 9 ≤ Dim.ref.lL - 1 + (lFe Dim.ref + Dim.ref.lT) := by decide +kernel

theorem ref_hfe : Dim.ref.fe ≤ Dim.ref.f := by decide +kernel

theorem ref_hf : Dim.ref.f = 2 * Dim.ref.fe := by decide +kernel

theorem ref_hh : Dim.ref.P.nq + Dim.ref.P.nkv ≤ 64 := by decide +kernel

theorem ref_nl : Dim.ref.nl = 4 := by decide +kernel

/-- The first layer of a group is even. -/
theorem ref_h0 (g : ℕ) : g * 4 % 2 = 0 := by omega

/-- The group's layers are the model's, for the twelve groups. -/
theorem ref_hLay {g : ℕ} (hg : g < 12) : g * 4 + Dim.ref.nl ≤ Dim.ref.P.layers := by
  have e : Dim.ref.P.layers = 48 := rfl
  rw [ref_nl, e]
  omega

/-- The weights' units end within the reference number of rows. -/
theorem ref_hH : off kRef (units Dim.ref.P) (units Dim.ref.P).length ≤ hRef := by
  have h := Inst.Model.Layout.Sanity.units_total
  show off kRef (units ppref) (units ppref).length ≤ hRef
  rw [h.1, h.2]
  decide

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ref_h5
#print axioms OnBytes.Road.K4.ref_h6
#print axioms OnBytes.Road.K4.ref_hLay
#print axioms OnBytes.Road.K4.ref_hH
