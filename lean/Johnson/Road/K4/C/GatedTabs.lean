-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/GatedTabs.lean: CONDITIONAL.

Not shown here. THAT A TENSOR's CELLS READ AS THE LIBRARY's VALUES (TensorIs): a hypothesis;
C/GatedCells.lean has it from the ties of Fits, CellsAre and public facts. That the honest side's
functions return the tables: a hypothesis. No example is known. Nothing on soundness, on
completeness or on any other property. No property is claimed.

The entries of the two gated products' tables, as the honest side makes them (`gatedTabs`,
`gatedTabs2`, Johnson/Desc/K4/Honest/Gated.lean), read into the field, are the library's four
vectors slV, upV, slV', upV' (Inst/Model/FF/Objects.lean) below the tables' sizes: `tab1_read` and
`tab2_read` (C/Gated.lean) at the tables that are returned.

  `tabs1_are`   the first gated product's two tables.
  `tabs2_are`   the second's.
-/
import Johnson.Road.K4.C.Gated

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.C
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (Ten)
open Inst.Model.FFSeg (Dim Cell lF lFe slV upV slV' upV')
open OnBytes.Desc.First.K4.Honest

variable {Q : K4Pub} {w : K4In} {D : Dim} {t : Cell → Cb.Gl.E} {ts tu : Ten}

/-- **The first gated product's tables.** CONDITIONAL: on every hypothesis named. -/
theorem tabs1_are (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    {tb : Tab × Tab} (htb : gatedTabs Q w = some tb) {X : ℕ}
    (hX : X < 2 ^ (D.lL + lF D + D.lT)) :
    Reading.gl.val (tb.1.getD X zeroE) = slV D t X ∧
      Reading.gl.val (tb.2.getD X zeroE) = upV D t X := by
  rw [gatedTabs_eq hts htu htb]
  exact ⟨tab1_read N Ss hX, tab1_read N Su hX⟩

/-- **The second gated product's tables.** CONDITIONAL: on every hypothesis named. -/
theorem tabs2_are (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    {tb : Tab × Tab} (htb : gatedTabs2 Q w = some tb) {X : ℕ}
    (hX : X < 2 ^ (D.lL - 1 + lFe D + D.lT)) :
    Reading.gl.val (tb.1.getD X zeroE) = slV' D t X ∧
      Reading.gl.val (tb.2.getD X zeroE) = upV' D t X := by
  rw [gatedTabs2_eq hts htu htb]
  exact ⟨tab2_read N Ss hX, tab2_read N Su hX⟩

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.tabs1_are
#print axioms OnBytes.Road.K4.C.tabs2_are
