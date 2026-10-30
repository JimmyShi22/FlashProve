-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/TabsBack.lean: kind K5's records of a table and of a segment's tables
(Att/TablesP.lean) as the records that the first chain's state and the smallness test's list hold,
field by field: no test, no arithmetic.

`funBack`: a table. `tabsBack`: all tables of a segment.
The state's field and the smallness test's list still have the types of OnBytes/Model's records
(HFun; Attention.Tables).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.TablesP
import OnBytes.Model.AttentionTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Model

/-- A table of the kind's own list as the smallness test's record of a table. -/
def funBack (f : P.Fun1) : HFun := { mat := f.mat, len := f.len, phi := f.phi, tree := f.tree, start := f.start }

/-- The kind's record of tables as the state's, field by field. -/
def tabsBack (t : P.TablesP) : Attention.Tables :=
  { ptM := t.ptM, ptD := t.ptD, tA := t.tA, tVM := t.tVM, tVD := t.tVD
    score := t.score.map fun s => { tM := s.tM, tQ := s.tQ, tK := s.tK }
    hW := t.hW, hX := t.hX, hE := t.hE, hT := t.hT, hPi := t.hPi, hR2 := t.hR2, tO := t.tO
    qO := t.qO, qVM := t.qVM, qVD := t.qVD, qF := t.qF, qKx := t.qKx
    tBit0 := t.tBit0, tBit1 := t.tBit1, tPin := t.tPin, tabLen := t.tabLen, funs := t.funs.map funBack }

end VerifiableInference.Desc.First.Att
