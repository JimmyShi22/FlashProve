-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPlaces.lean: where the 21 tables of an attention sub-proof begin in the vector
of tables, by the tables' library-side names.

The dictionary LateAt (Johnson/Road/Rows/AttEntRow.lean) says at which entry of the vector of tables
the late entry of a name lies: where the name's table begins, plus the name's place in the table.
The places are in Johnson/Road/Rows/AttPortLate.lean (placeAtt). This file has the beginnings, from
the verifier's own record of its tables (Tables in OnBytes/Model/AttentionHeard.lean).

Main definitions: tabOfAtt h: the beginning of each table. The unit of the scores below the diagonal
is taken to be number 0 of the verifier's list of units, the unit on the diagonal number 1.
Main theorems: lateTabs_att, firstTabs_att: the premises LateTabs and FirstTabs hold of tabOfAtt, by
definition.

What is not claimed. That the units stand in this order in a run: it is tried at the small
configuration alone, in Johnson/Road/Rows/TestAttPlaces.lean. That names of
different late entries have different places is tried there too, and is not proved.


-/
import Johnson.Road.Rows.AttPortFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Attention (Heard)
open Cb.Pv.Att.End (AttTab)

/-- Where each table begins. -/
def tabOfAtt (h : Heard) : AttTab → ℕ
  | .tA => h.t.tA
  | .tVM => h.t.tVM
  | .tVD => h.t.tVD
  | .tMm => (h.t.score.getD 0 default).tM
  | .tQm => (h.t.score.getD 0 default).tQ
  | .tKm => (h.t.score.getD 0 default).tK
  | .tMd => (h.t.score.getD 1 default).tM
  | .tQd => (h.t.score.getD 1 default).tQ
  | .tKd => (h.t.score.getD 1 default).tK
  | .hW => h.t.hW
  | .hX => h.t.hX
  | .hE => h.t.hE
  | .hT => h.t.hT
  | .hPi => h.t.hPi
  | .hR2 => h.t.hR2
  | .tO => h.t.tO
  | .qO => h.t.qO
  | .qVM => h.t.qVM
  | .qVD => h.t.qVD
  | .qF => h.t.qF
  | .qKx => h.t.qKx

theorem lateTabs_att (h : Heard) : LateTabs h (tabOfAtt h) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem firstTabs_att (h : Heard) :
    FirstTabs h (h.t.score.getD 0 default) (h.t.score.getD 1 default) (tabOfAtt h) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end OnBytes.Road.Rows
