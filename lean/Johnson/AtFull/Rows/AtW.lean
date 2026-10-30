-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/AtW.lean: THE CLOSED TERMS OF THE WALK AT rowsW's FOUR WRITTEN
VALUES (Johnson/LPFE1R/RowsAtWritten.lean). Definitions alone. A law file; no running text imports
it.
  `cW`, `sW`      what the planner configured, written; its setting.
  `kW i`, `prW i`  the key's and the proof's i-th written plan (an empty plan beyond the list).
  `piecesW`       the pieces of «proof 0» at the written arms.
  `placesW`, `tabW`   the table of the states between these pieces.
Limits. Nothing is proved here.
-/
import Johnson.AtFull.Rows.Parts
import Johnson.LPFE1R.RowsAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom
open Johnson.G.MadeFree (Hung)
open VerifiableInference.PlanWritten.Joined (writtenMade)

def cW : Configured := writtenMade.at Hung.none
def sW : Setting := cW.sized.set
def kW (i : Nat) : Planned := cW.key.getD i ⟨sW, []⟩
def prW (i : Nat) : Planned := cW.proof.getD i ⟨sW, []⟩

/-- The pieces of «proof 0» at the written arms. -/
def piecesW : List (N Unit) := proof0Pieces cW (List.replicate 25 1) 13 armAtW

/-- The places in the written rounds of «proof 0» at which its pieces begin, and the end. WHENCE: an
evaluator's print of the walk (a sheet for the evaluator, which is not in this repository), pasted
by program. Each is held by the kernel in the piece's own closed fact. -/
def placesW : List Nat :=
  [0, 1980, 3859, 5837, 7716, 9694, 11573, 13551, 15430, 17408, 19287, 21265, 23144, 25122, 27001,
      28979, 30858, 32836, 34715, 36693, 38572, 40550, 42429, 44407, 46286, 48235, 48270, 48293]

/-- The states between the pieces of «proof 0»: each joint stands at the request's scope and
counters 0. -/
def tabW (i : Nat) : SmallSt × Nat := (⟨.request, 0, 0, 0⟩, placesW.getD i 0)

end VerifiableInference.Desc.LinkJoin
