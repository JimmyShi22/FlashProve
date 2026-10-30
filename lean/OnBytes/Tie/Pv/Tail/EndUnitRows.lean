-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndUnitRows.lean: the row weights of every virtual row of a table's vector,
where the routine that sets the row weights returns (`HTailF2.coefficientsF`,
OnBytes/Model/Tail.lean). The batching element occurs in none of them.

Theorems with their proofs, in the words of OnBytes/Tie/Pv/Led/LedPort.lean (`rowWeight`). A table's
vector has one virtual row (`UShape`, OnBytes/Tie/Pv/Tail/EndFrame.lean). For its number 0
OnBytes/Tie/Pv/Tail/EndUnitWeight.lean has the weights. `rowWeight` at a number from 1 on reads a
row that is not there, and so the weight 0.

Main names:
  `rowWeight_none`: at a number from 1 on the weights are 0.
  `unitRows r`: the weights by the virtual row's number: `unitW` at 0, else 0.
  `rowWeight_rows`: where coefficientsF returns from F to G and the verifier's test of the weights
    has run after it on a view: `rowWeight ρ G.trees tU r = unitRows r` for every r.

Limits: a table's vector alone.


-/
import OnBytes.Tie.Pv.Tail.EndUnitWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows

variable {K : Type} [Field K] (ρ : Reading K)

/-- At a number from 1 on, a table's vector has no virtual row: the weights are read as 0. -/
theorem rowWeight_none (G : Fork) (tU cols r : Nat) (hs : UShape G tU cols) (hr : 1 ≤ r) :
    rowWeight ρ G.trees tU r = fun _ => 0 := by
  funext i
  rw [rowWeight_eq]
  have e : (G.trees.getD tU {}).rows.size = 1 := congrArg (·.2.2.2) hs.shape
  have e2 : (G.trees.getD tU {}).rows.getD r {} = {} :=
    getD_out (G.trees.getD tU {}).rows r {} (by omega)
  rw [e2]
  simpa using ρ.zero

/-- The weights by the virtual row's number. -/
def unitRows (r : Nat) : Nat → K := if r = 0 then unitW else fun _ => 0

/-- The weights of every virtual row of a table's vector. -/
theorem rowWeight_rows (tl : HTailF2) (n0 tU cols : Nat) (F G G' : Fork) (c c' c2 c2' : Ctx)
    (hn : n0 < 4) (hU : tl.ix.U.getD n0 none = some tU) (hs : UShape G tU cols)
    (h : tl.coefficientsF F c = .ok (((), G), c')) (hd : c2.ch.dry = false)
    (h2 : tl.tileSelfTestF G c2 = .ok (((), G'), c2')) (r : Nat) :
    rowWeight ρ G.trees tU r = unitRows r := by
  unfold unitRows
  by_cases hr : r = 0
  · rw [if_pos hr, hr]
    exact rowWeight_unit_tested ρ tl n0 tU cols F G G' c c' c2 c2' hn hU hs h hd h2
  · rw [if_neg hr]
    exact rowWeight_none ρ G tU cols r hs (Nat.one_le_iff_ne_zero.2 hr)

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rowWeight_none
#print axioms OnBytes.Tie.Pv.Tail.rowWeight_rows
