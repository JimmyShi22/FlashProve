-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/EndUnitWeight.lean: the row weights of the first virtual row of a table's
vector, where the routine that sets the row weights returns (`HTailF2.coefficientsF`,
OnBytes/Model/Tail.lean): 1 on the array's one row, 0 elsewhere. The batching element does not occur
in them.

Theorems with their proofs, in the words of OnBytes/Tie/Pv/Led/LedPort.lean (`rowWeight`).

Main names:
  `unitW`: the weights: 1 at 0, else 0.
  `rowWeight_unit`: where coefficientsF returns from F to G, `rowWeight ρ G.trees tU 0 = unitW`, for
    a table's vector tU whose number is another than those of the other arrays (`UApart`,
    OnBytes/Tie/Pv/Tail/EndCoef.lean).
  `rowWeight_unit_tested`: the same where the verifier's test of the weights has run after it on a
    view and the vector has its shape (`UShape`, OnBytes/Tie/Pv/Tail/EndFrame.lean).

Limits: the first virtual row alone; a table's vector has no other (`UShape`). Nothing on the rows
of the arrays of the digits, of the planes and of the symbols.


-/
import OnBytes.Tie.Pv.Tail.EndFrame
import OnBytes.Tie.Pv.Tail.EndPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port OnBytes.Road.Rows

variable {K : Type} [Field K] (ρ : Reading K)

/-- The weights of a row that reads the array's first row alone: 1 at 0, else 0. -/
def unitW (i : Nat) : K := if i = 0 then 1 else 0

/-- Where the routine returns, the first virtual row of a table's vector has the weights
1, 0, 0, … -/
theorem rowWeight_unit (tl : HTailF2) (n0 tU : Nat) (F G : Fork) (c c' : Ctx)
    (A : UApart tl n0 tU F) (h : tl.coefficientsF F c = .ok (((), G), c')) :
    rowWeight ρ G.trees tU 0 = unitW := by
  funext i
  rw [rowWeight_eq]
  have e := coefficientsF_unit tl n0 tU F G c c' A h
  unfold coefAt at e
  rw [e]
  unfold unitW
  cases i with
  | zero => simpa using ρ.one
  | succ j => simpa using ρ.zero

/-- The same from the verifier's own test of the weights and the vector's shape. -/
theorem rowWeight_unit_tested (tl : HTailF2) (n0 tU cols : Nat) (F G G' : Fork)
    (c c' c2 c2' : Ctx) (hn : n0 < 4) (hU : tl.ix.U.getD n0 none = some tU)
    (hs : UShape G tU cols) (h : tl.coefficientsF F c = .ok (((), G), c'))
    (hd : c2.ch.dry = false) (h2 : tl.tileSelfTestF G c2 = .ok (((), G'), c2')) :
    rowWeight ρ G.trees tU 0 = unitW :=
  rowWeight_unit ρ tl n0 tU F G c c'
    (uApart_tested tl n0 tU cols F G G' c c' c2 c2' hn hU hs h hd h2) h

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.rowWeight_unit
#print axioms OnBytes.Tie.Pv.Tail.rowWeight_unit_tested
