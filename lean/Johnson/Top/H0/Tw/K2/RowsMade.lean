-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/RowsMade.lean: the kind «the code switch»: THE NEW GROUP's ROWS, OR NOTHING:
K2/RowsCan.lean's eight clauses [G33], and where they hold what the maker swRows makes
(Johnson/Desc/Own/SwitchRows.lean: the program's switchRows taken over token for token). It has that
maker's arguments and result type, so that a text which matches on
it can match on rowsMade instead: whether there are rows is then decided by the eight clauses, in
the description's own text, and by nothing else.
  rowsMade          if rowsCan … then some (what swRows makes) else none
  rowsMade_none     rowsMade … = none ⇔ a clause fails
WHO CALLS IT: Johnson/Top/H0/Tw/L9/Switch.lean, a second form of the switch's text that another
kind's law unfolds; K2/Switch.lean asks rowsCan and takes swRows' value in its own lines.
PROVED BESIDE, IN K2/RowsMadeAgree.lean, which no block imports: rowsMade … = some rows ⇒ the
clauses hold and the program's switchRows … = some rows (rowsMade_some); switchRows returns nothing
wherever a clause fails: so rowsMade … = switchRows … at every input (rowsMade_eq).
No soundness: a definition with code and one small theorem.
-/
import Johnson.Top.H0.Tw.K2.RowsCan
import Johnson.Desc.Own.SwitchRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

/-- The rows, where the eight clauses hold. -/
def rowsMade (S : Statement) (old : SingleRows) (T : SwitchTarget) (g : Nat) (anew : Array Nat) (pos
    : Positions) (y : Array E) : Option (List Row) :=
  if rowsCan S old T anew pos y then
      some ((VerifiableInference.Desc.Own.swRows S old T g anew pos y).getD []) else none

theorem rowsMade_none {S : Statement} {old : SingleRows} {T : SwitchTarget} {g : Nat} {anew : Array
    Nat} {pos : Positions} {y : Array E} :
    rowsMade S old T g anew pos y = none ↔ rowsCan S old T anew pos y = false := by
  unfold rowsMade
  cases rowsCan S old T anew pos y <;> simp

end Tw.K2

#print axioms Tw.K2.rowsMade_none
