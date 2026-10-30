-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H0/Tw/K2/RowsCan.lean: the kind «the code switch»: [G33] IN THE KIND's OWN TEXT: THE
CONDITIONS UNDER WHICH THE NEW GROUP's ROWS CAN BE MADE. The rows themselves (the old claim carried
over · the kept members' old sample rows · for each draw the generator rows) are made by the
maker swRows (Johnson/Desc/Own/SwitchRows.lean: the program's switchRows, OnBytes/Iop/Cs.lean, taken
over token for token), called by name in K2/Switch.lean. That maker can return nothing. HERE STANDS,
CLAUSE BY CLAUSE AND IN PLAIN WORDS, ALL THAT IT WANTS; the block asks these clauses IN FRONT of it,
and rowsCan_some | rowsCan_someOwn (K2/RowsMadeAgree.lean, which no block imports) prove: WHERE THEY
HOLD THE MAKER RETURNS ROWS.
So no refusal of the block hangs on the maker.
  the symbols     there is one symbol for each row of the old complex at each position of the list
  the codes       the old main code, the old mask code and g's main code are in the statement's
  lists
  the kept        there is one new message for each kept member · the old claim reads no kept member
  that the group does not have · each kept member's old sample rows read that member's main table
  and nothing else
  the draws       each draw is among the positions of the list
No soundness: definitions with code; no theorem. What a yes means, as a proposition:
K2/RowsCanMeans.lean.
-/
import OnBytes.Iop.Cs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Tw.K2
open OnBytes

/-- The row reads the main table of the message o and nothing else. -/
def readsMainOf (o : Nat) (row : Row) : Bool :=
  (row.terms.all fun t => t.oracle == o && t.part == .main) &&
    (row.units.all fun u => u.oracle == o && u.part == .main) &&
    (row.runs.all fun r => r.oracle == o && r.part == .main) &&
    row.forms.all fun f => f.oracle == o

/-- [G33], clause by clause. -/
def rowsCanL (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos :
    Positions) (y : Array E) : List (String × Bool) :=
  [("there is one symbol for each row at each position", y.size == pos.all.size * old.rows),
   ("the old main code is in the list", decide (old.code < S.codes.base.size)),
   ("the old mask code is in the list", decide (old.maskCode < S.codes.mask.size)),
   ("g's main code is in the list", decide (T.shape.code < S.codes.base.size)),
   ("there is a new message for each kept member", anew.size == (switchKept old).size),
   ("the old claim reads kept members alone",
     old.kept.toList.all fun f => (List.range (switchKept old).size).any fun i =>
         (switchKept old).getD i noId == f.oracle),
   ("each kept member's old sample rows read its main table alone",
     (List.range (switchKept old).size).all fun i =>
       (S.oracles.getD ((switchKept old).getD i noId) default).sampleRows.toList.all (readsMainOf
           ((switchKept old).getD i noId))),
   ("each draw is among the positions", pos.draws.toList.all fun x => (pos.all.idxOf? x).isSome)]

/-- [G33] All clauses hold. -/
def rowsCan (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos :
    Positions) (y : Array E) : Bool :=
  (rowsCanL S old T anew pos y).all (·.2)

/-- The first clause that fails. -/
def rowsWhy (S : Statement) (old : SingleRows) (T : SwitchTarget) (anew : Array Nat) (pos :
    Positions) (y : Array E) : String :=
  (((rowsCanL S old T anew pos y).find? fun c => !c.2).map (·.1)).getD "no clause fails"

end Tw.K2
