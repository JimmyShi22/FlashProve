-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/Cond.lean: THE SMALLNESS TEST: THE TWO READINGS OF THE CARRIED RECORD THAT ITS
ROW OF THE TABLE OF JOINTS SPENDS IN FRONT OF THE DRAW, AND EACH AS A TEST WITH CODE. DEFINITIONS.
NO THEOREM HERE. NO SOUNDNESS IS CLAIMED.

  `seven tl`, `lay7 s`: seven fields of the smallness test's record in s: the symbol arrays'
    numbers, the arrays' index, the digits' two numbers of columns; the number of matrices, the
    shapes, the matrices.
  `onThird s`: whether every table of its list lies on the third vector of reads.
  `lay7B tlP s`: A TEST: a link is open in s, and the seven fields are those of tlP: meant: the
    segment's planned record.
  `closedNow s`: whether that list is closed.
  `onThirdB s`: A TEST: a link is open in s, THE LIST IS CLOSED, and `onThird` says yes. (Without
    "closed" the test would say an idle yes from the link's opening on: the plan's list is
    empty.)
What the two give is Johnson/Desc/First/K8/LawCondAtt.lean's `cond_of_readings` and `cond_of_tests`.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- The seven fields that the two conditions read. -/
def seven (tl : HTailF2) :=
  (tl.gtTree, tl.ix, tl.mz, tl.off, tl.NM, tl.shp, tl.mats)

/-- They, of the smallness test's record in the carried record. -/
def lay7 (s : S) := s.tl?.map seven

/-- Whether every table of the list lies on the third vector of reads. -/
def onThird (s : S) : Option Bool := s.tl?.map fun tl => tl.funs.toList.all fun Fn => Fn.tree == 2

/-- The first as a test. -/
def lay7B (tlP : HTailF2) (s : S) : Bool :=
  match s.tl? with
  | none => false
  | some tl =>
    decide (tl.gtTree = tlP.gtTree) && decide (tl.ix = tlP.ix) && decide (tl.mz = tlP.mz) &&
      decide (tl.off = tlP.off) && decide (tl.NM = tlP.NM) && decide (tl.shp = tlP.shp) &&
      decide (tl.mats = tlP.mats)

/-- Whether the list of tables is closed. -/
def closedNow (s : S) : Option Bool := s.tl?.map fun tl => tl.funClosed

/-- The second as a test: with "the list is closed": in front of the step that closes the list the
list is the plan's, which is empty, and `onThird` alone says an idle yes. -/
def onThirdB (s : S) : Bool := onThird s == some true && closedNow s == some true

end VerifiableInference.Desc.First.K8.Ready
