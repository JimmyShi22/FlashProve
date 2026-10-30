-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/MarksOfTile.lean: THE SMALLNESS TEST: "NO READ IS MARKED TWICE, ALL MARKS ARE
SET, AND THE READS ARE AS MANY AS THE TABLES' SEGMENTS" FOLLOW FROM "THE TABLES TILE". ONE
STATEMENT, as a definition of a proposition; no proof stands here. A lemma; none of the library's
goals.

What it is for. Of the seventeen premises of `TailReady`
(Johnson/Desc/K8/Honest/EqTailReturns.lean) three speak of the marks that the reads lay, one by one,
into arrays as long as the vectors' parts that hold tables: `marks`, `allSet`, `count`. A test
that is to stand for them lays all these marks: it is expected to be dear at the full size; it has
not been measured. The statement says that they follow from three others, which read the list of
tables alone (`inList`, `tile1`, `tile3`), and one number.

  `Spec.marks_of_tile`   every table lies on a matrix of the list and on vector 0 or 2; the tables
                         on vector 0 tile its part, with s1 segments; those on vector 2 theirs, with
                         s3; there are at most two parts: THEN the marks behind all reads are there
                         (no read refuses), every mark is set, and the list of reads has s1 + s3
                         members.

Why at most two parts. `noMarks` has a list of marks for each entry of `tabLen`; the reads mark
parts 0 and 1 alone: a third part with an entry would keep its marks unset. The premise is enough,
not needed: further parts that are empty do no harm.
Of the premise on the list of tables the half "on vector 0 or 2" is not needed either: neither the
tiling test nor the list of reads sees a table on another vector. It stands as `TailReady` has it.
Limits. Nothing says that the tables tile at any state of a run. The statement goes one way.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (readsList)

namespace Spec

/-- States: where the tables tile, no read is marked twice, all marks are set, and the reads are as
many as the tables' segments. -/
def marks_of_tile : Prop :=
  ∀ (tl : HTailF2) (funs : Array HFun) (s1 s3 : Nat),
    (funs.all fun Fn => decide (Fn.mat < tl.NM) && (Fn.tree == 0 || Fn.tree == 2)) = true →
    tl.tablesTile funs 0 = some s1 → tl.tablesTile funs 2 = some s3 → tl.tabLen.size ≤ 2 →
    ∃ rd, marksOf tl funs = some rd ∧ (rd.all fun a => a.all id) = true ∧
      (readsList tl funs).length = s1 + s3

end Spec

end VerifiableInference.Desc.First.K8.Honest
