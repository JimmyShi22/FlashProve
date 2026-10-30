-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookLinear/Eleventh.lean: WHERE THE NAMES OF A LIST OF ENTRIES ARE ALL
DIFFERENT, THE ELEVENTH TEST OF ProverCoinCounts.clauses (Honest/Frame.lean: "two entries bear one name")
ACCEPTS THE LIST (clause11_of_nodup). One statement with its proof; no definition. Written by the
authors of the honest side of the linear claim's shared rounds (K14), in the frame's folder, not by
the frame's authors; Ahead and the test are the frame's (Honest/Frame.lean).

  clause11_of_nodup   **(l.map (·.name)).Nodup → the eleventh test's Bool at l is true**: THE
                  CONCLUSION IS THE TEST's Bool AS IT STANDS IN ProverCoinCounts.clauses, with the list as a
                  letter: at l := B.ahead it is the eleventh premise of clauses_all_of_each
                  (Honest/BookWordOf.lean), to the letter. one_each (Honest/BookLinear/Tool.lean) at
                  the entries' names

Who spends it: clause11_of_keys (Honest/BookLinear/NameKeys.lean), which has "the names are all
different" without opening a name: from what each name is made of.

Kin. Beside clause11_of_keys no law that concludes the eleventh test, and none that draws it out of
a book's return, was found in the frame's files or this kind's. For the other direction the frame
has the step nodup_of_count (Honest/Law/Rule/Tests.lean): "A list in which every member counts once
has no member twice". The sister law at the second test, by the same one_each: clause2_of_nodup
(Honest/BookRawRows.lean, by authors of this kind); it concludes in another form: the list's member
number 1 is "some true". The frame says what the test is for at Honest/ForKinds.lean's head ("no two
entries of a book bear one name"), and has a toy at which it rejects (Honest/FrameToy.lean).

Limits. An implication: that the names of any list are all different is not shown here. No book is
named. Nothing on what an evaluation costs. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.BookLinear.Tool

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **Where the names are all different, the eleventh test of `ProverCoinCounts.clauses` accepts.** -/
theorem clause11_of_nodup {l : List Ahead} (h : (l.map (·.name)).Nodup) :
    (l.all fun a => (l.filter fun b => b.name == a.name).length == 1) = true :=
  one_each (·.name) l h

end ProofFile.Honest

#print axioms ProofFile.Honest.clause11_of_nodup
