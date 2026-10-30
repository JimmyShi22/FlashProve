-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/EntryRunIsOfList.lean: NO KIND IS NAMED. By the writers of the
merge of the claims on the weights (sub-protocol K11). THE PUBLIC TEST `entryRunIs` (EntryRunIs.lean
of this folder) SAYS YES WHERE THE LIST OF THE ENTRIES' OWNERS, STARTS AND COUNTS HAS THE THREE AT
THAT POSITION. One lemma with its proof, and its form at a written list; no definition; none of the
library's goals. PUBLIC DATA ALONE: a list of a book's entries, numbers.

  `entryRunIs_of_map`   where member number i of the list of triples (owner, start, count) of es is
                        (o, st, ct): the test says yes at es, i, o, st, ct
  `entryRunIs_of_list`  the same from an equation of that whole list with a list L, and L's member
                        number i

Why. A closed fact on what a part spends in a book is had as an equation of lists of such triples;
the laws on a part's lots take the test. This is the step between the two.

WHAT IT IS NOT. That any list of entries has given triples is not said here. The entries' names and
spenders are not read. NEAR. `entryRunIs_of_oneStretch`, `entryRunIs_of_row`
(Honest/BookStretchEntry.lean, which imports EntryRunIs.lean of this folder as this file does; this
library may not hold it): two more roads to the same yes, from the test `oneStretch` at a row of one
entry.

Limits. An unfolding. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.EntryRunIs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest

/-- **From the triple at a position to the test's yes.** -/
theorem entryRunIs_of_map {es : List Ahead} {i : Nat} {o : Addr} {st ct : Due}
    (h : (es.map fun e => (e.owner, e.start, e.count))[i]? = some (o, st, ct)) :
    entryRunIs es i o st ct = true := by
  rw [List.getElem?_map] at h
  obtain ⟨e, he, hx⟩ := Option.map_eq_some_iff.1 h
  have h1 : e.owner = o := congrArg (·.1) hx
  have h2 : e.start = st := congrArg (·.2.1) hx
  have h3 : e.count = ct := congrArg (·.2.2) hx
  rw [← h1, ← h2, ← h3]
  exact entryRunIs_of he

/-- **The same from an equation of the whole list.** -/
theorem entryRunIs_of_list {es : List Ahead} {L : List (Addr × Due × Due)}
    (hL : (es.map fun e => (e.owner, e.start, e.count)) = L) {i : Nat} {o : Addr} {st ct : Due}
    (h : L[i]? = some (o, st, ct)) : entryRunIs es i o st ct = true :=
  entryRunIs_of_map (by rw [hL]; exact h)

end ProofFile.Honest

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.entryRunIs_of_map
#print axioms ProofFile.Honest.entryRunIs_of_list
