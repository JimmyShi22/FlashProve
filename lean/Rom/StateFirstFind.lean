-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/StateFirstFind.lean: two lemmas on `findMade` (Rom/StateFirst.lean), the search in a list of
query-answer pairs for the stored answer of a query. They serve the step that expands a long answer
of a random oracle from a state.

  `findMade_self`   In the list with the one entry (o, q, r), the stored answer of (o, q) is r.
  `findMade_mem`    A stored answer that is found is an entry of the list.

Limits: it is not said which entry is found if the list holds several for one query (the first,
which is the oldest where entries are appended at the end: by the definition, not stated here). No
probability.
-/
import Rom.StateFirstMix

set_option autoImplicit false

namespace Rom

variable {S : OSpec}

/-- In the list with the one entry (o, q, r), the stored answer of (o, q) is r. -/
theorem findMade_self (o : S.ι) (q : S.Dom o) (r : S.Rng o) :
    findMade [(⟨o, q, r⟩ : QA S)] o q = some r := by
  simp [findMade]

theorem findMade_mem {made : List (QA S)} {o : S.ι} {q : S.Dom o}
    {r : S.Rng o} (h : findMade made o q = some r) : (⟨o, q, r⟩ : QA S) ∈ made := by
  obtain ⟨e, he, hf⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨o', q', r'⟩ := e
  by_cases ho : o' = o
  · subst ho
    by_cases hq : q' = q
    · subst hq
      simp only [dif_pos, if_true, Option.some.injEq] at hf
      subst hf
      exact he
    · simp [hq] at hf
  · simp [ho] at hf

end Rom
