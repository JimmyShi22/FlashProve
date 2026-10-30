-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/BookApart.lean: the seventh of the book's own tests (`ProverCoinCounts.clauses`,
Honest/Frame.lean: "a coin stands in two entries that spend it"), stated as lemmas: where no test of
a book fails, two spending entries at two positions have no coin in common. Lemmas with their
proofs; no definition.

  `ProverCoinCounts.spentApart`   from `B.word F = none`: two entries at two positions of the list of spending
     entries do not share a coin (`Ahead.shares`)
  `ProverCoinCounts.spentApart_parts`   so the spending entries of two different parts share no coin. Within one
     part it is `ProverCoinCounts.spentApart` that serves
  `shares_false_iff`   what "share no coin" means in numbers: if the two entries have one owner, no
     number lies in both blocks, in either field (by `meets_iff`, Honest/BookGuard.lean)

The first two at a book that `bookWhole` returns are in Honest/BookApartWhole.lean, so that this
file imports no more than Honest/BookGuard.lean and two files of Honest/Law/Rule/.

Related lemmas. Honest/Law/Rule/Tests.lean states the first, fourth, fifth and sixth test in the
same way (`ProverCoinCounts.rowsAt`, `ProverCoinCounts.within`, `ProverCoinCounts.behind`, `ProverCoinCounts.notUp`). Honest/BookLinear/Seventh.lean
(by the authors of K14's honest side) begins at the seventh test's own
`Bool`, not at a book: `apart_of_clause7` concludes `List.Pairwise` from it, by `pairwise_of_all`;
`clause7_of` concludes that `Bool` from a faster test. `ProverCoinCounts.spentApart` has the step of
`pairwise_of_all` inside its proof, in the form by positions. This file does not import that one.

Limits.
  * They say nothing where a test of the book fails. That a book passes its tests is a hypothesis.
  * Spending entries alone (`once := true`). An entry by which a part carries may share coins with
    any entry, as far as these lemmas go: that is the eighth test's matter.
  * What an owner does with its own coins is not seen. The coins of an entry are also among its
    owner's own coins; these lemmas compare entries with entries.
  * At which parts this is used is not said here: no part, kind or place is named.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.BookGuard
import Johnson.Desc.ProofFile.Honest.Law.Rule.Cell
import Johnson.Desc.ProofFile.Honest.Law.Rule.Tests

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (FileDescription)

variable {Xi : Type} {F : FileDescription Xi} {B : ProverCoinCounts}

/-- **The seventh test**: two entries at two positions of the list of spending entries have no coin
in common. -/
theorem ProverCoinCounts.spentApart (h : B.word F = none) : ∀ (i j : Nat) (e e' : Ahead),
    (B.ahead.filter (·.once))[i]? = some e → (B.ahead.filter (·.once))[j]? = some e' → i ≠ j →
    e.shares e' = false := by
  have t := ProverCoinCounts.tests h
  simp only [ProverCoinCounts.clauses, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at t
  obtain ⟨-, -, -, -, -, -, t7, -⟩ := t
  intro i j e e' hi hj hne
  have h1 : ((B.ahead.filter (·.once)).zipIdx.all fun q =>
      i == q.2 || !e.shares q.1) = true :=
    List.all_eq_true.1 t7 (e, i) (List.mem_zipIdx_iff_getElem?.2 hi)
  have h2 : (i == j || !e.shares e') = true :=
    List.all_eq_true.1 h1 (e', j) (List.mem_zipIdx_iff_getElem?.2 hj)
  rw [Bool.or_eq_true] at h2
  rcases h2 with h2 | h2
  · exact absurd (beq_iff_eq.1 h2) hne
  · cases hs : e.shares e' with
    | false => rfl
    | true =>
      rw [hs] at h2
      cases h2

/-- **The spending entries of two different parts have no coin in common.** Two entries with two
spenders are at two positions. Within one part (a = a') `ProverCoinCounts.spentApart` serves. -/
theorem ProverCoinCounts.spentApart_parts (h : B.word F = none) {a a' : Addr} (hne : a ≠ a') :
    ∀ e ∈ spentE B a, ∀ e' ∈ spentE B a', e.shares e' = false := by
  intro e he e' he'
  have m : ∀ {x : Addr} {f : Ahead}, f ∈ spentE B x →
      f ∈ B.ahead.filter (·.once) ∧ f.spender = x := by
    intro x f hf
    unfold spentE at hf
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hf
    obtain ⟨h3, h4⟩ := List.mem_filter.1 h1
    exact ⟨List.mem_filter.2 ⟨h3, h2⟩, beq_iff_eq.1 h4⟩
  obtain ⟨m1, s1⟩ := m he
  obtain ⟨m2, s2⟩ := m he'
  obtain ⟨i, hi⟩ := List.getElem?_of_mem m1
  obtain ⟨j, hj⟩ := List.getElem?_of_mem m2
  refine ProverCoinCounts.spentApart h i j e e' hi hj ?_
  intro hij
  rw [hij, hj] at hi
  have e1 : e' = e := Option.some.inj hi
  exact hne (by rw [← s1, ← s2, e1])

/-- **What "no coin in common" means in numbers**: if the two entries have one owner, no number lies
in both blocks, neither in the base field's count nor in the extension field's. -/
theorem shares_false_iff (e e' : Ahead) : e.shares e' = false ↔
    (e.owner = e'.owner →
      (¬ ∃ k, (e.start.f ≤ k ∧ k < e.start.f + e.count.f) ∧
        e'.start.f ≤ k ∧ k < e'.start.f + e'.count.f) ∧
      ¬ ∃ k, (e.start.e ≤ k ∧ k < e.start.e + e.count.e) ∧
        e'.start.e ≤ k ∧ k < e'.start.e + e'.count.e) := by
  unfold Ahead.shares
  rw [← meets_iff e.start.f e.count.f e'.start.f e'.count.f,
    ← meets_iff e.start.e e.count.e e'.start.e e'.count.e]
  by_cases ho : e.owner = e'.owner
  · have hb : (e.owner == e'.owner) = true := beq_iff_eq.2 ho
    rw [hb, Bool.true_and]
    cases meets e.start.f e.count.f e'.start.f e'.count.f <;>
      cases meets e.start.e e.count.e e'.start.e e'.count.e <;> simp [ho]
  · have hb : (e.owner == e'.owner) = false := beq_eq_false_iff_ne.2 ho
    rw [hb, Bool.false_and]
    simp [ho]

end ProofFile.Honest

#print axioms ProofFile.Honest.ProverCoinCounts.spentApart
#print axioms ProofFile.Honest.ProverCoinCounts.spentApart_parts
#print axioms ProofFile.Honest.shares_false_iff
