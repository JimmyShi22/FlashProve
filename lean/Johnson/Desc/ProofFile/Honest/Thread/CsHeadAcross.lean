-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/CsHeadAcross.lean: arithmetic lemmas about the spans of the 55
rider clauses in `csHead` (Honest/Thread/CsHead.lean). A rider clause states a fact about the
verifier's state that holds from border `lo` to border `hi` of the first chain; border b is the
point before sub-protocol number b. The file holds three lemmas and no definition.

A lemma which shows that a run's invariant holds again after sub-protocol number b has two
hypotheses about the list of clauses: each clause whose `lo` is at most b and whose `hi` is at least
b + 1 still holds after the step, and each clause with lo = b + 1 is established by the step. The
lemmas here say which clauses of `csHead` fall under either hypothesis.

  1  `csHead_across`   if a clause has `lo` at most b and `hi` at least b + 1, then b is in one of
     three ranges
  2  `csHead_none_across_341`   no clause has `lo` at most 341 and `hi` at least 342
  3  `csHead_begins_342`   the only clause with lo = 342 is the first of the list

Sub-protocol number 341 is the output head's own rounds (kind K6).

Limits.
  * The lemmas read the numbers `lo` and `hi` only. They say nothing about the facts that the
    clauses state.
  * `csHead_begins_342` names the first clause's fact. If that fact changes in `csHead`, the lemma
    changes with it.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.CsHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc.First (S)

variable {W : Type} {ν : Nat} {st : Nat → S → Prop}
  {R : Nat → Option OnBytes.Model.Forest.Heard → Prop} {c : RiderCl W S}

/-- If a clause of the list has `lo` at most b and `hi` at least b + 1, then b is between 342 and
351, or is one of five numbers in an attention segment, or is one of five numbers in a layers'
segment. -/
theorem csHead_across (h : c ∈ csHead ν st R) {b : Nat} (h1 : c.lo ≤ b) (h2 : b + 1 ≤ c.hi) :
    (342 ≤ b ∧ b < 352) ∨
      (∃ g, g < 12 ∧ 14 * (2 * g + 1) + 4 ≤ b ∧ b < 14 * (2 * g + 1) + 9) ∨
      ∃ g, g < 12 ∧ 28 * g + 5 ≤ b ∧ b < 28 * g + 10 := by
  rcases csHead_span h with ⟨a1, a2⟩ | ⟨l, -, e1, e2⟩ | ⟨g, hg, e1, e2⟩ | ⟨g, hg, e1, e2⟩
  · exact Or.inl ⟨by omega, by omega⟩
  · exact absurd h2 (by omega)
  · exact Or.inr (Or.inl ⟨g, hg, by omega, by omega⟩)
  · exact Or.inr (Or.inr ⟨g, hg, by omega, by omega⟩)

/-- No clause of the list has `lo` at most 341 and `hi` at least 342. -/
theorem csHead_none_across_341 (h : c ∈ csHead ν st R) (h1 : c.lo ≤ 341) : ¬ 341 + 1 ≤ c.hi := by
  intro h2
  rcases csHead_across h h1 h2 with ⟨a, -⟩ | ⟨g, hg, -, a⟩ | ⟨g, hg, -, a⟩
  · omega
  · omega
  · omega

/-- The only clause of the list with lo = 342 is the first. -/
theorem csHead_begins_342 (h : c ∈ csHead ν st R) (e : c.lo = 341 + 1) :
    c = riderHead (341 + 1) 347 fun o => o.x.isSome = true := by
  rcases (csHead_mem ν st R c).1 h with
    ((((rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨l, -, rfl⟩) | ⟨g, -, rfl⟩) | ⟨g, -, rfl⟩)
  · rfl
  · exact absurd e (show (343 : Nat) ≠ 341 + 1 by omega)
  · exact absurd e (show (347 : Nat) ≠ 341 + 1 by omega)
  · exact absurd e (show (346 : Nat) ≠ 341 + 1 by omega)
  · exact absurd e (show (344 : Nat) ≠ 341 + 1 by omega)
  · exact absurd e (show (346 : Nat) ≠ 341 + 1 by omega)
  · exact absurd e (show (346 : Nat) ≠ 341 + 1 by omega)
  · exact absurd e (show 14 * l + 9 ≠ 341 + 1 by omega)
  · exact absurd e (show 14 * (2 * g + 1) + 4 ≠ 341 + 1 by omega)
  · exact absurd e (show 28 * g + 5 ≠ 341 + 1 by omega)

end ProofFile.Honest

#print axioms ProofFile.Honest.csHead_across
#print axioms ProofFile.Honest.csHead_none_across_341
#print axioms ProofFile.Honest.csHead_begins_342
