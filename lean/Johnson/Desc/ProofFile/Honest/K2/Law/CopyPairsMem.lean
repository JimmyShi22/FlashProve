-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CopyPairsMem.lean: the kind "the code switch" (K2): WHAT A
MEMBER OF `copyPairs` IS (Honest/K2/Law/CopyFitsWritten.lean): both its switches are written places;
their links are neighbours; its segment is the written one between them; and so just that segment
lies between the two links, in the form in which the laws on a kept copy ask it (hS). PUBLIC DATA
ALONE. Three statements with their proofs; no definition.

  `take_succ_drop`      a list's entry number k is all that lies between k and k + 1
  `copyPairs_mem`       a member's two places, links and segment
  `copyPairs_between`   hS and hl at a member

By: `copyPairs`' own text: `List.filterMap`, `List.find?`. No closed fact is used: these hold of the
list by its make.

Limits. At the written lists `placesW`, `segsW`: not carried to the head's own. That the place found
in front is the only one with that link is not said, nor needed. Nothing on shapes, codes, the book
or a run. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopyFitsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law

/-- A list's entry number k is all that lies between k and k + 1. -/
theorem take_succ_drop {α : Type} {l : List α} {k : Nat} {a : α} (h : l[k]? = some a) :
    (l.take (k + 1)).drop k = [a] := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero =>
      rw [List.getElem?_cons_zero] at h
      obtain rfl := Option.some.inj h
      rfl
    | succ k =>
      rw [List.getElem?_cons_succ] at h
      exact ih h

/-- **A member of the list of pairs.** -/
theorem copyPairs_mem {x : SwitchPlace × SwitchPlace × SegmentPub} (hx : x ∈ copyPairs) :
    x.1 ∈ placesW ∧ x.2.1 ∈ placesW ∧ x.1.link + 1 = x.2.1.link ∧
      segsW[x.2.1.link - 1]? = some x.2.2 := by
  unfold copyPairs at hx
  obtain ⟨p, hp, hy⟩ := List.mem_filterMap.1 hx
  cases hf : placesW.find? (fun q => q.link + 1 == p.link) with
  | none =>
    rw [hf] at hy
    cases hy
  | some p₀ =>
    cases hs : segsW[p.link - 1]? with
    | none =>
      rw [hf, hs] at hy
      cases hy
    | some S =>
      rw [hf, hs] at hy
      obtain rfl : (p₀, p, S) = x := Option.some.inj hy
      have hq := List.find?_some hf
      exact ⟨List.mem_of_find?_eq_some hf, hp, eq_of_beq hq, hs⟩

/-- **hS and hl at a member**: in the laws' own form, at the written segments. -/
theorem copyPairs_between {x : SwitchPlace × SwitchPlace × SegmentPub} (hx : x ∈ copyPairs) :
    (segsW.take x.2.1.link).drop x.1.link = [x.2.2] ∧ x.1.link ≤ x.2.1.link := by
  obtain ⟨-, -, hl, hs⟩ := copyPairs_mem hx
  rw [← hl] at hs ⊢
  exact ⟨take_succ_drop (by simpa using hs), Nat.le_succ _⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.take_succ_drop
#print axioms ProofFile.Honest.K2.Law.copyPairs_mem
#print axioms ProofFile.Honest.K2.Law.copyPairs_between
