-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/PlanListsMembers.lean: the few different rounds of which the planner's long lists are
made.

The lists of OnBytes/Params/PlanListsSum.lean and OnBytes/Params/PlanListsProx.lean are long where a
loop is long, but a loop adds the same description of a round in every turn whose variable the round
does not read. This file says which descriptions can be members of a sumcheck's list, a product
tree's, a lookup's and the list of a fold's rounds. So a fact that is wanted of every round of such
a list is wanted of these few.

Main theorems: `map_pscVariable_replicate`, `mem_pscList`, `mem_treeList` (five descriptions,
whatever the numbers of levels and of further variables), `mem_lookupList` (thirteen),
`foldRoundError_eq`, `foldRound_eq`, `mem_foldFromList`.
What is not claimed: that each of the named descriptions is a member. `foldRoundError_eq` and
`foldRound_eq` are for settings without the factor of the rows (the line `rowcost` 1). Nothing on
the lists of a code switch, a last step, the stages and a proximity test
(OnBytes/Params/PlanListsProx.lean), nor on those of OnBytes/Params/PlanListsChains.lean and
OnBytes/Plan/PlanListsKey.lean as wholes. For proofs only; the program, that is the Lean port built
from OnBytes/, does not import this file.

-/
import OnBytes.Params.PlanListsProx

set_option autoImplicit false

namespace OnBytes.Params

/-- The rounds of n variables of one degree are one description, n times. -/
theorem map_pscVariable_replicate (s : Setting) (n g : Nat) :
    (List.replicate n g).map (pscVariable s) = List.replicate n (pscVariable s g) :=
  List.map_replicate

/-- The members of a sumcheck's list. -/
theorem mem_pscList {s : Setting} {x : PscSize} {y : RoundSpec} (h : y ∈ pscList s x) :
    y = pscEpsilon s ∨ (∃ g ∈ x.degree, y = pscVariable s g) ∨
      (x.withY = true ∧ (y = pscY s x.degreeY ∨ y = .silent "PSC values" (24 * x.values) 0)) := by
  unfold pscList at h
  rcases List.mem_cons.1 h with h | h
  · exact Or.inl h
  · rcases List.mem_append.1 h with h | h
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.1 h
      exact Or.inr (Or.inl ⟨g, hg, rfl⟩)
    · split at h
      · rename_i hy
        rcases List.mem_cons.1 h with h | h
        · exact Or.inr (Or.inr ⟨hy, Or.inl h⟩)
        · exact Or.inr (Or.inr ⟨hy, Or.inr (List.mem_singleton.1 h)⟩)
      · cases h

/-- The members of a product tree's list: five descriptions, whatever the levels. -/
theorem mem_treeList {s : Setting} {more : Nat} {y : RoundSpec} :
    ∀ {fuel l : Nat}, y ∈ treeList s more fuel l →
      y = pscEpsilon s ∨ y = pscVariable s 3 ∨ y = pscY s 2 ∨
        y = .silent "PSC values" (24 * 2) 0 ∨ y = lineRound s
  | 0, _, h => by cases h
  | fuel + 1, l, h => by
      unfold treeList at h
      rcases List.mem_append.1 h with h | h
      · rcases mem_pscList h with h | ⟨g, hg, h⟩ | ⟨_, h | h⟩
        · exact Or.inl h
        · rw [(List.mem_replicate.1 hg).2] at h
          exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · rcases List.mem_cons.1 h with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
        · exact mem_treeList h

/-- A member of a list of copies of one list, flattened, is a member of that list. -/
theorem mem_of_replicate_flatten {α : Type} {n : Nat} {l : List α} {y : α}
    (h : y ∈ (List.replicate n l).flatten) : y ∈ l := by
  obtain ⟨l', hl, hy⟩ := List.mem_flatten.1 h
  rw [(List.mem_replicate.1 hl).2] at hy
  exact hy

/-- The descriptions of which a lookup's list is made: thirteen. The first four read the lookup's
sizes; the other nine are the same for every lookup under one setting. -/
def lookupMembers (s : Setting) (x : LookupSize) : List RoundSpec :=
  [.said "LKP shift" .field (fieldError s (2 ^ x.d)) { drawE := 1, priced := .callersWord } 0 0 0,
   .said "LKP" .field (Bound.ratio (sumT ((lookupParts x).map (2 ^ ·)) - 1) s.cardE)
      { drawE := 1, priced := .callersWord } 0 0 0,
   .said "JOIN" .field (fieldError s x.mu) { drawE := x.mu, priced := .roundItself } 0 0 0,
   .said "ZERO" .field (fieldError s (x.mu + x.d))
      { drawE := x.mu + x.d, priced := .roundItself } 0 0 0,
   pscEpsilon s, pscVariable s 3, pscVariable s 2, pscY s 3, pscY s 2, lineRound s,
   .silent "PSC values" (24 * 3) 0, .silent "PSC values" (24 * 2) 0,
   .silent "PSC values" (24 * 1) 0]

/-- Every member of a lookup's list is one of `lookupMembers`. -/
theorem mem_lookupList {s : Setting} {x : LookupSize} {y : RoundSpec} (h : y ∈ lookupList s x) :
    y ∈ lookupMembers s x := by
  have tree : ∀ {more fuel l : Nat}, y ∈ treeList s more fuel l → y ∈ lookupMembers s x := by
    intro more fuel l ht
    rcases mem_treeList ht with h | h | h | h | h <;> subst h <;> simp [lookupMembers]
  unfold lookupList at h
  rcases List.mem_append.1 h with h | h
  · split at h
    · rw [List.mem_singleton.1 h]
      simp [lookupMembers]
    · cases h
  rcases List.mem_cons.1 h with h | h
  · subst h
    simp [lookupMembers]
  rcases List.mem_append.1 h with h | h
  · rcases mem_pscList h with h | ⟨g, hg, _⟩ | ⟨_, h | h⟩
    · subst h; simp [lookupMembers]
    · cases hg
    · subst h; simp [lookupMembers]
    · subst h; simp [lookupMembers]
  rcases List.mem_append.1 h with h | h
  · rcases mem_pscList (mem_of_replicate_flatten h) with h | ⟨g, hg, _⟩ | ⟨_, h | h⟩
    · subst h; simp [lookupMembers]
    · cases hg
    · subst h; simp [lookupMembers]
    · subst h; simp [lookupMembers]
  rcases List.mem_append.1 h with h | h
  · rcases mem_pscList (mem_of_replicate_flatten h) with h | ⟨g, hg, _⟩ | ⟨_, h | h⟩
    · subst h; simp [lookupMembers]
    · cases hg
    · subst h; simp [lookupMembers]
    · subst h; simp [lookupMembers]
  rcases List.mem_cons.1 h with h | h
  · subst h
    simp [lookupMembers]
  rcases List.mem_append.1 h with h | h
  · obtain ⟨l', hl, hy⟩ := List.mem_flatten.1 h
    obtain ⟨v, _, rfl⟩ := List.mem_map.1 hl
    exact tree hy
  rcases List.mem_append.1 h with h | h
  · exact tree h
  rcases List.mem_append.1 h with h | h
  · rcases mem_pscList h with h | ⟨g, hg, h⟩ | ⟨hw, _⟩
    · subst h; simp [lookupMembers]
    · rcases List.mem_append.1 hg with hg | hg
      · rw [(List.mem_replicate.1 hg).2] at h
        subst h; simp [lookupMembers]
      · rw [(List.mem_replicate.1 hg).2] at h
        subst h; simp [lookupMembers]
    · cases hw
  rcases List.mem_cons.1 h with h | h
  · subst h
    simp [lookupMembers]
  · rcases mem_pscList h with h | ⟨g, hg, h⟩ | ⟨_, h | h⟩
    · subst h; simp [lookupMembers]
    · rw [(List.mem_replicate.1 hg).2] at h
      subst h; simp [lookupMembers]
    · subst h; simp [lookupMembers]
    · subst h; simp [lookupMembers]

/-- In a setting without the factor of the rows the error of a fold's round depends on j only
through whether mask rows are still folded. -/
theorem foldRoundError_eq {s : Setting} (hs : s.rowsFactor = false) (g : GroupSize) (a : Analysis)
    {j j' : Nat} (h : (g.hasMask && decide (j ≤ g.h)) = (g.hasMask && decide (j' ≤ g.h))) :
    foldRoundError s g a j = foldRoundError s g a j' := by
  unfold foldRoundError mcaError
  simp only [hs, Bool.false_and, Bool.false_eq_true, if_false, h]

/-- So the description of a fold's round, too: a fold has at most two different descriptions beside
its first round's. -/
theorem foldRound_eq {s : Setting} (hs : s.rowsFactor = false) (g : GroupSize) (a : Analysis)
    {j j' : Nat} (h : (g.hasMask && decide (j ≤ g.h)) = (g.hasMask && decide (j' ≤ g.h))) :
    foldRound s g a j = foldRound s g a j' := by
  unfold foldRound
  rw [foldRoundError_eq hs g a h, h]

/-- The members of the list of a fold's rounds. -/
theorem mem_foldFromList {s : Setting} {g : GroupSize} {a : Analysis} {y : RoundSpec} :
    ∀ {fuel j : Nat}, y ∈ foldFromList s g a fuel j → ∃ i, j ≤ i ∧ i < j + fuel ∧
      y = foldRound s g a i
  | 0, _, h => by cases h
  | fuel + 1, j, h => by
      unfold foldFromList at h
      rcases List.mem_cons.1 h with h | h
      · exact ⟨j, le_refl j, by omega, h⟩
      · obtain ⟨i, h1, h2, h3⟩ := mem_foldFromList h
        exact ⟨i, by omega, by omega, h3⟩

end OnBytes.Params

#print axioms OnBytes.Params.mem_treeList
#print axioms OnBytes.Params.mem_lookupList
#print axioms OnBytes.Params.foldRoundError_eq
#print axioms OnBytes.Params.foldRound_eq
#print axioms OnBytes.Params.mem_foldFromList
