-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Rows/Slice.lean: THE WALK BY CALLS, MADE CHEAP FOR THE KERNEL IN TWO WAYS.
(1) StepC.lean's walkCalls drops into the written rounds anew, from their head, at every call; here
the REST of the written rounds is handed on. (2) A long routine's noted calls are walked IN SLICES,
each slice a closed fact of its own.
Definitions and theorems. A law file; no running text imports it.
  `walkR`         with code: walkCalls with the rest of the written rounds handed on. `walkR_eq`: it
                  is walkCalls.
  `pieceD`        with code: pieceC over walkR.   `pieceD_eq`: it is pieceC.
  `walk_append`   the walk over two lists of calls, one behind the other.
  `sliceD s truth st x σ₀ a w` with code: x is run once from no call and no round at σ₀ FOR ITS
                  CALLS; of these the w from place a on are walked from the state st.
  `good_of_slices`   a table over m slices of w calls each, which begins at (σ₀, 0), covers all the
                  calls and ends at counters 0 and at truth's length: Good, for a faithful routine.
  `length_of_drops`   a list's length said by two drops (List.length nests a level an element for
                      the kernel).
Limits. No closed fact is here. Nothing on soundness or on hiding.
-/
import Johnson.AtFull.Rows.Twin

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Params
open Johnson.G hiding sendsFrom

/-- walkCalls with the rest of the written rounds handed on. -/
def walkR (s : Setting) : SmallSt × Nat → List PlanRound → List Call → Option (SmallSt × Nat)
  | st, _, [] => some st
  | st, rest, c :: cs =>
    match c.plan.run (st.1.plan s) with
    | .error _ => none
    | .ok (_, q) =>
      if sameAll q.rounds.toList (rest.take q.rounds.size) then
        walkR s (smallOf q, st.2 + q.rounds.size) (rest.drop q.rounds.size) cs
      else none

theorem walkR_eq (s : Setting) (truth : List PlanRound) :
    ∀ (cs : List Call) (st : SmallSt × Nat),
      walkR s st (truth.drop st.2) cs = walkCalls s truth st cs
  | [], st => by
    unfold walkR walkCalls
    rfl
  | c :: cs, st => by
    unfold walkR walkCalls
    cases c.plan.run (st.1.plan s) with
    | error m => rfl
    | ok r =>
      obtain ⟨u, q⟩ := r
      dsimp only
      rw [List.drop_drop]
      have ih := walkR_eq s truth cs (smallOf q, st.2 + q.rounds.size)
      dsimp only at ih
      rw [ih]

/-- pieceC over walkR. -/
def pieceD (s : Setting) (truth : List PlanRound) (st : SmallSt × Nat) (x : N Unit) :
    Option (SmallSt × Nat) :=
  match (x.run #[]).run (st.1.plan s) with
  | .error _ => none
  | .ok ((_, cs), _) => walkR s st (truth.drop st.2) cs.toList

theorem pieceD_eq (s : Setting) (truth : List PlanRound) (st : SmallSt × Nat) (x : N Unit) :
    pieceD s truth st x = pieceC s truth st x := by
  unfold pieceD pieceC
  cases (x.run #[]).run (st.1.plan s) with
  | error m => rfl
  | ok r =>
    obtain ⟨⟨u, cs⟩, q⟩ := r
    exact walkR_eq s truth cs.toList st

/-- The walk over two lists of calls, one behind the other. -/
theorem walk_append {s : Setting} {truth : List PlanRound} :
    ∀ (l₁ l₂ : List Call) (st st' st'' : SmallSt × Nat), walkCalls s truth st l₁ = some st' →
      walkCalls s truth st' l₂ = some st'' → walkCalls s truth st (l₁ ++ l₂) = some st''
  | [], l₂, st, st', st'', h1, h2 => by
    unfold walkCalls at h1
    cases h1
    exact h2
  | c :: l₁, l₂, st, st', st'', h1, h2 => by
    unfold walkCalls at h1
    rw [List.cons_append]
    unfold walkCalls
    cases e : c.plan.run (st.1.plan s) with
    | error m =>
      rw [e] at h1
      cases h1
    | ok r =>
      obtain ⟨u, q⟩ := r
      rw [e] at h1
      dsimp only at h1 ⊢
      split at h1
      · rename_i c1
        rw [if_pos c1]
        exact walk_append l₁ l₂ _ _ _ h1 h2
      · cases h1

/-- The walk of a list of calls from slice j on, by a table over slices of w calls. -/
theorem walk_from_slices {s : Setting} {truth : List PlanRound} (L : List Call) (w m : Nat)
    (tab : Nat → SmallSt × Nat) (hl : L.length ≤ m * w)
    (h : ∀ i, i < m → walkCalls s truth (tab i) ((L.drop (i * w)).take w) = some (tab (i + 1))) :
    ∀ k j, j + k = m → walkCalls s truth (tab j) (L.drop (j * w)) = some (tab m)
  | 0, j, e => by
    have ej : j = m := by omega
    subst ej
    rw [List.drop_of_length_le hl]
    unfold walkCalls
    rfl
  | k + 1, j, e => by
    have hj : j < m := by omega
    have ih := walk_from_slices L w m tab hl h k (j + 1) (by omega)
    have e1 : L.drop (j * w) = (L.drop (j * w)).take w ++ L.drop ((j + 1) * w) := by
      have : (j + 1) * w = j * w + w := by rw [Nat.add_mul, Nat.one_mul]
      rw [this, ← List.drop_drop, List.take_append_drop]
    rw [e1]
    exact walk_append _ _ _ _ _ (h j hj) ih

/-- One slice of a routine's noted calls, walked from the state st. -/
def sliceD (s : Setting) (truth : List PlanRound) (st : SmallSt × Nat) (x : N Unit) (σ₀ : SmallSt)
    (a w : Nat) : Option (SmallSt × Nat) :=
  match (x.run #[]).run (σ₀.plan s) with
  | .error _ => none
  | .ok ((_, cs), _) => walkR s st (truth.drop st.2) ((cs.toList.drop a).take w)

/-- **A table over the slices of a faithful routine's noted calls gives the walk.** -/
theorem good_of_slices {s : Setting} {truth : List PlanRound} {x : N Unit} {σ₀ : SmallSt}
    {sc' : Scope}
    (hx : Faith x) (w m : Nat) (tab : Nat → SmallSt × Nat)
    (h0 : tab 0 = (σ₀, 0)) (hl : (callsAt s σ₀ x).size ≤ m * w)
    (h : ∀ i, i < m → sliceD s truth (tab i) x σ₀ (i * w) w = some (tab (i + 1)))
    (hm : 0 < m) (he : tab m = (⟨sc', 0, 0, 0⟩, truth.length)) : Good s truth (σ₀, 0) x := by
  cases e : (x.run #[]).run (σ₀.plan s) with
  | error msg =>
    have h' := h 0 hm
    unfold sliceD at h'
    rw [e] at h'
    cases h'
  | ok r =>
    obtain ⟨⟨u, cs⟩, q⟩ := r
    have hc : callsAt s σ₀ x = cs := by
      unfold callsAt outAt
      rw [e]
      rfl
    rw [hc] at hl
    have hs : ∀ i, i < m →
        walkCalls s truth (tab i) ((cs.toList.drop (i * w)).take w) = some (tab (i + 1)) := by
      intro i hi
      have h' := h i hi
      unfold sliceD at h'
      rw [e] at h'
      dsimp only at h'
      rw [walkR_eq] at h'
      exact h'
    have hw := walk_from_slices cs.toList w m tab (by simpa using hl) hs m 0 (by omega)
    rw [Nat.zero_mul, List.drop_zero, h0, he] at hw
    refine good_oneC (sc' := sc') hx ?_
    unfold pieceC
    dsimp only
    rw [e]
    exact hw

/-- A list's length, said by two drops. -/
theorem length_of_drops {α : Type} (l : List α) (n : Nat)
    (h : ((l.drop (n + 1)).isEmpty && !(l.drop n).isEmpty) = true) : l.length = n + 1 := by
  simp only [Bool.and_eq_true, List.isEmpty_iff, Bool.not_eq_true', List.drop_eq_nil_iff] at h
  obtain ⟨h1, h2⟩ := h
  have h3 : ¬ l.length ≤ n := by
    intro c
    have : l.drop n = [] := List.drop_eq_nil_iff.2 c
    rw [this] at h2
    simp at h2
  omega

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.walkR_eq
#print axioms VerifiableInference.Desc.LinkJoin.pieceD_eq
#print axioms VerifiableInference.Desc.LinkJoin.walk_append
#print axioms VerifiableInference.Desc.LinkJoin.good_of_slices
#print axioms VerifiableInference.Desc.LinkJoin.length_of_drops
