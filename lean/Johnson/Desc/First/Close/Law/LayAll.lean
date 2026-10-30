-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayAll.lean: `layBlocks` (OnBytes/Iop/Ground.lean) leaves no member
out: every member with a size gets a block. Statements and proofs.

LayBlocks.lean, beside this file, shows that the blocks which are laid are in order. Here: that they
are all laid.
  `layStep_keeps`, `layInner_keeps`, `layOuter_keeps`: a place that holds a block goes on holding
    one.
  `layStep_size`, `layInner_size`, `layOuter_size`: the number of places stays.
  `layInner_sets`, `layOuter_sets`: the pass at the size e lays a block for every member of that
    size.
  `le_top`: no size is above the largest, so there is a pass at every size.
  `layBlocks_all`: if the member at the place j has a size, `layBlocks` returns a first row for j.

Limits. Nothing on which row that is (for that: `Laid`, LayBlocks.lean). Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw

/-- A step keeps the number of places, and a place that holds a block goes on holding one. -/
theorem layStep_keeps (sizes : Array (Option Nat)) (e : Nat) (acc : Array (Option Nat) × Nat)
    (i j : Nat) (h : ∃ f, acc.1[j]? = some (some f)) :
    ∃ f, (layStep sizes e acc i).1[j]? = some (some f) := by
  unfold layStep
  split
  · obtain ⟨f, hf⟩ := h
    dsimp only
    rw [Array.getElem?_setIfInBounds]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      have hlt : i < acc.1.size := by
        by_contra hn
        rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hf
        cases hf
      rw [if_pos hlt]
      exact ⟨_, rfl⟩
    · rw [if_neg hij]
      exact ⟨f, hf⟩
  · exact h

theorem layStep_size (sizes : Array (Option Nat)) (e : Nat) (acc : Array (Option Nat) × Nat)
    (i : Nat) : (layStep sizes e acc i).1.size = acc.1.size := by
  unfold layStep
  split <;> simp

theorem layInner_keeps (sizes : Array (Option Nat)) (e j : Nat) : ∀ (l : List Nat)
    (acc : Array (Option Nat) × Nat), (∃ f, acc.1[j]? = some (some f)) →
    ∃ f, (l.foldl (layStep sizes e) acc).1[j]? = some (some f)
  | [], _, h => h
  | i :: l, acc, h => layInner_keeps sizes e j l _ (layStep_keeps sizes e acc i j h)

theorem layInner_size (sizes : Array (Option Nat)) (e : Nat) : ∀ (l : List Nat)
    (acc : Array (Option Nat) × Nat), (l.foldl (layStep sizes e) acc).1.size = acc.1.size
  | [], _ => rfl
  | i :: l, acc => (layInner_size sizes e l _).trans (layStep_size sizes e acc i)

/-- The pass at the size e lays a block for every member of that size that the pass comes to. -/
theorem layInner_sets (sizes : Array (Option Nat)) (e j : Nat)
    (hs : sizes[j]? = some (some e)) : ∀ (l : List Nat) (acc : Array (Option Nat) × Nat),
    j ∈ l → acc.1.size = sizes.size → ∃ f, (l.foldl (layStep sizes e) acc).1[j]? = some (some f)
  | i :: l, acc, hm, hsz => by
    rw [List.foldl_cons]
    by_cases hij : i = j
    · subst hij
      refine layInner_keeps sizes e i l _ ?_
      have hlt : i < sizes.size := by
        by_contra hn
        rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hs
        cases hs
      unfold layStep
      rw [if_pos (by rw [(getD_some _ _ _).2 hs]; exact beq_self_eq_true _)]
      dsimp only
      rw [Array.getElem?_setIfInBounds, if_pos rfl, if_pos (hsz ▸ hlt)]
      exact ⟨_, rfl⟩
    · have hm' : j ∈ l := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm hij
        · exact h
      exact layInner_sets sizes e j hs l _ hm' ((layStep_size sizes e acc i).trans hsz)

theorem layOuter_keeps (sizes : Array (Option Nat)) (l : List Nat) (j : Nat) : ∀ (es : List Nat)
    (acc : Array (Option Nat) × Nat), (∃ f, acc.1[j]? = some (some f)) →
    ∃ f, (es.foldl (fun a e => l.foldl (layStep sizes e) a) acc).1[j]? = some (some f)
  | [], _, h => h
  | e :: es, acc, h => layOuter_keeps sizes l j es _ (layInner_keeps sizes e j l acc h)

theorem layOuter_size (sizes : Array (Option Nat)) (l : List Nat) : ∀ (es : List Nat)
    (acc : Array (Option Nat) × Nat),
    (es.foldl (fun a e => l.foldl (layStep sizes e) a) acc).1.size = acc.1.size
  | [], _ => rfl
  | e :: es, acc => (layOuter_size sizes l es _).trans (layInner_size sizes e l acc)

theorem layOuter_sets (sizes : Array (Option Nat)) (l : List Nat) (e j : Nat)
    (hs : sizes[j]? = some (some e)) (hj : j ∈ l) : ∀ (es : List Nat)
    (acc : Array (Option Nat) × Nat), e ∈ es → acc.1.size = sizes.size →
    ∃ f, (es.foldl (fun a e => l.foldl (layStep sizes e) a) acc).1[j]? = some (some f)
  | e' :: es, acc, hm, hsz => by
    rw [List.foldl_cons]
    by_cases he : e' = e
    · subst he
      exact layOuter_keeps sizes l j es _ (layInner_sets sizes e' j hs l acc hj hsz)
    · have hm' : e ∈ es := by
        rcases List.mem_cons.1 hm with h | h
        · exact absurd h.symm he
        · exact h
      exact layOuter_sets sizes l e j hs hj es _ hm' ((layInner_size sizes e' l acc).trans hsz)

/-- No size is above the largest. -/
theorem le_top : ∀ (l : List (Option Nat)) (m s : Nat), some s ∈ l →
    s ≤ l.foldl (fun m x => max m (x.getD 0)) m
  | x :: l, m, s, h => by
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · have mono : ∀ (l : List (Option Nat)) (a : Nat),
          a ≤ l.foldl (fun m x => max m (x.getD 0)) a := by
        intro l
        induction l with
        | nil => intro a; exact le_refl _
        | cons y l ih => intro a; exact (le_max_left _ _).trans (ih _)
      exact (le_max_right m s).trans (mono l _)
    · exact le_top l _ s h

/-- **EVERY MEMBER WITH A SIZE GETS A BLOCK.** -/
theorem layBlocks_all (sizes : Array (Option Nat)) (j s : Nat) (hs : sizes[j]? = some (some s)) :
    ∃ f, (layBlocks sizes).1[j]? = some (some f) := by
  have hlt : j < sizes.size := by
    by_contra hn
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hn)] at hs
    cases hs
  have hmem : some s ∈ sizes.toList := by
    rw [Array.getElem?_eq_getElem hlt] at hs
    have := Array.getElem_mem_toList hlt
    rwa [Option.some.inj hs] at this
  unfold layBlocks
  refine layOuter_sets sizes (List.range sizes.size) s j hs (List.mem_range.2 hlt) _ _ ?_ (by simp)
  rw [List.mem_reverse, List.mem_range, ← Array.foldl_toList]
  exact Nat.lt_succ_of_le (le_top sizes.toList 0 s hmem)

end OnBytes.LayLaw

#print axioms OnBytes.LayLaw.layBlocks_all
