-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/End.lean: at the end of a chain the statement claims nothing any more.

The test for the end of a protocol asks that the proximity test of every group has begun and that
every sampled oracle message notes a group. This file shows that a statement which passes it claims
nothing any more (claims_end_of; Claims: Johnson/Desc/Means/Claims.lean), under three invariants: an
oracle message that notes a group is a member of it; a group whose test has begun holds no open row;
an oracle message that is not marked as sampled has no sample row (NoneYet). The first two are
written out here as conditions, and are shown to go over the beginning of a test (linked_begun,
markedEmpty_begun).

Main theorems: markedEmpty_begun, closeLedgers_noted, linked_begun, claims_end_of.

What is not claimed. That the first two invariants hold along a chain, but for the step shown here.
Nothing on whether a test that has begun was carried through. Nothing on soundness.

-/
import Johnson.Desc.Means.Claims

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {S : Statement}

/-- A group whose test has begun holds no open row: this goes over the beginning of a test. -/
theorem markedEmpty_begun (g : Nat) (G : Group)
    (h : ∀ (i : Nat) (G : Group), S.groups[i]? = some G → G.inRun = true → G.rows = #[]) :
    ∀ (i : Nat) (G' : Group), (Slice.begun S g G).groups[i]? = some G' → G'.inRun = true →
      G'.rows = #[] := by
  intro i G' hG' hr
  rw [begun_groups, Array.getElem?_modify] at hG'
  by_cases c : g = i
  · rw [if_pos c] at hG'
    obtain ⟨G0, _, rfl⟩ := Option.map_eq_some_iff.1 hG'
    rfl
  · rw [if_neg c] at hG'
    exact h i G' hG' hr

/-- Closing ledgers changes no note of a group. -/
theorem closeLedgers_noted : ∀ (l : List Nat) (S : Statement) (o : Nat),
    ((Slice.closeLedgers S l).oracles[o]?).map (fun x : Oracle => x.groups) =
      (S.oracles[o]?).map (fun x : Oracle => x.groups)
  | [], _, _ => rfl
  | a :: l, S, o => by
    show ((Slice.closeLedgers _ l).oracles[o]?).map _ = _
    rw [closeLedgers_noted l]
    exact map_modify _ _ _ _ _ fun _ => rfl

/-- An oracle message that notes a group is a member of it: this goes over the beginning of a
test. -/
theorem linked_begun (g : Nat) (G : Group)
    (h : ∀ (o : Nat) (x : Oracle) (g : Nat), S.oracles[o]? = some x → g ∈ x.groups →
      ∃ G, S.groups[g]? = some G ∧ o ∈ G.members) :
    ∀ (o : Nat) (x : Oracle) (g' : Nat), (Slice.begun S g G).oracles[o]? = some x →
      g' ∈ x.groups → ∃ G', (Slice.begun S g G).groups[g']? = some G' ∧ o ∈ G'.members := by
  intro o x' g' hx' hg'
  have e := closeLedgers_noted G.members.toList S o
  have hx'' : (Slice.closeLedgers S G.members.toList).oracles[o]? = some x' := hx'
  rw [hx''] at e
  obtain ⟨x, hx, hsame⟩ := Option.map_eq_some_iff.1 e.symm
  have hsame' : x.groups = x'.groups := hsame
  obtain ⟨G0, hG0, hm⟩ := h o x g' hx (by rw [hsame']; exact hg')
  rw [begun_groups, Array.getElem?_modify]
  by_cases c : g = g'
  · rw [if_pos c, hG0]
    exact ⟨_, rfl, hm⟩
  · rw [if_neg c]
    exact ⟨G0, hG0, hm⟩

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- **A statement that passes the test for the end of a protocol claims nothing any more.** -/
theorem claims_end_of
    (hT : (S.groups.all (·.inRun) && S.oracles.all fun x => !x.sampled || !x.groups.isEmpty) = true)
    (hL : ∀ (o : Nat) (x : Oracle) (g : Nat), S.oracles[o]? = some x → g ∈ x.groups →
      ∃ G, S.groups[g]? = some G ∧ o ∈ G.members)
    (hM : ∀ (i : Nat) (G : Group), S.groups[i]? = some G → G.inRun = true → G.rows = #[])
    (hN : NoneYet S) (m : Words K) : Claims ρ S m := by
  simp only [Bool.and_eq_true, Array.all_eq_true_iff_forall_mem] at hT
  obtain ⟨h1, h2⟩ := hT
  have hall : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → G.inRun = true :=
    fun g G hG => h1 G (Array.mem_of_getElem? hG)
  refine claims_end ρ hall (fun g G hG => hM g G hG (hall g G hG)) (fun o x hx hne => ?_) m
  have hs : x.sampled = true := by
    by_contra c
    exact hne (hN o x hx (Bool.eq_false_iff.2 c))
  have c := h2 x (Array.mem_of_getElem? hx)
  rw [hs] at c
  have hne' : x.groups ≠ [] := by
    intro c'
    rw [c'] at c
    simp at c
  obtain ⟨g, hg⟩ := List.exists_mem_of_ne_nil _ hne'
  obtain ⟨G, hG, hm⟩ := hL o x g hx hg
  exact ⟨g, G, hG, Array.mem_toList_iff.2 hm⟩

end OnBytes.Means
