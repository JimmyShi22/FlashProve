-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Ties/KeptOff.lean: WHOSE PADS A CODE SWITCH LAYS, AND WHOSE NOT, from the table's
own test
on the plan's numbers (`numbersFit`, Johnson/Desc/First/Borders.lean). Six theorems. A law file: no
sub-protocol imports it.

Why. A code switch lays the pads of the tenants that the group in front has kept. The claims that
stay
open across it must not read these pads. Two of these debts are facts on the plan's numbers alone.

What is said. Under `numbersFit os N n = true`, for m < n:
  `kept_in_group`: what segment m's group hands on as kept lies in that group.
  `kept_off_group`: so no tenant of ANOTHER group g ≤ n is among them (each tenant stands once).
  `index_off_kept`: nor is the index masks' tenant.
  `laysPads_switch`: at a place of the kind K2 the pads laid are those of `N.keptOf` at the number
  in
    front of what the switch opens, or none.
  `index_off_switch`: so the field indexOff of `K2Owes` (T5.lean).

Limits. `numbersFit` is a premise: a test with code; by the table's own head it has run true at two
real
plans, with a negative test: NOT RUN HERE. No soundness is claimed.

Terms: lean/GLOSSARY.md.
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise
import Johnson.Desc.First.Borders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Ties
open VerifiableInference.Desc (Place Oracle KindName)
open VerifiableInference.Desc.First (ModelPart Numbers numbersFit eachOnce laysPads rowOf)

theorem nodup_of_eachOnce : ∀ l : List (Nat × Nat), eachOnce l = true → l.Nodup
  | [], _ => List.nodup_nil
  | x :: l, h => by
    unfold eachOnce at h
    rw [Bool.and_eq_true] at h
    refine List.nodup_cons.2 ⟨fun hm => ?_, nodup_of_eachOnce l h.2⟩
    have : l.contains x = true := List.contains_iff_mem.2 hm
    rw [this] at h
    exact absurd h.1 (by decide)

section
variable {os : List Oracle} {N : Numbers} {n : Nat} (h : numbersFit os N n = true)
include h

/-- All the groups' tenants, then the index masks' and W's: each once. -/
theorem seats_nodup : (((List.range (n + 1)).flatMap fun m =>
    N.sent m 0 ++ N.sent m 1 ++ N.sent m 2) ++ [N.index, N.w]).Nodup := by
  unfold numbersFit at h
  simp only [Bool.and_eq_true] at h
  exact (List.nodup_append.1 (nodup_of_eachOnce _ h.1.2)).1

theorem kept_in_group (m : Nat) (hm : m < n) : ∀ x ∈ N.keptOf m, x ∈ N.group m := by
  unfold numbersFit at h
  simp only [Bool.and_eq_true] at h
  intro x hx
  have h1 := List.all_eq_true.1 h.2 m (List.mem_range.2 hm)
  exact List.contains_iff_mem.1 (List.all_eq_true.1 h1 x hx)

/-- No tenant of another group is among what segment m's group hands on as kept. -/
theorem kept_off_group (m g : Nat) (hm : m < n) (hg : g ≤ n) (hne : m ≠ g) :
    ∀ x ∈ N.group g, x ∉ N.keptOf m := by
  intro x hx hk
  have hx' := kept_in_group h m hm x hk
  have hN := (List.nodup_append.1 (seats_nodup h)).1
  have hP := (List.nodup_flatMap.1 hN).2
  have hD : List.Disjoint (N.sent m 0 ++ N.sent m 1 ++ N.sent m 2)
      (N.sent g 0 ++ N.sent g 1 ++ N.sent g 2) := by
    refine List.Pairwise.forall ?_ hP (List.mem_range.2 (Nat.lt_succ_of_lt hm))
      (List.mem_range.2 (Nat.lt_succ_of_le hg)) hne
    intro a b d x u v
    exact d v u
  exact hD hx' hx

/-- Nor is the index masks' tenant. -/
theorem index_off_kept (m : Nat) (hm : m < n) : N.index ∉ N.keptOf m := by
  intro hk
  have hx' := kept_in_group h m hm _ hk
  have hD := (List.nodup_append.1 (seats_nodup h)).2.2
  exact hD _ (List.mem_flatMap.2 ⟨m, List.mem_range.2 (Nat.lt_succ_of_lt hm), hx'⟩) _
    List.mem_cons_self rfl

end

/-- At a place of the kind K2: the pads of what the group in front has kept, or none. -/
theorem laysPads_switch (N : Numbers) (links : List ModelPart) (p : Place) (hk : p.kind = KindName.K2) :
    laysPads N links p = N.keptOf (p.link.getD links.length - 1) ∨ laysPads N links p = [] := by
  unfold laysPads
  rw [hk]
  cases (rowOf links p).lays
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The switch does not lay the index masks' pad.** -/
theorem index_off_switch {os : List Oracle} {N : Numbers} {n : Nat}
    (h : numbersFit os N n = true) (links : List ModelPart) (p : Place) (hk : p.kind = KindName.K2)
    (hm : p.link.getD links.length - 1 < n) : N.index ∉ laysPads N links p := by
  rcases laysPads_switch N links p hk with e | e
  · rw [e]
    exact index_off_kept h _ hm
  · rw [e]
    exact List.not_mem_nil

end VerifiableInference.Desc.First.K2Ties

#print axioms VerifiableInference.Desc.First.K2Ties.kept_in_group
#print axioms VerifiableInference.Desc.First.K2Ties.kept_off_group
#print axioms VerifiableInference.Desc.First.K2Ties.index_off_kept
#print axioms VerifiableInference.Desc.First.K2Ties.laysPads_switch
#print axioms VerifiableInference.Desc.First.K2Ties.index_off_switch
