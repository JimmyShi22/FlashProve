-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/KeyLaw/Plan.lean: the planner's entries at a face's size have the lookup's
shape: PlanShape of Statement.lean, proved.

Main names:
  bareOf: the entry that a description of a round adds, bare (Statement.lean).
  psc_bare, tree_bare: a sumcheck's and a product tree's entries.
  live_size, parts_size: the planner's record of a face's numbers gives the numbers back.
  planShape : PlanShape.

Limits. Nothing on the bits of work, on the errors, or on whether the planner returns.

-/
import Johnson.Desc.First.Look.KeyLaw.Pat
import OnBytes.Params.PlanListsSum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params
open OnBytes.Model (RoundName)

variable (s : Setting) (c : Scope)

/-- The entry that a description of a round adds, bare. -/
def bareOf (y : RoundSpec) : Fmt.Entry := bare (y.round s c).entry

theorem psc_bare (x : PscSize) : (pscList s x).map (bareOf s c) =
    (pscShape (x.degree.map (· - 1)) (if x.withY = true then some (x.degreeY, x.values) else
        none)).map
      entryOf := by
  unfold pscList pscShape
  cases x.withY <;>
    simp [bareOf, bare, entryOf, RoundSpec.round, pscEpsilon, pscVariable, pscY, RoundName.name,
      Function.comp_def]

theorem tree_bare (more : ℕ) : ∀ fuel l, (treeList s more fuel l).map (bareOf s c) =
    (levelsShape more fuel l).map entryOf
  | 0, _ => rfl
  | fuel + 1, l => by
    show (pscList s { degree := List.replicate (l + more) 3 } ++
      (lineRound s :: treeList s more fuel (l + 1))).map (bareOf s c) =
      ((pscShape (List.replicate (more + l) 2) (some (2, 2)) ++
        [(RoundName.line.name, 0, 1, 0)]) ++ levelsShape more fuel (l + 1)).map entryOf
    rw [List.map_append, List.map_cons, psc_bare, tree_bare more fuel (l + 1), List.map_append,
      List.map_append, List.append_assoc, Nat.add_comm l more]
    simp [bareOf, bare, entryOf, RoundSpec.round, lineRound, RoundName.name]

variable {s c}

theorem live_size {f : Face} (h1 : f.mu ≤ 6) (h2 : 2 ≤ f.planes) : lookupLive f.size = f.planes :=
    by
  unfold lookupLive Face.size
  by_cases h : f.planes = 2 ^ f.mu
  · simp [h, Nat.min_eq_left h1]
  · have : (f.planes == 2 ^ f.mu) = false := by simpa using h
    simp [this]
    omega

theorem parts_size {f : Face} (h : f.parts ≠ []) : lookupParts f.size = f.parts := by
  unfold lookupParts Face.size
  by_cases h1 : f.parts.length = 1
  · obtain ⟨v, hv⟩ := List.length_eq_one_iff.1 h1
    simp [hv]
  · have : (f.parts.length == 1) = false := by simpa using h1
    simp [this, h]

theorem flat_rep {α : Type} (n : ℕ) (l : List α) :
    (List.replicate n l).flatten = (List.range n).flatMap fun _ => l := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, List.flatten_cons, ih, flat_succ]

/-- **The planner's entries at a face's size have the lookup's shape.** -/
theorem planShape : PlanShape := by
  intro set scope f es hs hok h
  unfold Face.ok at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, k2⟩, k3⟩, -⟩, k5⟩, -⟩, -⟩, -⟩, -⟩ := hok
  have hne : f.parts ≠ [] := by
    intro h0
    rw [h0] at k5
    simp at k5
  unfold entriesG at h
  cases hf : finish set scope (planLookup f.size) with
  | error e => rw [hf] at h; cases h
  | ok P =>
    rw [hf] at h
    obtain rfl : P.rounds.map (·.entry) = es := Option.some.inj h
    obtain ⟨-, hr, -⟩ := finish_rounds (runs_lookup f.size) hf
    rw [hr, List.map_map, List.map_map]
    show (lookupList set f.size).map (bareOf set scope) = _
    have hsh : f.size.shifted = false := hs
    have hd : f.size.d = f.d := rfl
    have hmu : f.size.mu = f.mu := rfl
    unfold lookupList
    rw [live_size k2 k3, parts_size hne, hsh, hd, hmu, shape_cut]
    simp only [Bool.false_eq_true, if_false, List.nil_append, List.map_append, List.map_cons,
      List.map_flatten, List.map_replicate, List.map_map, psc_bare, tree_bare, flat_rep,
      List.map_flatMap, keysShape, List.map_nil, degs_eq]
    simp [bareOf, bare, entryOf, RoundSpec.round, RoundName.name, List.flatMap_def,
      Function.comp_def, tree_bare, List.map_flatten]

end VerifiableInference.Desc.K3.KeyLaw

#print axioms VerifiableInference.Desc.K3.KeyLaw.planShape
