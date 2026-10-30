-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Lines/Layers/PublicRecordLight.lean: a second text of the test at the whole
public record (atXL, Johnson/AtFull/Shape/AtX.lean), equal to it at every test: atXLLight. It is
made in three stages. In place, unfolded, columnsOf (OnBytes/Model/Calls.lean), which appends arrays
in a fold, is rewritten into a function on lists. In baseNoFill, unfolded, place is rewritten into
that second text. In atXL, with atMakers, withPubC and withLookC unfolded, baseNoFill is rewritten
into its second text. Each time only where the name shows. And the way back, atXLC_of_light: a
closed Bool that is true on the second text is true under atXLC
(Johnson/AtFull/Shape/AtXCounts.lean). General; nothing is evaluated.

Why. A test that reads the placed calls' columns makes whoever evaluates it run columnsOf. The
second text is meant to spare Lean's kernel that fold.

Main names.
* columnsOfLists, columnsOf_lists: the columns by lists; equal to columnsOf at all arguments.
* placeLight, baseNoFillLight, atXLLight: pairs of a second text, made by Lean, and its equation
  with the first.

Limits. Equations of terms, with no premise. The second texts can be read nowhere here: #print shows
them. The pairs' type is met by the first text itself: that a column is made by lists in the second
text, or that no call of columnsOf is left in it, is stated nowhere. What either text costs is not
said. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.AtXCounts

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- The second texts are made by unfolding long definitions: two limits of the elaborator are lifted.
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

-- No default table of scales is in sight: a statement that reads a table says which.
attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Layers
open OnBytes OnBytes.Model OnBytes.Model.Layer
open Johnson.AtFull.Shape

/-- columnsOf by lists: the pieces' runs of columns one after the other, then zeros. -/
def columnsOfLists (pieces : List (Nat × Nat × Nat)) (s n : Nat) : Array Nat :=
  (((pieces.filter fun (p : Nat × Nat × Nat) => p.1 == s).flatMap
      fun (p : Nat × Nat × Nat) => (List.range (2 ^ p.2.1)).map (· + p.2.2)) ++
    List.replicate
      (n - ((pieces.filter fun (p : Nat × Nat × Nat) => p.1 == s).flatMap
        fun (p : Nat × Nat × Nat) => (List.range (2 ^ p.2.1)).map (· + p.2.2)).length) 0).toArray

/-- The fold that appends the pieces' runs of columns, by lists. -/
theorem fold_lists : ∀ (ps : List (Nat × Nat × Nat)) (a : Array Nat),
    ps.foldl (fun a p => a ++ (Array.range (2 ^ p.2.1)).map (· + p.2.2)) a =
      (a.toList ++ ps.flatMap fun p => (List.range (2 ^ p.2.1)).map (· + p.2.2)).toArray
  | [], a => by simp
  | p :: ps, a => by
    rw [List.foldl_cons, fold_lists ps]
    simp [List.flatMap_cons, List.append_assoc]

/-- columnsOf is columnsOfLists, at all arguments. -/
theorem columnsOf_lists (pieces : List (Nat × Nat × Nat)) (s n : Nat) :
    columnsOf pieces s n = columnsOfLists pieces s n := by
  unfold columnsOf columnsOfLists
  simp only [fold_lists]
  simp

/-- place with the columns by lists, and its equation with place. -/
def placeLight : { f : String → String → List SegAsk → Nat → CallD //
    ∀ a b c d, place a b c d = f a b c d } :=
  ⟨_, fun a b c d => by
    delta place
    simp -zeta only [columnsOf_lists]
    rfl⟩

/-- baseNoFill over placeLight, and its equation with baseNoFill. -/
def baseNoFillLight : { f : Shape → List (List String) → Except String Lay //
    ∀ h pc, baseNoFill h pc = f h pc } :=
  ⟨_, fun h pc => by
    delta baseNoFill
    simp -zeta only [placeLight.2]
    rfl⟩

/-- The test at the whole public record in its second text, and its equation with atXL. -/
def atXLLight : { g : (Verify.Public → Bool) → Bool // ∀ t, atXL t = g t } :=
  ⟨_, fun t => by
    delta atXL Johnson.AtFull.Public.atMakers OnBytes.Road.K4.Trial.AttK7Owners.withPubC
      OnBytes.Road.K4.Trial.AttK7Owners.withLookC
    simp -zeta only [baseNoFillLight.2]
    rfl⟩

/-- **A test that accepts on the second text accepts under atXLC.** -/
theorem atXLC_of_light {t : Verify.Public → Bool}
    (h : atXLLight.1 (fun X => t (withCounts X)) = true) : atXLC t = true :=
  (atXLLight.2 _).trans h

end Johnson.AtFull.Shape.Layers

#print axioms Johnson.AtFull.Shape.Layers.columnsOfLists
#print axioms Johnson.AtFull.Shape.Layers.fold_lists
#print axioms Johnson.AtFull.Shape.Layers.columnsOf_lists
#print axioms Johnson.AtFull.Shape.Layers.placeLight
#print axioms Johnson.AtFull.Shape.Layers.baseNoFillLight
#print axioms Johnson.AtFull.Shape.Layers.atXLLight
#print axioms Johnson.AtFull.Shape.Layers.atXLC_of_light
