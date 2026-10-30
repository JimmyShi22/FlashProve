-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/RangeChecksReturn.lean: A REQUEST's RANGE CHECKS (`Model.Verify.rangeChecksOf`,
OnBytes/Model/VerifySubproofs.lean) RETURN, FORWARD; AND THEY ARE THE WRITTEN LIST `checksFull`
(Johnson/AtFull/Made/GateChecks.lean) WHERE EACH OF THE 25 SMALLNESS TESTS HAS THE
WRITTEN CHECKS. Laws by unfolding, and one closed equation of lists. A law file; no running text
imports it. Nothing on codes.

What it is for. `rangeChecksOf X = some rc` is the first step of `shapesWith` (the premise hc of
`shapes_and_sizes`, Johnson/AtFull/Made/ShapesReturn.lean), and rc is what the planner's fourth gate
reads (`ShapesRead.checks`, Johnson/AtFull/Made/Gates.lean).

  `mapM_some`, `checksH_append`, `checksH_flatten`: tools. `pairAt X g`: the two smallness tests of
    group g.
  `rangeChecksOf_of`: **forward, at every X of profile 4**: each group's two plans are there ⊢
    rangeChecksOf X = some (the groups' checks in order, then the head's).
  `checksFull_split`: the written list is twelve times (nine and five) and eight. IT WOULD HOLD AT
    EVERY CUT OF THE FOURTEEN: that the layers' test ends behind the ninth check is borne by the
    premises of `rangeChecks_written` alone.
  `rangeChecks_written`: p4 · twelve groups · at each g a layers' plan whose test has the pair's
    first nine checks and an attention's plan whose test has its last five · the head's test has the
    head's eight ⊢ rangeChecksOf X = some checksFull. A VALUE.

WHAT IS READ OF A SMALLNESS TEST: its matrices' rows and columns, in order, and tau (`rangeCheckOf`,
OnBytes/Model/VerifyHiding.lean). That is more than an arm holds: an arm has the sum of the columns.

Limits. THE PREMISES ARE PREMISES: shown at no files. `checksFull` was copied off a run (that file's
head). The full size alone. Nothing on soundness.

-/
import Johnson.AtFull.Made.GateChecks
import OnBytes.Model.VerifySubproofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify

/-! ## 1 Tools -/

/-- Where a step returns a named value at each member, the walk returns the list of these. -/
theorem mapM_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ l : List α, (∀ a ∈ l, f a = some (g a)) → l.mapM f = some (l.map g)
  | [], _ => rfl
  | a :: l, h => by
    rw [List.mapM_cons, h a (List.mem_cons_self ..),
      mapM_some f g l fun b hb => h b (List.mem_cons_of_mem _ hb)]
    rfl

theorem checksH_append (a b : List HTailF2) :
    rangeChecksH (a ++ b) = rangeChecksH a ++ rangeChecksH b := by
  unfold rangeChecksH
  exact List.flatMap_append ..

theorem checksH_flatten : ∀ L : List (List HTailF2),
    rangeChecksH L.flatten = L.flatMap rangeChecksH
  | [] => rfl
  | a :: L => by
    rw [List.flatten_cons, checksH_append, checksH_flatten L, List.flatMap_cons]

/-! ## 2 The range checks of a request, forward -/

/-- The two smallness tests of group g; nothing where a plan is missing. -/
def pairAt (X : Public) (g : Nat) : List HTailF2 :=
  match X.G[g]?, X.A[g]? with
  | some hp, some a => [hp.tl, a.seam.tl]
  | _, _ => []

/-- **The range checks, forward**: at profile 4, where each group's two plans are there. -/
theorem rangeChecksOf_of {X : Public} (h4 : X.p4 = true)
    (hG : ∀ g, g < X.NGr → (X.G[g]?).isSome = true ∧ (X.A[g]?).isSome = true) :
    rangeChecksOf X =
      some ((List.range X.NGr).flatMap (fun g => rangeChecksH (pairAt X g)) ++
        rangeChecksH [X.H.tl]) := by
  have e : (List.range X.NGr).mapM (closingPartsOf X) =
      some ((List.range X.NGr).map (pairAt X)) := by
    refine mapM_some _ _ _ fun g hg => ?_
    obtain ⟨a1, a2⟩ := hG g (List.mem_range.1 hg)
    unfold closingPartsOf pairAt
    cases e1 : X.G[g]? with
    | none =>
      rw [e1] at a1
      cases a1
    | some hp =>
      cases e2 : X.A[g]? with
      | none =>
        rw [e2] at a2
        cases a2
      | some a =>
        show some (if X.p4 = true then [hp.tl, a.seam.tl] else [hp.tl]) = _
        rw [if_pos h4]
  unfold rangeChecksOf closingParts
  rw [e]
  show some (rangeChecksH (((List.range X.NGr).map (pairAt X)).flatten ++ [X.H.tl])) = _
  rw [checksH_append, checksH_flatten, List.flatMap_map]

/-! ## 3 At the written list -/

set_option maxRecDepth 1000000 in
/-- Twelve times the pair's fourteen, and the head's eight, are the written list. -/
theorem checksFull_split :
    (List.range 12).flatMap (fun _ => checksPair.take 9 ++ checksPair.drop 9) ++ checksHead =
      checksFull := by
  decide +kernel

/-- **The range checks are the written list**, where each of the 25 smallness tests has the
written checks. -/
theorem rangeChecks_written {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (hL : ∀ g, g < 12 → ∃ hp, X.G[g]? = some hp ∧ rangeChecksH [hp.tl] = checksPair.take 9)
    (hA : ∀ g, g < 12 → ∃ a, X.A[g]? = some a ∧ rangeChecksH [a.seam.tl] = checksPair.drop 9)
    (hH : rangeChecksH [X.H.tl] = checksHead) : rangeChecksOf X = some checksFull := by
  rw [rangeChecksOf_of h4 fun g hg => by
    rw [hN] at hg
    obtain ⟨hp, e1, _⟩ := hL g hg
    obtain ⟨a, e2, _⟩ := hA g hg
    rw [e1, e2]
    exact ⟨rfl, rfl⟩, hN, hH, ← checksFull_split]
  congr 2
  refine List.flatMap_congr fun g hg => ?_
  obtain ⟨hp, e1, c1⟩ := hL g (List.mem_range.1 hg)
  obtain ⟨a, e2, c2⟩ := hA g (List.mem_range.1 hg)
  unfold pairAt
  rw [e1, e2]
  show rangeChecksH ([hp.tl] ++ [a.seam.tl]) = _
  rw [checksH_append, c1, c2]

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.mapM_some
#print axioms Johnson.AtFull.Made.checksH_append
#print axioms Johnson.AtFull.Made.checksH_flatten
#print axioms Johnson.AtFull.Made.rangeChecksOf_of
#print axioms Johnson.AtFull.Made.checksFull_split
#print axioms Johnson.AtFull.Made.rangeChecks_written
