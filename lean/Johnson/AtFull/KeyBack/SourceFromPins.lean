-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/KeyBack/SourceFromPins.lean: `Key.sourceOf m` returns at every m that has the full
size's written values, and its declared rounds are the written declared rounds.

Calls alone: `sourceOf_at_pins` (SourceAtPins.lean), at `treesK_at_pins` (TreesKAtPins.lean) and at
the two closed facts `fills_run` (FillsAtRun.lean) and `closes_run` (ClosesAtRun.lean), carried to
the trees' own terms by `trees_A`, `trees_B`, `trees_C` (TreesAtKey.lean).

  `sourceOf_from_pins`: from `KeyPins m` alone: the answer is `sourceAt m declKeyFull T`, where T is
    what `toldOfMade m` returns.
  `sourceOf_returns_from_pins`: so `sourceOf m` returns.

Limits. THAT `KeyPins` HOLDS AT ANY m IS NOT SHOWN: so that `sourceOf` returns at any m
is not shown here. Of T only that it is returned: which tenants and which groups it holds
is not said. That the written values are the planner's at any public files is not said.
Nothing on soundness, nothing on hiding.

-/
import Johnson.AtFull.KeyBack.SourceAtPins
import Johnson.AtFull.KeyBack.TreesKAtPins
import Johnson.AtFull.KeyBack.FillsAtRun
import Johnson.AtFull.KeyBack.ClosesAtRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack
open Johnson.G.OfPlan
open VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

/-- **`sourceOf` from the pins alone**: it returns, and its declared rounds are the written
value. -/
theorem sourceOf_from_pins (m : Made) (h : KeyPins m) :
    ∃ T, toldOfMade m = .ok T ∧ sourceOf m = .ok (sourceAt m declKeyFull T) :=
  sourceOf_at_pins m h _ _ _ (treesK_at_pins m h)
    (by rw [trees_A, trees_B, trees_C]; exact fills_run)
    (by rw [trees_A, trees_B, trees_C]; exact closes_run)

/-- So `sourceOf` returns. -/
theorem sourceOf_returns_from_pins (m : Made) (h : KeyPins m) : ∃ X, sourceOf m = .ok X := by
  obtain ⟨_, _, hs⟩ := sourceOf_from_pins m h
  exact ⟨_, hs⟩

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.sourceOf_from_pins
#print axioms Johnson.AtFull.KeyBack.sourceOf_returns_from_pins
