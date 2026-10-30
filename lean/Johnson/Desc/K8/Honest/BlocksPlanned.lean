-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/BlocksPlanned.lean: THE SMALLNESS TEST: THE THREE FACTS ON THE BLOCKS OF THE
DIGITS' ROWS THAT Johnson/Desc/K8/Honest/BlocksCount.lean TAKES AS PREMISES (the data's blocks are
the loop's at the data's number of combinations · not none · at most two) HOLD OF WHATEVER THE
VERIFIER's OWN MAKER OF THE TEST's DATA RETURNS (`HTailF2.shapeF`, by its last step `piecesF`;
OnBytes/Model/Tail.lean). So at such data the verifier's two computations of the number of blocks
agree. Lemmas on the verifier's own text; none of the library's goals.

  **`pieces_blocks`**   tl0.piecesF = .ok tl → t2BL tl.tau = .ok tl.blocks ∧ tl.blocks.size ≠ 0 ∧
                   tl.blocks.size ≤ 2
  **`shape_blocks`**   tl0.shapeF m txOf f hasU tau = .ok tl → the same: by the library's
                   `shapeF_pieces`: a yes of shapeF is a yes of piecesF
                   (OnBytes/Tie/Pv/Lookup/Ends/FoZMade.lean)
  **`shape_wants`**   so there: tl.wants = some (nbW, W) → nbW = tl.zzBlocks
Limits. AT WHAT THE MAKER RETURNS ALONE: that a later routine of a plan (the list of arrays; the
owner's record) and the runs of a segment leave tau and the blocks, and that a state's data come of
a plan, is not shown here.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.BlocksCount
import OnBytes.Tie.Pv.Lookup.Ends.FoZMade
import OnBytes.Tie.Pv.Lookup.Ends.ShapePrem

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model

/-- **What the last step of the maker returns.** -/
theorem pieces_blocks {tl0 tl : HTailF2} (h : tl0.piecesF = .ok tl) :
    t2BL tl.tau = .ok tl.blocks ∧ tl.blocks.size ≠ 0 ∧ tl.blocks.size ≤ 2 := by
  unfold HTailF2.piecesF at h
  obtain ⟨bz, hb, h⟩ := Ends.ok_of_bind h
  obtain ⟨hc, h⟩ := Ends.ok_of_jp h
  obtain ⟨_, h⟩ := Ends.ok_of_jp h
  obtain ⟨f9, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨pub, _, h⟩ := Ends.ok_of_bind h
  obtain ⟨_, _, h⟩ := Ends.ok_of_bind h
  have e := (Except.ok.inj h).symm
  subst e
  have hc' : ¬ (bz.isEmpty = true ∨ 2 < bz.size) := by
    intro hh
    apply hc
    rcases hh with h1 | h1
    · simp [h1]
    · simp [h1]
  refine ⟨hb, fun h0 => hc' (Or.inl ?_), ?_⟩
  · exact Array.isEmpty_iff_size_eq_zero.2 h0
  · exact Nat.le_of_not_lt fun h2 => hc' (Or.inr h2)

/-- **What the maker returns.** -/
theorem shape_blocks {tl0 tl : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl0.shapeF m txOf f hasU tau = .ok tl) :
    t2BL tl.tau = .ok tl.blocks ∧ tl.blocks.size ≠ 0 ∧ tl.blocks.size ≤ 2 := by
  obtain ⟨tl1, h1⟩ := Fo.ZPlan.shapeF_pieces h
  exact pieces_blocks h1

/-- **So there the second computation's number of blocks is the plan's.** -/
theorem shape_wants {tl0 tl : HTailF2} {m : Array TMat} {txOf : Array (Option Nat)}
    {f : Array T2Foreign} {hasU : Array Bool} {tau : Nat}
    (h : tl0.shapeF m txOf f hasU tau = .ok tl) :
    ∀ nbW W, tl.wants = some (nbW, W) → nbW = tl.zzBlocks :=
  wants_blocks tl (shape_blocks h).1 (shape_blocks h).2.1 (shape_blocks h).2.2

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.pieces_blocks
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_blocks
#print axioms VerifiableInference.Desc.First.K8.Honest.shape_wants
