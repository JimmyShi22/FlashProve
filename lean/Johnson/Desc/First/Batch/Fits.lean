-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/Fits.lean (kind K9): THEOREMS: which of the batching draw's twelve tests
can never say no in the block form, at all places and all views.
  entry_tests p: the four tests on the entry hold of the entry that the kind itself states.
  round_tests p r: where the general step function's test on the rounds (roundsFit) has said yes at
    K9's one declared round, the three tests on the round hold.
  draw_eq_drawn p r ..: so, where roundsFit has said yes, K9.draw at the kind's own entry (twelve
    tests) and chiOf, then K9.drawn (five tests) return the same, refusals and their names too.
So in the block form seven of the twelve tests repeat what is a constant or what Block.step has
asked just before: the block's decision does not ask them again. THE BLOCK's DECISION IS STRICTER
THAN K9.draw: it calls K9.drawnClean: K9.drawn's five tests and three more at the empty ledger.
Nothing on soundness.

-/
import Johnson.Desc.First.Batch.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model

/-- K9.entry-name, K9.entry-kind, K9.entry-not-zero, K9.entry-draws. -/
theorem entry_tests (p : Where) :
    ((entry p).name == RoundName.batSigma.name) = true ∧
    (Params.kindOf (entry p).name == some .elems) = true ∧
    ((entry p).drawNZ == 0) = true ∧
    ((entry p).drawE == 1 && (entry p).trits == 0 && (entry p).poss == 0) = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (simp only [entry]; decide)

/-- K9.round-items, K9.round-draws, K9.one-element. -/
theorem round_tests (p : Where) (r : Fmt.RoundView)
    (h : roundsFit [{ entry := entry p }] [r] = true) :
    r.vals.isEmpty = true ∧
    (r.drawn.elems.length == (entry p).drawE && r.drawn.poss.length == (entry p).poss &&
      r.drawn.trits.length == (entry p).trits) = true ∧
    ∃ x, r.drawn.elems = [x] := by
  simp only [roundsFit, Bool.and_eq_true, Bool.and_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hv, he⟩, hp⟩, ht⟩, _⟩, _⟩, _⟩ := h
  have hv' : r.vals.map itemOf = [] := by
    have : (({ entry := entry p } : Fmt.DeclaredRound).items.filter (· != .root)) = [] := by
      simp only [Fmt.DeclaredRound.items, Fmt.Entry.cut, entry]; decide
    rw [this] at hv
    exact eq_of_beq hv
  refine ⟨?_, ?_, ?_⟩
  · cases hr : r.vals with
    | nil => rfl
    | cons a l => rw [hr] at hv'; simp at hv'
  · simp only [Bool.and_eq_true]; exact ⟨⟨he, hp⟩, ht⟩
  · have h1 : r.drawn.elems.length = 1 := eq_of_beq he
    match hq : r.drawn.elems with
    | [x] => exact ⟨x, rfl⟩
    | [] => rw [hq] at h1; simp at h1
    | _ :: _ :: _ => rw [hq] at h1; simp at h1

/-- **Where the format's test on the round has said yes, the two return the same.** -/
theorem draw_eq_drawn (p : Where) (r : Fmt.RoundView) (owed : RowsOwed)
    (used : Nat) (L : LinkCtx) (F : Fork)
    (h : roundsFit [{ entry := entry p }] [r] = true) :
    draw (entry p) r owed used L F =
      (chiOf r).bind fun chi => drawn p.rows chi owed used L F := by
  obtain ⟨e1, e2, e3, e4⟩ := entry_tests p
  obtain ⟨r1, r2, x, hx⟩ := round_tests p r h
  unfold draw drawn chiOf
  rw [e1, e2, e3, e4, r1, r2, hx]
  cases owed <;> rfl

end VerifiableInference.Desc.K9
