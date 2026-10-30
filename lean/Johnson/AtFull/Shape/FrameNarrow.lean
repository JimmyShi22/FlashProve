-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/FrameNarrow.lean: A GUARD IN FRONT OF A STEP ON SHAPES KEEPS `Carries`
(Johnson/Desc/ProofFile/Honest/Thread/Shape.lean), at the frame's letters `firstZA G vals`
(Johnson/AtFull/Shape/FrameForm.lean). Three small general laws: no head, no kind, no member's
number.

Why. `Carries` at a member takes "the step on shapes returns" as a premise. So a table of steps that
returns at that member only where another table does, and then the same shape, has `Carries` there
if the other has. A guard on the shape that "returns" needs, and that the step itself does not ask,
can so be laid in front of the step.

Main names.
* `carries_narrow`: the law, for two tables G and G' and any two tables of tests on values.
* `optE_guard`: where `optE` (Johnson/AtFull/Shape/FrameOpt.lean) of "if c accepts then f, else
  nothing" returns, c accepts and `optE f` returns the same.
* `carries_behind_guard`: so `Carries` at a member whose step is `optE f` gives `Carries` at the
  same member with the guard c in front.

Limits. It says nothing on where a guarded step returns: a guard that never accepts makes `Carries`
empty, and stops the run on shapes. Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.FrameOpt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest (Carries)

/-- **A table that returns only where another does, and then the same, keeps "Carries".** -/
theorem carries_narrow {Cl : Type} {bs : List (Block S Cl)} {ft n : Nat}
    {G G' : Nat → ShA → Except String ShA}
    {vals vals' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
    (hn : ∀ y u, G n y = .ok u → G' n y = .ok u)
    (hc : Carries bs ft (firstZA G' vals') n) : Carries bs ft (firstZA G vals) n :=
  fun blk hb s rs cols s' k t hs hg => hc blk hb s rs cols s' k t hs (hn _ _ hg)

/-- Where a guarded step returns, the guard accepts and the bare step returns the same. -/
theorem optE_guard {α β : Type} {c : α → Bool} {f : α → Option β} {y : α} {u : β}
    (h : optE (fun y => if c y then f y else none) y = .ok u) :
    c y = true ∧ optE f y = .ok u := by
  have k := optE_ok.1 h
  by_cases hc : c y = true
  · rw [if_pos hc] at k
    exact ⟨hc, optE_ok.2 k⟩
  · rw [if_neg hc] at k
    cases k

/-- **A guard in front keeps "Carries".** -/
theorem carries_behind_guard {Cl : Type} {bs : List (Block S Cl)} {ft n : Nat}
    {G G' : Nat → ShA → Except String ShA}
    {vals vals' : Nat → S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool}
    (c : ShA → Bool) (f : ShA → Option ShA)
    (hG : G n = optE fun y => if c y then f y else none) (hG' : G' n = optE f)
    (hc : Carries bs ft (firstZA G' vals') n) : Carries bs ft (firstZA G vals) n :=
  carries_narrow (fun y u h => by rw [hG] at h; rw [hG']; exact (optE_guard h).2) hc

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.carries_narrow
#print axioms Johnson.AtFull.Shape.optE_guard
#print axioms Johnson.AtFull.Shape.carries_behind_guard
