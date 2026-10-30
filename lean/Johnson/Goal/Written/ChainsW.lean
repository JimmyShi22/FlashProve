-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Written/ChainsW.lean: the routine that makes the seven chains with the written value of
the full size in the planner's place (`chainsOfW`, Johnson/G/ChainsWritten.lean, at `writtenMade`,
Johnson/Goal/Written/Made.lean); and under which premises it returns the planner's chains to the
letter.

What it is for: a brick for a description that takes the plan as data. The routine: no other caller.

Definitions.
  `pickWritten small l`: which written value goes with the parameter file's lines: `writtenMade`
    with `recordLines`; the letter small with `smallRecordLines`
    (OnBytes/Params/EntryStagesRecordSmall.lean): no written value of the small example lies yet;
    nothing with any other lines.
  `chainsW small`: `chainsOfW shapesOf (pickWritten small)`.
Statements and proofs.
  `pick_full`, `pick_other`: what the picking gives at the written lines of the full size, and at
    lines that are neither of the two.
  `free_of_sized`: a record that `configure` returns, with the written sizes and the proof file's
    first written plan, has `writtenMade` as its four fields. From `sixOfSized`
    (Johnson/Goal/Written/MadeOfSized.lean).
  `chainsW_of`: if `chainsOf X lay cfg` returns ch, the lines are `recordLines`, ch's sizes are
    `writtenSized` and the first plan of its proof file is the written one, then `chainsW small X
    lay cfg` returns ch.
  `chainsW_other`: at lines that are neither of the two it refuses, wherever the shapes are made.

What of OnBytes/Model/ is used: `Verify.Public`, `Verify.Chains`, `Verify.chainsOf`,
`Verify.shapesOf`.

Limits. Two premises of `chainsW_of` are shown of no public files: that the planner's sizes of the
proof file are the written ones, and that its first plan of the proof file is the written one; both
hang on the run's shapes. The proof file's written plans stand on prints of the library's own
planner (see the head of Johnson/Desc/Ok/NumberPrices/ProofAtWritten.lean). The limits of
ChainsWritten.lean hold here. Nothing on soundness.
-/
import Johnson.G.ChainsWritten
import Johnson.G.PlansPriced
import Johnson.Goal.Written.MadeOfSized
import OnBytes.Params.EntryStagesRecordSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten.Joined
open VerifiableInference VerifiableInference.Number.ByRuns
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages
open Johnson.G Johnson.G.MadeFree

/-- Which written value goes with the parameter file's lines. small: the small example's. -/
def pickWritten (small : Option Free) (l : Lines) : Option Free :=
  if l = recordLines then some writtenMade else if l = smallRecordLines then small else none

/-- The seven chains, with the written values in the planner's place. -/
def chainsW (small : Option Free) (X : Public) (layoutFile : Option ByteArray)
    (cfg : ByteArray) : Except String Chains :=
  chainsOfW shapesOf (pickWritten small) X layoutFile cfg

theorem pick_full (small : Option Free) : pickWritten small recordLines = some writtenMade :=
  if_pos rfl

theorem pick_other (small : Option Free) {l : Lines} (h1 : l ≠ recordLines)
    (h2 : l ≠ smallRecordLines) : pickWritten small l = none := by
  unfold pickWritten
  rw [if_neg h1, if_neg h2]

/-- A record that `configure` returns, with the written sizes and the proof file's first written
plan, has the written value as its four fields. -/
theorem free_of_sized {l : Lines} {x : Shapes} {cfg : ByteArray} {bits : ℕ} {made : Configured}
    (h : configure l x cfg bits = .ok made) (hs : made.sized = writtenSized)
    (hF : made.proof.head? = some proofThree.A.plan) : freeOf made = writtenMade := by
  obtain ⟨hk, he, F, hp, _⟩ := sixOfSized l x cfg bits made h hs
  rw [hp] at hF
  have eF : F = proofThree.A.plan := Option.some.inj hF
  show (⟨made.sized, made.proof, made.key, made.entry⟩ : Free) = writtenMade
  rw [hs, hp, hk, he, eF]
  rfl

/-- **Where the planner makes the written value, the routine returns the planner's chains.** -/
theorem chainsW_of {small : Option Free} {X : Public} {layoutFile : Option ByteArray}
    {cfg : ByteArray} {ch : Chains} (h : chainsOf X layoutFile cfg = .ok ch)
    (hl : X.P.frame = recordLines) (hs : ch.made.sized = writtenSized)
    (hF : ch.made.proof.head? = some proofThree.A.plan) :
    chainsW small X layoutFile cfg = .ok ch := by
  obtain ⟨l, x, hc, _⟩ := OfPlan.chainsOf_made h
  refine chainsOfW_of (sh := shapesOf) (h := h) ?_
  rw [hl, pick_full, free_of_sized hc hs hF]

/-- At lines that are neither of the two it refuses. -/
theorem chainsW_other {small : Option Free} {X : Public} {layoutFile : Option ByteArray}
    {cfg : ByteArray} {links : Array LinkH} {shapes : Params.Shapes}
    (hsh : shapesOf X layoutFile = .ok (links, shapes)) (h1 : X.P.frame ≠ recordLines)
    (h2 : X.P.frame ≠ smallRecordLines) :
    chainsW small X layoutFile cfg = .error notAdmitted :=
  chainsOfW_no_pick hsh (pick_other small h1 h2)

end VerifiableInference.PlanWritten.Joined

#print axioms VerifiableInference.PlanWritten.Joined.pick_full
#print axioms VerifiableInference.PlanWritten.Joined.pick_other
#print axioms VerifiableInference.PlanWritten.Joined.free_of_sized
#print axioms VerifiableInference.PlanWritten.Joined.chainsW_of
#print axioms VerifiableInference.PlanWritten.Joined.chainsW_other
