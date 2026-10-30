-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Scope/ScopeLines.lean: in the goals' scope the reader of the parameter file's first 32
lines gives one fixed record of lines, whatever stands behind them. The full size alone: the scope
pins the stored full-size example's 32 lines; nothing here speaks of the small examples.

This file adds little. In the library, and only used here: the frame law `keeps_lines`
(OnBytes/K/Left/SaysLinesPrefix.lean): where the reader gives a value and leaves t' on a text t, it
gives the same value and leaves t' ++ u on t ++ u; and `toList_data` of the same file. That file's
`full_says_of_prefix` already says that every file that begins with the library's own copy of the 32
lines (`TestSaysLines.full32`) is read as the full-size ground's lines; it does not say what is
handed on, and it speaks of that copy, not of `VerifierAndGoals.lines32`.

Main names:
  `lines_at32`: on `VerifierAndGoals.lines32` alone the reader gives `Params.recordLines` and leaves nothing.
    Decided once by Lean's kernel (`decide +kernel`, as `TestSaysLines.full_says`).
  `lines_tail`: so with any bytes t behind the 32 lines it gives the same lines and leaves t.
  `readLines_tail`: readLines (textOf lines32 ++ b) = .ok (recordLines, b).
  `readLines_policy`: every `VerifierAndGoals.policyFile v` is the 32 lines with some bytes b behind them, and
    is read so.
  `inScope_files`: InScope Z = true gives v with Z.pol = policyFile v, and Z.lay = storedPublicFiles.lay.
  `inScope_reads`: InScope Z = true gives b with readLines Z.pol = .ok (recordLines, b).
  `inScope_reads_ground`: the same at `recordGround.lines`, which is `recordLines` by unfolding.
  `inScope_reads_at`: `inScope_reads` with its b tied: Z.pol = textOf lines32 ++ b.
  `inScope_at`: at the settings pp that the goals' reader gives: Z.pol = policyFile (freeLinesOf pp)
    and Z.lay = storedPublicFiles.lay and 2 ^ 8 ≤ pp.pol.theta: all that `InScope` says.
  `lines32_eq`: `VerifierAndGoals.lines32` is the library's copy `TestSaysLines.full32`; and by it and
    `full_says_of_prefix`, `inScope_says`: in scope the full-size ground's `SaysLines` holds.
The record of lines is `OnBytes.Params.recordLines`
(OnBytes/Params/EntryStagesRecord.lean): no term is written a second time.

Limits: one way: nothing on a file that is out of scope. Nothing on what the bytes behind the 32
lines say, on the scale file, or on the planner. That a shipped parameter file is in scope is not
shown here. Nothing on soundness.


-/
import Ladder
import OnBytes.K.Left.SaysLinesPrefix

set_option autoImplicit false

namespace Johnson.G.ScopeLines
open OnBytes OnBytes.Params OnBytes.K.Left
open OnBytes.Tie.Pv.Plan (textOf)

/-- On the 32 lines alone the reader gives the full-size record's lines and leaves nothing. Once, by
Lean's kernel. -/
theorem lines_at32 : lines (textOf VerifierAndGoals.lines32).toList = .ok (recordLines, []) := by
  have h : (lines (textOf VerifierAndGoals.lines32).toList).toOption = some (recordLines, []) := by
    decide +kernel
  cases hl : lines (textOf VerifierAndGoals.lines32).toList with
  | error e =>
    rw [hl] at h
    cases h
  | ok p =>
    rw [hl] at h
    exact congrArg Except.ok (Option.some.inj h)

/-- **The reader of the 32 lines does not look behind them**, at lists of bytes. -/
theorem lines_tail (t : List UInt8) :
    lines ((textOf VerifierAndGoals.lines32).toList ++ t) = .ok (recordLines, t) :=
  keeps_lines _ _ t _ lines_at32

/-- **The same of `readLines`**: the 32 lines with any bytes b behind them are read as the full-size
record's lines, and b is handed on. -/
theorem readLines_tail (b : ByteArray) :
    readLines (textOf VerifierAndGoals.lines32 ++ b) = .ok (recordLines, b) := by
  have e : (textOf VerifierAndGoals.lines32 ++ b).toList = (textOf VerifierAndGoals.lines32).toList ++ b.toList := by
    rw [toList_data, toList_data, toList_data, ByteArray.data_append, Array.toList_append]
  unfold readLines
  rw [e, lines_tail, toList_data]
  rfl

/-- Every parameter file of the goals' family is the 32 lines with some bytes behind them, and is
read so. -/
theorem readLines_policy (v : VerifierAndGoals.FreeLines) :
    ∃ b, VerifierAndGoals.policyFile v = textOf VerifierAndGoals.lines32 ++ b ∧
      readLines (VerifierAndGoals.policyFile v) = .ok (recordLines, b) :=
  ⟨_, rfl, readLines_tail _⟩

/-- What the scope says of two of the three files. -/
theorem inScope_files {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    (∃ v, Z.pol = VerifierAndGoals.policyFile v) ∧ Z.lay = VerifierAndGoals.storedPublicFiles.lay := by
  unfold VerifierAndGoals.InScope at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, of_decide_eq_true h1⟩
  split at h2
  · rw [Bool.and_eq_true] at h2
    exact ⟨_, of_decide_eq_true h2.1⟩
  · cases h2

/-- **In scope the 32 lines are read as one fixed record.** -/
theorem inScope_reads {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    ∃ b, readLines Z.pol = .ok (recordLines, b) := by
  obtain ⟨⟨v, hv⟩, _⟩ := inScope_files h
  obtain ⟨b, _, hb⟩ := readLines_policy v
  exact ⟨b, hv ▸ hb⟩

/-- The same at the full-size ground's field, which is `recordLines` by unfolding. -/
theorem inScope_reads_ground {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    ∃ b, readLines Z.pol = .ok (OnBytes.Tie.recordGround.lines, b) :=
  inScope_reads h

/-- `inScope_reads` with its b tied to the file: for whoever goes on to what is read of the rest. -/
theorem inScope_reads_at {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    ∃ b, Z.pol = textOf VerifierAndGoals.lines32 ++ b ∧ readLines Z.pol = .ok (recordLines, b) := by
  obtain ⟨⟨v, hv⟩, _⟩ := inScope_files h
  obtain ⟨b, hb, hr⟩ := readLines_policy v
  exact ⟨b, hv.trans hb, hv ▸ hr⟩

/-- All that the scope says, at the settings that the goals' reader gives. -/
theorem inScope_at {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (h : VerifierAndGoals.InScope Z = true)
    (hr : VerifierAndGoals.readFiles Z = .ok pp) :
    Z.pol = VerifierAndGoals.policyFile (VerifierAndGoals.freeLinesOf pp) ∧ Z.lay = VerifierAndGoals.storedPublicFiles.lay ∧
      2 ^ 8 ≤ pp.pol.theta := by
  unfold VerifierAndGoals.InScope at h
  rw [hr] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.2.1, h.1, h.2.2⟩

/-- The goals' file's copy of the 32 lines is the library's copy. -/
theorem lines32_eq : VerifierAndGoals.lines32 = TestSaysLines.full32 := by decide

/-- In scope the one test on a parameter file that the theorems of OnBytes/K/Left/ ask holds at the
full-size ground: by `full_says_of_prefix`. -/
theorem inScope_says {Z : VerifierAndGoals.PublicFiles} (h : VerifierAndGoals.InScope Z = true) :
    OnBytes.Tie.recordGround.SaysLines Z.pol := by
  obtain ⟨b, hb, _⟩ := inScope_reads_at h
  rw [hb, lines32_eq]
  exact full_says_of_prefix b

end Johnson.G.ScopeLines

#print axioms Johnson.G.ScopeLines.lines_at32
#print axioms Johnson.G.ScopeLines.lines_tail
#print axioms Johnson.G.ScopeLines.readLines_tail
#print axioms Johnson.G.ScopeLines.readLines_policy
#print axioms Johnson.G.ScopeLines.inScope_files
#print axioms Johnson.G.ScopeLines.inScope_reads
#print axioms Johnson.G.ScopeLines.inScope_reads_ground
#print axioms Johnson.G.ScopeLines.inScope_reads_at
#print axioms Johnson.G.ScopeLines.inScope_at
#print axioms Johnson.G.ScopeLines.lines32_eq
#print axioms Johnson.G.ScopeLines.inScope_says
