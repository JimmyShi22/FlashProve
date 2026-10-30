-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryCheckLaws.lean: what it says that `entryCheck`
(OnBytes/ShellOf/EntryCheck.lean) returns without an exception. For proofs only: no program imports
it.

  `entryCheck_main`: then the program returned the exit code 0, between the same two states.
  `entryCheck_returns`: so all that `entryMain_zero` (OnBytes/ShellOf/EntryProgLaws.lean) says.

What is not claimed: all that the head of OnBytes/ShellOf/EntryProgLaws.lean does not claim. In
Lean's model of IO; nothing on how Lean's command line turns an exception into an exit code.

-/
import OnBytes.ShellOf.EntryCheck
import OnBytes.ShellOf.EntryProgLaws

set_option autoImplicit false

namespace OnBytes.ShellOf.EntryProg

open TypedOracleCompiler.Slice (verifyEntryFull verifyEntrySmall)
open OnBytes.Shell (World run_bind run_pure)

/-- If `entryCheck` returns, the program returned the exit code 0, between the same two states. -/
theorem entryCheck_main {args : List String} {s s' : World}
    (h : Shell.Run (entryCheck args) s () s') : Shell.Run (entryMain args) s 0 s' := by
  obtain ⟨c, s1, h1, h2⟩ := run_bind.1 h
  by_cases hc : c = 0
  · subst hc
    rw [if_pos rfl] at h2
    obtain ⟨-, rfl⟩ := run_pure.1 h2
    exact h1
  · rw [if_neg hc] at h2
    have h3 : (EST.Out.error (IO.userError ("NOT A YES: the program's exit code is " ++ toString c))
        s1 : EST.Out IO.Error IO.RealWorld Unit) = EST.Out.ok () s' := h2
    cases h3

/-- IF `entryCheck` RETURNS WITHOUT AN EXCEPTION: all that the exit code 0 says. -/
theorem entryCheck_returns {args : List String} {s s' : World}
    (h : Shell.Run (entryCheck args) s () s') :
    (∃ r, args = "full" :: r ∧ ZeroSays verifyEntryFull Tie.recordGround.q.link.table Params.stdFull
      (parseE Tie.recordGround Params.stdFull)
      (givesO Tie.recordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') ∨
    (∃ r, args = "small" :: r ∧ ZeroSays verifyEntrySmall Tie.smallRecordGround.q.link.table
      Params.stdSmall (parseE Tie.smallRecordGround Params.stdSmall)
      (givesO Tie.smallRecordGround.q.link.table _root_.Fmt.oracle) _root_.Run.oBits r s s') :=
  entryMain_zero (entryCheck_main h)

end OnBytes.ShellOf.EntryProg
