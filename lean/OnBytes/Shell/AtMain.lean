-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/AtMain.lean: from the exit code of the program in IO to a run of `call C args`.

`mainIO C args` (OnBytes/Shell/Ops.lean) runs the value `call C args` with the three operations of
the program and returns the exit code of its ending. C holds the checks on a model's files; the
theorems hold for all C.

Main theorems.
- `main_iff`: started in the state s, `mainIO C args` returns the code c and leaves the state s'
  exactly if `call C args` has a run whose answers the three operations gave from s to s' and whose
  ending has the exit code c.
- `main_noThrow`, `main_total`: `mainIO C args` throws in no state, so it returns in every state.
- `status_small`, `main_small`: every exit code is below 256, so it equals itself modulo 256, which
  is what an operating system's shell sees of the number that `main` returns.
- `main_eq` (`OnBytes.Shell.main_eq`; `OnBytes.Guard.main_eq`, OnBytes/Guard/Program.lean, is
  another statement: `main` is `programFront`, by unfolding): the program's entry function is
  `program`, which is `mainIO` with `modelChecks`; so the theorems above speak of it. Not by
  unfolding: `main` calls `programFront` (OnBytes/Shell/Front.lean), and that is `program` by
  `programFront_eq` (OnBytes/Shell/FrontSame.lean), which rests on four equations of
  OnBytes/ChecksWithHashAsArgument/M/AtPort/Spine.lean.

What is not claimed. Nothing about compiled code, Lean's run-time or the operating system: the
theorems are about the terms that Lean's kernel checks. In particular `main_total` does not say
that the real program ends: it says that the term throws no exception in Lean's model of IO.
Theorems only; the program does not import this file.
-/
import OnBytes.Shell.AtOps
import OnBytes.Main
import OnBytes.Shell.FrontSame

namespace OnBytes.Shell

/-- The driver with the program's three operations throws in no state. -/
theorem noThrow_call (C : Checks) (args : List String) : NoThrow ((call C args).run opsIO) :=
  noThrow_run readIO_noThrow outIO_noThrow errIO_noThrow _

/-- The program in IO returns c exactly if the program as a value has a run whose answers the three
operations gave and whose ending has the exit code c. -/
theorem main_iff (C : Checks) (args : List String) (s s' : World) (c : UInt32) :
    Run (mainIO C args) s c s' ↔
      ∃ evs r, (call C args).Ends evs r ∧ Steps opsIO evs s s' ∧ r.status = c := by
  constructor
  · intro h
    obtain ⟨r, s1, h1, h2⟩ := (run_bind
      (x := tryCatch ((call C args).run opsIO) fun _ => pure Ending.fault)
      (f := fun e => pure e.status)).1 h
    obtain ⟨h3, rfl⟩ := run_pure.1 h2
    rcases run_try.1 h1 with h4 | ⟨e, s2, h4, _⟩
    · obtain ⟨evs, h5, h6⟩ := (Ask.run_iff opsIO (call C args) s r s1).1 h4
      exact ⟨evs, r, h5, h6, h3⟩
    · exact absurd h4 (noThrow_call C args s e s2)
  · rintro ⟨evs, r, h1, h2, rfl⟩
    exact (run_bind (x := tryCatch ((call C args).run opsIO) fun _ => pure Ending.fault)
      (f := fun e => pure e.status)).2
      ⟨r, s', run_try.2 (Or.inl ((Ask.run_iff opsIO (call C args) s r s').2 ⟨evs, h1, h2⟩)),
        run_pure.2 ⟨rfl, rfl⟩⟩

/-- The program in IO throws in no state. -/
theorem main_noThrow (C : Checks) (args : List String) : NoThrow (mainIO C args) :=
  noThrow_bind (x := tryCatch ((call C args).run opsIO) fun _ => pure Ending.fault)
    (f := fun e => pure e.status) (noThrow_try fun _ => noThrow_pure _) fun _ => noThrow_pure _

/-- The program in IO returns in every state. -/
theorem main_total (C : Checks) (args : List String) (s : World) :
    ∃ c s', Run (mainIO C args) s c s' :=
  run_of_noThrow (main_noThrow C args) s

/-- The exit code of every ending is below 256. -/
theorem status_small (r : Ending) : r.status.toNat < 256 := by
  cases r with
  | ended e => cases e <;> simp only [Ending.status, Model.Stages.CallEnd.status] <;> decide
  | _ => decide

/-- Whatever `mainIO C args` returns is below 256. -/
theorem main_small {C : Checks} {args : List String} {s s' : World} {c : UInt32}
    (h : Run (mainIO C args) s c s') : c.toNat < 256 := by
  obtain ⟨_, r, _, _, rfl⟩ := (main_iff C args s s' c).1 h
  exact status_small r

/-- The entry function is `program`: it is `programFront` by unfolding, and that is `program` by
`programFront_eq`. -/
theorem main_eq : _root_.main = program := programFront_eq

end OnBytes.Shell

#print axioms OnBytes.Shell.main_iff
#print axioms OnBytes.Shell.main_total
#print axioms OnBytes.Shell.main_small
#print axioms OnBytes.Shell.main_eq
