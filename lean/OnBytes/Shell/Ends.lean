-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Ends.lean: what a run of a program is.

A program (OnBytes/Shell/Ask.lean) is a tree of questions to the outside world. A run of it is a
list of questions with their answers. `q.Ends evs a` says: if the world gives the answers in evs,
the program q asks exactly the questions in evs, in this order, and then stops with the result a.

Main definitions: `Event`, `Ask.Ends`. Theorems: one for each form of a program, which says what
its runs are (`ends_done`, `ends_read`, `ends_say`, `ends_err`). Not claimed: that a program has a
run, or how runs relate to `Ask.run`: for that see OnBytes/Shell/AtOps.lean. For proofs only; the
program does not import this file.
-/
import OnBytes.Shell.Ask

namespace OnBytes.Shell

/-- One step of a run: a question with its answer. -/
inductive Event where
  /-- at most n bytes of the file at path were asked for; `got` is the answer -/
  | read (path : String) (n : Nat) (got : FileRead)
  /-- the line was handed to standard output; ok says whether that succeeded -/
  | say (line : String) (ok : Bool)
  /-- the words were handed to standard error -/
  | err (words : String)

/-- On the answers in the list the program asks exactly the list's questions and stops with a. -/
inductive Ask.Ends {α : Type} : Ask α → List Event → α → Prop where
  /-- a program that is done asks nothing -/
  | done (a : α) : Ask.Ends (.done a) [] a
  /-- a read, and then a run of what follows on its answer -/
  | read {p : String} {n : Nat} {next : FileRead → Ask α} {got : FileRead} {evs : List Event}
      {a : α} (h : Ask.Ends (next got) evs a) : Ask.Ends (.read p n next) (.read p n got :: evs) a
  /-- a printed line, and then a run of what follows on its answer -/
  | say {l : String} {next : Bool → Ask α} {ok : Bool} {evs : List Event} {a : α}
      (h : Ask.Ends (next ok) evs a) : Ask.Ends (.say l next) (.say l ok :: evs) a
  /-- words on standard error, and then a run of what follows -/
  | err {x : String} {next : Ask α} {evs : List Event} {a : α}
      (h : Ask.Ends next evs a) : Ask.Ends (.err x next) (.err x :: evs) a

variable {α : Type}

/-- The only run of a program that is done is the empty one, with its own result. -/
theorem ends_done {a b : α} {evs : List Event} (h : (Ask.done a).Ends evs b) :
    evs = [] ∧ a = b := by
  cases h
  exact ⟨rfl, rfl⟩

/-- A run of a program that begins with a read is that read and a run of what follows. -/
theorem ends_read {p : String} {n : Nat} {next : FileRead → Ask α} {evs : List Event} {a : α}
    (h : (Ask.read p n next).Ends evs a) :
    ∃ got t, evs = .read p n got :: t ∧ (next got).Ends t a := by
  cases h with
  | read h => exact ⟨_, _, rfl, h⟩

/-- A run of a program that begins with a printed line is that line and a run of what follows. -/
theorem ends_say {l : String} {next : Bool → Ask α} {evs : List Event} {a : α}
    (h : (Ask.say l next).Ends evs a) : ∃ ok t, evs = .say l ok :: t ∧ (next ok).Ends t a := by
  cases h with
  | say h => exact ⟨_, _, rfl, h⟩

/-- A run of a program that begins with words on standard error is these and a run of the rest. -/
theorem ends_err {x : String} {next : Ask α} {evs : List Event} {a : α}
    (h : (Ask.err x next).Ends evs a) : ∃ t, evs = .err x :: t ∧ next.Ends t a := by
  cases h with
  | err h => exact ⟨_, rfl, h⟩

end OnBytes.Shell
