-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ShellOf/EntryCheck.lean: the program for the entry file's part
(OnBytes/ShellOf/EntryProg.lean) in a form that THROWS unless the verdict is a yes. One definition;
its law is in OnBytes/ShellOf/EntryCheckLaws.lean.

Why. Where a term of type `IO UInt32` is evaluated by Lean itself (`#eval`), the number that it
returns is printed and Lean's own exit code stays 0: "the command succeeded" would then say nothing.
An exception makes Lean's evaluation fail. That Lean's exit code follows is a fact of Lean's command
line, seen in a run, not a theorem.

What is not claimed: all that the head of OnBytes/ShellOf/EntryProg.lean does not claim.

-/
import OnBytes.ShellOf.EntryProg

set_option autoImplicit false

namespace OnBytes.ShellOf.EntryProg

/-- The program, then: the code 0 returns; every other code is thrown, as words. -/
def entryCheck (args : List String) : IO Unit :=
  entryMain args >>= fun c =>
    if c = 0 then pure ()
    else throw (IO.userError ("NOT A YES: the program's exit code is " ++ toString c))

end OnBytes.ShellOf.EntryProg
