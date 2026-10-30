-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/EntryPre.lean: the statement of an entry's chain at two tables with `answers = []`
(`bareStatement`).







Main definition: `bareStatement`.
Main theorem.



- `entryStatement_bare`: for tables with `answers = []` `entryStatement` is `bareStatement`,
  whatever the tables' roots are.




What is not claimed. Nothing on soundness and no probability. No chain is read here; that no hash is
called is true of the text and is no theorem.

Nothing is said of a table with answers.
The program is the Lean port built from OnBytes/; nothing here is said of
the C++ program `cp_verify` or of how its results compare. For proofs only; the program does not
import this file.

-/
import OnBytes.Tie.EntryWith
import OnBytes.Params.EntryRounds
import Run.Toy1TieTree
import Run.CodingPage160

set_option autoImplicit false

namespace OnBytes.Tie

/-- The statement of an entry's chain for two tables with `answers = []`, as a function of the two
roots. -/
def bareStatement (r0 r1 : ByteArray) : ByteArray :=
  Params.Link.statement ⟨r0, []⟩ ⟨r1, []⟩

/-- For tables with `answers = []` `entryStatement` is `bareStatement`. -/
theorem entryStatement_bare (first further : Params.TableName) (h0 : first.answers = [])
    (h1 : further.answers = []) : entryStatement first further = bareStatement := by
  funext r0 r1
  unfold entryStatement bareStatement
  rw [h0, h1]

end OnBytes.Tie
