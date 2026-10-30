-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Reads.lean: the quiet step behind an attention segment's sending of its reads, whole,
as one plain function on data, with the tables made by Att/Tables.lean.

In OnBytes/Model's order: the list of tables is open (Attention.lean:217); the tables
(AttentionTables.lean:277); the list is closed (Attention.lean:219; Tail.lean:646-647); the list is
closed, one shape a matrix, and the guard of order (Tail.lean:718-721). The last four lines are called
by import (Johnson/Top/H0/L3/Frame.lean: closeStep, drawFront).
It reads the smallness test's record, what the hearing returned, the segment's record, the chain's
statement and the ledger's next free number; it gives the tables, the closed record and slotA.
The next free number is laid as slotA. Nothing tests that number where it is laid; it is read later
as the lower end of one stretch of numbers. By reading, a step that laid that number + 1 would pass
every later test on an honest proof.
Not asked here: that a sent word is below the prime (the general fold's).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import OnBytes.Model.Attention
import Johnson.Desc.First.Att.Tables
import Johnson.Top.H0.L3.Frame

set_option autoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Attention
open OnBytes.Model

/-- **aReadsQuiet, whole, on data.** Returns the tables, the closed record, and the next free slot in front of the draw of the matrix. -/
def readsStep (P : Plan) (tl : HTailF2) (f : First) (L : LinkCtx) (S : Statement) (F : Fork) :
    Option (Tables × HTailF2 × Nat) :=
  if tl.funOpen then do
    let t ← Tab.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x
    let s ← (L3.closeStep t.funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit)).toOption
    let _ ← (L3.drawFront s.tl L S).toOption
    pure (t, s.tl, F.next)
  else none

end VerifiableInference.Desc.First.Att
