-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/OwedLedgers.lean: A DEFINITION, AND A STATEMENT THAT IS OWED, WRITTEN AS A
DEFINITION OF A Prop: no proof stands here.
IN PLAIN WORDS. `LedgersFit st`: every ledger in the statement is that of some number of takes since
it was made (`LedgerAt`, Johnson/Desc/K13/Law/LedgerWithin.lean): under it an entry that a ledger
gives lies within its table (`takeEntry_within`, `takeMasksP_within` there). `OwedLedgersKept`: THE
GROUND's TEN PLAIN FUNCTIONS KEEP IT (`GroundKeeps`, Johnson/Desc/GroundKeeps.lean): so every block
of which a law "it keeps whatever the ground's functions keep" stands keeps it, as it keeps "tidy".
THE ROAD THAT IS MEANT, function by function. The admitting of a sample MAKES a ledger:
`ledgerAt_made` (read `admitP` and `Slice.freshLedger`: a ledger is laid only where there are mask
rows; "at least one answer" is tested). A mask's entry STEPS one: `takeMaskP_within`'s last clause.
The closing of a ledger turns "closed" alone, which `LedgerAt` does not read. The other seven leave
every message's ledger, its shape and the code table, or append messages without a ledger (read
`recvP`, `adoptP`, `elsewhereP`: THE QUESTION: does one of these lay or copy a ledger?).
Who spends it: whoever lays a row with a mask entry that a ledger gives, and must say "within its
table" of it at a later border.
What is not claimed. That a step which writes the statement by another road than these functions
keeps it: the laying of a pending row does so (`pendingRowO`, Johnson/Desc/First/Pend/Row.lean):
there `ledgerAt_take` serves.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K13.Law.LedgerWithin
import Johnson.Desc.GroundKeeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes
open VerifiableInference.Desc.Ground (GroundKeeps)

/-- Every ledger in the statement is that of some number of takes since it was made. -/
def LedgersFit (st : Statement) : Prop :=
  ∀ (o : ℕ) (x : Oracle), st.oracles[o]? = some x → x.ledger.isSome = true → ∃ k, LedgerAt st o k

/-- **OWED.** The ground's ten plain functions keep it. -/
def OwedLedgersKept : Prop := GroundKeeps fun S Z => LedgersFit S → LedgersFit Z

end VerifiableInference.Desc.K13.Law
