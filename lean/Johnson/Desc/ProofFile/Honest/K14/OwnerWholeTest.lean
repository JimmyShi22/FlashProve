-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/OwnerWholeTest.lean: A SHORT PUBLIC TEST ON A BOOK OF COINS AT ONE
OWNER: just one entry spends of the owner's coins, and it is a given run; every other entry with
that owner is one of given stretches. DEFINITIONS WITH CODE ALONE; no statement. It stands over
Honest/K14/FreshOwner.lean (and so Honest/BookGuard.lean) alone, so that a test program can call it.

  aheadAt, onlyAt   the book's entries with an owner; the book with these entries alone
  wholeOrSpent st ct ms B o   **the test**: just one entry spends of o's coins, and it is the run
                  (st, ct); every other entry with that owner is one of the stretches ms, by start
                  and count. It reads of the book the field ahead alone, and of that the entries
                  with the owner o alone: so it can be asked of a book, and of that book with
                  another list laid for ahead
  runsFit first len a c ms   each stretch has no coin of the base field, and is apart from the run
                  (first, len), or holds one of the coins (a, c)
  spStretches, spWholeB   **the test at the part at "send o_omega"**: the stretches: o_omega's and
                  o_sp's whole runs among the part's coins; the spent run: o_sp's first coin; the
                  number n of o_sp's entries that are no pad read off the mask code (spEntries)

What a yes is worth: Honest/K14/OwnerWhole.lean: with the book's own tests and three tests on the
plan: a yes of the owner's test (spOwner, Honest/K14/FreshOwner.lean) at the description's own order
of places. A YES AT ONE BOOK, BY A PROGRAM's RUN, IS NO PROOF.
What is not claimed. That any book passes. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.FreshOwner

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- The book's entries with this owner, in the book's order. -/
def aheadAt (B : ProverCoinCounts) (o : Addr) : List Ahead := B.ahead.filter (·.owner == o)

/-- The book with these entries alone. -/
def onlyAt (B : ProverCoinCounts) (o : Addr) : ProverCoinCounts := { B with ahead := aheadAt B o }

/-- **The test**: just one entry spends of o's coins, and it is the run (st, ct); every other entry
with that owner is one of the stretches ms. -/
def wholeOrSpent (st ct : Due) (ms : List (Due × Due)) (B : ProverCoinCounts) (o : Addr) : Bool :=
  (match spendersOf B o with
    | [e] => e.start == st && e.count == ct
    | _ => false) &&
    (aheadAt B o).all fun e => e.once || ms.contains (e.start, e.count)

/-- Each stretch has no coin of the base field, and is apart from the run (first, len), or holds
one of the coins (a, c). -/
def runsFit (first len a c : Nat) (ms : List (Due × Due)) : Bool :=
  ms.all fun m => m.2.f == 0 && (!meets m.1.e m.2.e first len || meets m.1.e m.2.e a c)

/-- o_omega's and o_sp's whole runs among the coins of the part at "send o_omega", each by start and
count. n: the number of o_sp's entries that are no pad. -/
def spStretches (A : SendPub) (n : Nat) : List (Due × Due) :=
  [(⟨0, 0⟩, ⟨0, spFirstCoin A⟩), (⟨0, spFirstCoin A⟩, ⟨0, n + 1 + (spMaskCode A).r⟩)]

/-- **The test at the part at "send o_omega".** -/
def spWholeB (A : SendPub) (B : ProverCoinCounts) : Bool :=
  wholeOrSpent ⟨0, spFirstCoin A⟩ ⟨0, 1⟩ (spStretches A (spEntries A)) B
    { place := sendPlace 5, part := 0 }

end ProofFile.Honest.K14
