-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/MaskWholeTest.lean: kind K14: A SHORT PUBLIC TEST ON A BOOK OF
COINS AT THE PART AT "send o_u": just one entry spends of that part's coins, and it is the run of
the first mask's coefficients; every other entry with that owner is o_u's or the first mask's whole
run. DEFINITIONS WITH CODE ALONE; no statement. It stands over Honest/K14/MaskOwner.lean and
Honest/K14/OwnerWholeTest.lean alone, so that a test program can call it.

  maskStretches   o_u's and the first mask's whole runs among the part's coins, by start and count
  maskWholeB      **the test**: wholeOrSpent (Honest/K14/OwnerWholeTest.lean) at the run of the
                  2 k + 1 coefficients, k read off the shape's first stage (maskRounds), and at
                  these two stretches

What a yes is worth: Honest/K14/MaskWhole.lean: with the book's own tests and three tests on the
plan: a yes of the owner's test (maskOwner, Honest/K14/MaskOwner.lean) at the description's own
order of places. A YES AT ONE BOOK, BY A PROGRAM's RUN, IS NO PROOF.
What is not claimed. That any book passes. Nothing on what is or is not hidden; no property.
-/
import Johnson.Desc.ProofFile.Honest.K14.MaskOwner
import Johnson.Desc.ProofFile.Honest.K14.OwnerWholeTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- o_u's and the first mask's whole runs among the coins of the part at "send o_u", each by start
and count. -/
def maskStretches (A : SendPub) : List (Due × Due) :=
  [(⟨0, 0⟩, ⟨0, maskFirstCoin A⟩), (⟨0, maskFirstCoin A⟩, ⟨0, (maskRun A).2⟩)]

/-- **The short test at the part at "send o_u"**: just one entry spends of its coins, and it is the
run of the first mask's 2 k + 1 coefficients; every other entry with that owner is one of the two
whole runs. -/
def maskWholeB (A : SendPub) (B : ProverCoinCounts) : Bool :=
  wholeOrSpent ⟨0, maskFirstCoin A⟩ ⟨0, 2 * maskRounds A + 1⟩ (maskStretches A) B
    { place := sendPlace 2, part := 0 }

end ProofFile.Honest.K14
