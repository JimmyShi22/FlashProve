-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofPlan/Every/Controls.lean: one root for the controls of this folder: the four
counts (Len‹…›.lean) and the nineteen negative tests (No‹…›.lean: each test rejects a bent copy or a
bent letter). Imports alone.
Limits. WHAT THE CONTROLS ARE WORTH. The four counts say that at the written term the seven plans'
entries, linkLocs, tableLocs and planPoints are not empty; planSeeds AND THE OTHER LISTS OVER WHICH
A TEST SAYS «all» ARE NOT COUNTED. By a reading of the tests' texts (Johnson/Bridge/PlanOkNat.lean,
PlanFiveNat.lean, Johnson/Desc/Ok/FormRules.lean), which no theorem says: THIRTEEN OF THE NINETEEN
NEGATIVE TESTS SHOW ONLY THAT THEIR TEST CAN REJECT (their heads say which); testsOk HAS NO NEGATIVE
TEST THAT REACHES ITS ARITHMETIC (tests_no repeats workOk's bound); every_no (EveryWritten.lean)
repeats seven_no.
Nothing on soundness.
-/
import Johnson.AtFull.ProofPlan.Every.LenPoints
import Johnson.AtFull.ProofPlan.Every.LenLocs
import Johnson.AtFull.ProofPlan.Every.LenEntries
import Johnson.AtFull.ProofPlan.Every.LenFirst
import Johnson.AtFull.ProofPlan.Every.NoSeven
import Johnson.AtFull.ProofPlan.Every.NoSetWork
import Johnson.AtFull.ProofPlan.Every.NoFirstPlans
import Johnson.AtFull.ProofPlan.Every.NoWork
import Johnson.AtFull.ProofPlan.Every.NoTests
import Johnson.AtFull.ProofPlan.Every.NoLocs
import Johnson.AtFull.ProofPlan.Every.NoTables
import Johnson.AtFull.ProofPlan.Every.NoPoints
import Johnson.AtFull.ProofPlan.Every.NoSends
import Johnson.AtFull.ProofPlan.Every.NoBats
import Johnson.AtFull.ProofPlan.Every.NoCensus
import Johnson.AtFull.ProofPlan.Every.NoRounds
import Johnson.AtFull.ProofPlan.Every.NoLinkGood
import Johnson.AtFull.ProofPlan.Every.NoRowsP1
import Johnson.AtFull.ProofPlan.Every.NoRowsP2
import Johnson.AtFull.ProofPlan.Every.NoRowsK1
import Johnson.AtFull.ProofPlan.Every.NoRowsK2
import Johnson.AtFull.ProofPlan.Every.NoRowsE
import Johnson.AtFull.ProofPlan.Every.NoBears
