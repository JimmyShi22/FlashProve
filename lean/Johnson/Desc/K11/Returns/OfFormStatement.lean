-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Returns/OfFormStatement.lean: AT THE MERGE OF THE CLAIMS ON THE WEIGHTS: THE KIND's
CLAUSE `K11Keeps` FROM THE WHOLE MEMBER's ACCEPTING STEP; AND WHAT TWO PUBLIC TESTS ON THE
VERIFIER's STATE (`ledgerB`, `freeAboveB`, Johnson/Desc/First/FillKeeper.lean) GIVE IN FRONT OF THE
MERGE AND BEHIND IT: STATEMENTS ALONE: four, each a definition of a proposition. NOTHING IS PROVED
IN THIS FILE, and none of the four is one of the library's goals: they are lemmas' statements. The
texts are the description's and the table's; no prover is named.

The two tests. `ledgerB s`: a ledger is open, and its three arrays have as many entries as it has
slots. `freeAboveB n s`: a ledger is open; every slot from its next free number on is free; it has n
slots. They are what the table's own layer lays for the public items "ledger" and "free above".

  `HeadMergeKeepsOfStep`   where the step of the kind's block, as it stands alone at a seat, says
                           yes from s to s' (`StepYes`, Johnson/Top/H0/Walk/Reach.lean):
                           `K11Keeps P s s'` (KeepsStatement.lean of this folder)
  `FreeAboveOfForm`        at a state that stands in the head's link and passes both tests, at any
                           number n: the link is open; the ledger has its sizes (`Sized`) and n
                           slots, and nothing at or above its next slot is filled (`FreeAbove`,
                           OnBytes/Tie/Pv/Psc/PscRoom.lean)
  `PubBehindMerge`         under `K11Keeps P s s'`: if both tests pass at s, the second at the
                           number P.nMsg, both pass at s', at the same number
  `PubTestOfForm`          where the kind's decision returns s' at s, both tests pass at s, and the
                           state in front names the member that holds the segment's mask rows
                           (`MaskAt`, Johnson/Top/H0/MergeLaw/MaskRow.lean): the test on forms at
                           the merge's own run passes behind (`formsIn`)

Limits. That the two tests pass at any state of a run is not said; nor `MaskAt`. Of the second test
in front `PubBehindMerge` spends the number of slots alone. Nothing on any property.
-/
import Johnson.Desc.K11.Returns.KeepsStatement
import Johnson.Desc.First.FillKeeper
import Johnson.Top.H0.Walk.Reach
import Johnson.Top.H0.MergeLaw.MergeMakesForms
import Johnson.Top.H0.MergeLaw.MaskRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Returns
open OnBytes.PscRun (Sized FreeAbove)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S HeadOwn ledgerB freeAboveB)
open VerifiableInference.Desc.First.MergeLaw (MaskAt mergeStates)
open VerifiableInference.Desc.K9 (formsIn Readers)
open Johnson.Desc.First.Walk.Tied (StepYes)

/-- The statement at the whole member's accepting step. ft: the first tree's number. name, pl: the
seat's name and place. Not proved here; a lemma's statement, none of the library's goals. -/
def HeadMergeKeepsOfStep : Prop :=
  ∀ (ft : ℕ) (P : HeadMergeP) (name : String) (pl : Place) (s s' : S),
    StepYes ft (IM.seatedAs ProofFile.sameReply (headClaimMergeKind P) name pl) s s' → K11Keeps P s s'

/-- The statement on what the two tests give at a head. Not proved here; a lemma's statement, none
of the library's goals. -/
def FreeAboveOfForm : Prop :=
  ∀ (n : ℕ) (s : S) (a : HeadOwn), s.here = .head a → ledgerB s = true → freeAboveB n s = true →
    a.opened = true ∧ Sized a.F ∧ a.F.ns = n ∧ FreeAbove a.F

/-- The statement on the two tests behind the merge. Not proved here; a lemma's statement, none of
the library's goals. -/
def PubBehindMerge : Prop :=
  ∀ (P : HeadMergeP) (s s' : S), K11Keeps P s s' → ledgerB s = true →
    freeAboveB P.nMsg s = true → ledgerB s' = true ∧ freeAboveB P.nMsg s' = true

/-- The statement on the test on forms. own: the segment's own places. xM, R: the member that holds
the mask rows, and the bits that number them. Not proved here; a lemma's statement, none of the
library's goals. -/
def PubTestOfForm : Prop :=
  ∀ (P : HeadMergeP) (s s' : S) (rs : List Fmt.RoundView) (own : List (ℕ × ℕ))
    (xM : VerifiableInference.Desc.Sound.Mem) (R : ℕ),
    headMergeDecide P s rs = .ok s' → ledgerB s = true → freeAboveB P.nMsg s = true →
    MaskAt own xM R s →
    formsIn (Readers.ofStates (mergeStates "the merge")) own 8 "the merge" s' = true

end Johnson.Desc.First.ForkMerge.Returns

#print axioms Johnson.Desc.First.ForkMerge.Returns.HeadMergeKeepsOfStep
#print axioms Johnson.Desc.First.ForkMerge.Returns.FreeAboveOfForm
#print axioms Johnson.Desc.First.ForkMerge.Returns.PubBehindMerge
#print axioms Johnson.Desc.First.ForkMerge.Returns.PubTestOfForm
