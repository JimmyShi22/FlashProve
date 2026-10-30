-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Across/PassAtSixStatement.lean: AT EVERY RUN UNDER THE SIX NAMES OF "forms" THAT
ARE OPEN ON BOTH SIDES OF THE MERGE: WHAT THE RUN's READER ANSWERS IN FRONT IT ANSWERS BEHIND
(`Fwd`), AND THE SLOT OF THE MERGE's END VALUE IS NONE OF THE RUN's LATE ONES (`NotLate`): FROM THE
LIBRARY's CONDITION `RunsPass`; AND THAT CONDITION UNDER THE LIBRARY's HEAD, AT A STATE THAT THE
FIRST CHAIN REACHES AT BORDER 346, FROM NINE PUBLIC TESTS THERE AND THE MERGE's YES: STATEMENTS
ALONE: two definitions of propositions. NOTHING IS PROVED IN THIS FILE, and neither is one of the
library's goals: they are lemmas' statements.

  `PassAtSix`          the data's list of segments is the written one · the merge's yes · `RunsPass
                       (D.Rd 24) Pm a b` (Johnson/Top/H0/MergeLaw/KeepAtMerge.lean): at every run
                       under each of `sixNames` (FormsBackAtMerge.lean): `Fwd` and `NotLate`
  `RunsPassAtReached`  the head · a state reached at 346 · the eight public tests of `keep24`
                       (K11PubClosed.lean) accept there, at the composed meaning · `ledgerB` there ·
                       the merge's yes: `RunsPass (h.𝔇.Rd 24) Pm s s'`

Why. The library's `fwd_of_runsPass` (RunsAtMerge.lean) has the first half of the first; the way
forward of the sentence "forms" (FormsFwdStatement.lean of this folder) wants both halves, run by
run. The library's `runsPass_at_merge` takes the table's condition at 346, which a thread of the
honest side does not have; the thread has the public tests.

Limits. JOININGS: NOTHING NEW IS SHOWN OF ANY RUN. "Reached", the nine tests and the yes stay
premises: shown here of no state. Laws from a yes. Free of the honest side's frame. The head is a
premise, at the earlier hash, at the full size. Nothing on any property.
-/
import Johnson.Desc.K11.Behind.ReachedStatement
import Johnson.Top.H0.MergeLaw.RunsAtMerge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Across
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S ledgerB)
open VerifiableInference.Desc.First.MergeLaw (RunsPass NotLate sixNames)
open VerifiableInference.Desc.Sound (MgData mgAll mgBase keep24 linksFull)
open VerifiableInference.Reads.Pass (Fwd)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA TS)

/-- The statement on the runs under the six names. Not proved here; a lemma's statement, none of
the library's goals. -/
def PassAtSix : Prop :=
  ∀ (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (D : MgData Xi P Tok rows cols nR X), D.links = linksFull →
    ∀ (Pm : HeadMergeP) (a b : S) (rs : List Fmt.RoundView), headMergeDecide Pm a rs = .ok b →
    RunsPass (D.Rd 24) Pm a b →
    ∀ y ∈ sixNames, ∀ p ∈ D.runs 24 y.1 y.2,
      Fwd (D.Rd 24) p.1 p.2 a b ∧ NotLate (D.Rd 24) Pm p.1 p.2 a

/-- The statement at a reached state. Not proved here; a lemma's statement, none of the library's
goals. -/
def RunsPassAtReached : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Pm : HeadMergeP) (z : ProofFile.InstPub) (s s' : S)
    (rs : List Fmt.RoundView), Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 346 (z, s) →
    (∀ q ∈ keep24, (mgAll h.𝔇 mgBase).pub q (z, s) = true) → ledgerB s = true →
    headMergeDecide Pm s rs = .ok s' → RunsPass (h.𝔇.Rd 24) Pm s s'

end Johnson.Desc.First.ForkMerge.Across

#print axioms Johnson.Desc.First.ForkMerge.Across.PassAtSix
#print axioms Johnson.Desc.First.ForkMerge.Across.RunsPassAtReached
