-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K11/Behind/ReachedStatement.lean: BEHIND A YES OF THE MERGE's MEMBER, NUMBER 346 OF THE
FIRST CHAIN's FLAT LIST, FROM A REACHED STATE, UNDER THE LIBRARY's HYPOTHESIS ON THE PUBLIC FILES
(`P5J.AtMgA`) AT THE FULL SIZE ALONE: NO MARK · THE PROMISE's SIX BOOLS AT BORDER 347 · "THE SAMPLES
ARE HELD" THERE · WHAT THE PUBLIC ITEMS THAT ARE OPEN THERE SAY BESIDE THEIR BOOLS: FROM THE SAME
FOUR AT BORDER 346: STATEMENTS ALONE: three definitions of propositions. NOTHING IS PROVED IN THIS
FILE, and none is one of the library's goals: they are lemmas' statements. No thread of the honest
side's frame, no prover and no oracle string stands in them.

Why. `PromiseBehindMerge` (PromiseStatement.lean of this folder) asks three facts on the state in
front, and stands at the decision. Here the three are had at a state that is reached by the steps of
the sub-protocols behind the test "every word shown is below the prime" (`Reach` over cF.blocksInOrder.map
below, Johnson/Top/H0/Walk/Reach.lean: the library's "reached"), and the yes is the seated member's
own step's.

  `SpeaksOfTests`       `speaks_at_front` (Johnson/Top/H0/MergeLaw/SpeaksAtFront.lean) with the
                        public tests of the eight items that it draws out of the table's condition
                        as a premise in that condition's stead
  `FrontAtReached`      at a reached state without a mark that meets the three of the promise at
                        346: `MergeFront` at the mask row's member, 0 and 256 · `Speaks` at the
                        head's link · `leavesLenB`
  `PromiseBehindStep`   the four behind the member's yes from the four in front, at a reached state

Limits. The four in front, "reached" and the yes are premises. The hypothesis is a premise; it
stands at the earlier hash. "Reached" is at the list with the test, not at the list that runs.
Nothing on any property.
-/
import Johnson.Desc.K11.Behind.PromiseStatement
import Johnson.Top.H0.Walk.Reach
import Johnson.Top.H0.MergeLaw.SpeaksOfTables

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.ForkMerge.Behind
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain Link Claim Block Wit)
open VerifiableInference.Desc.Sound (MgData mgAll CellsQ MsgT Mem xAt linksFull psFull keep24 below)
open VerifiableInference.Desc.First (S Meaning samplesHeld)
open VerifiableInference.Desc.First.MergeLaw (MergeFront Speaks leavesLenB TablesLaid)
open Johnson.Desc.First.Walk.Tied (Reach)
open P5J (AtMgA mgAtAll TS)

/-- The statement on the five tests with code. The letters: those of `speaks_at_front`. Not proved
here; a lemma's statement, none of the library's goals. -/
def SpeaksOfTests : Prop :=
  ∀ (Xi P Tok : Type) (rows cols nR : ℕ) (X : OnBytes.Model.Verify.Public)
    (D : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT)) (z : P)
    (a : S) (l : Link S Claim),
    D.links = linksFull → VerifiableInference.OnPublicFiles.headLink X = 24 →
    (∀ q ∈ keep24, (mgAll D Mg).pub q (z, a) = true) → D.lk 24 = some l →
    TablesLaid (VerifiableInference.Desc.K9.phAt X 24) a → Speaks l a

/-- The statement on the three facts. Not proved here; a lemma's statement, none of the library's
goals. -/
def FrontAtReached : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (Lk : Link S ProofFile.Cl) (xM : Mem)
    (z : ProofFile.InstPub) (s : S),
    cF.links[24]? = some Lk → xAt (P5J.At.ms Zp Z.lay) (73, 2) = some xM →
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 346 (z, s) → s.failed = none →
    IM.XK h.𝔇.N linksFull psFull (P1K2.EQ (mgAtAll h) linksFull psFull z) 346 s = true →
    samplesHeld h.𝔇.N (mgAtAll h) (IM.openAt linksFull psFull 346) (z, s) = true →
    (∀ q ∈ P1K2.pubAt (mgAtAll h) linksFull psFull 346, (mgAtAll h).pubP q (z, s)) →
    MergeFront (h.𝔇.N.group 24) xM 0 256 s ∧ Speaks Lk s ∧ leavesLenB s = true

/-- The statement at the member's step. Not proved here; a lemma's statement, none of the library's
goals. -/
def PromiseBehindStep : Prop :=
  ∀ (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (blk : Block S ProofFile.Cl)
    (z : ProofFile.InstPub) (s s' : S),
    cF.blocksInOrder[346]? = some blk → IM.Yes 0 blk s s' →
    Reach 0 (cF.blocksInOrder.map below) (ProofFile.startS Zp) 346 (z, s) → s.failed = none →
    IM.XK h.𝔇.N linksFull psFull (P1K2.EQ (mgAtAll h) linksFull psFull z) 346 s = true →
    samplesHeld h.𝔇.N (mgAtAll h) (IM.openAt linksFull psFull 346) (z, s) = true →
    (∀ q ∈ P1K2.pubAt (mgAtAll h) linksFull psFull 346, (mgAtAll h).pubP q (z, s)) →
    s'.failed = none ∧
      IM.XK h.𝔇.N linksFull psFull (P1K2.EQ (mgAtAll h) linksFull psFull z) 347 s' = true ∧
      samplesHeld h.𝔇.N (mgAtAll h) (IM.openAt linksFull psFull 347) (z, s') = true ∧
      ∀ q ∈ P1K2.pubAt (mgAtAll h) linksFull psFull 347, (mgAtAll h).pubP q (z, s')

end Johnson.Desc.First.ForkMerge.Behind

#print axioms Johnson.Desc.First.ForkMerge.Behind.SpeaksOfTests
#print axioms Johnson.Desc.First.ForkMerge.Behind.FrontAtReached
#print axioms Johnson.Desc.First.ForkMerge.Behind.PromiseBehindStep
