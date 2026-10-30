--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/TwoTestsOfTheSharedChainStatements.lean: THE TWO PROXIMITY
TESTS OF THE PROOF FILE's SHARED CHAIN (the kind K12, members 9 and 10: on G_u and on G_omega): THE
BOOK LENDS BOTH THEIR JOBS; AND THE NEW TREES OF THE FIRST ARE THE THREAD's TABLES. Statements:
definitions alone. The proofs: Honest/K12/Part4/TwoTestsOfTheSharedChain.lean.

WHAT IT IS NOT.
  * Nothing is proved here: every statement is a definition of type Prop.
  * laysB (Honest/K12/StepsReturn.lean) IS A PUBLIC TEST on the book of coins and on three public
    fields of a job (its place's record, its members, its word on the fresh table): "the book has
    the rows, cuts and entries that the test's two parts ask". It names no run and no coin's value.
  * NOT the depths of the shared chain's tables and NOT the carrying of the letter SaidField: these
    are another house's (table_depths, Honest/K12/AtFile/OSaid.lean; depths_all and walk_shared,
    WalkAtShared.lean; said_of_trees, SharedWalk.lean). The first two statements here are two
    PREMISES of those laws (hLU, hLO).
  * The third statement is not acceptance and none of the five sentences at member 9; it says
    nothing where no state meets the invariant at 9. NOT IN FRONT OF A LAW OVER COINS.
  * It stands over files of another house that lie in no sealed tree (Honest/K12/AtFile/*).
  * Under the library's hypothesis on the proof file's description: the full size alone.
  * Nothing on completeness, on soundness or on what a proof hides.

WHAT IT IS.
  BookLendsATestOnU        at the book that the maker's routine returns at the written description:
                           laysB says yes at EVERY job with the seated record of the test on G_u,
                           the two sendings' members and that test's word on the fresh table
  BookLendsATestOnOmega    the same at the test on G_omega
  BookLendsTheJobOnU, BookLendsTheJobOnOmega   so at the library's two jobs (jobAtU, jobAtOmega,
                           Honest/K12/JobShared.lean), at EVERY door, reader and handed vector:
                           other house's jobDoorU and jobDoorO unfold to these
  NewTreesOfTheTestOnUAreTheThreadsTables   TreesNext at 9 (Honest/Thread/SaidField.lean), at every
                           letter Said and every door: with no premise on the book and none that
                           the prover's halves never stop

THE PREMISES, AND WHOSE EACH IS.
  the head       the library's hypothesis (P5J.AtMg).
  the book       bookWhole at the written description returns Bk: the maker's (at a return of the
                 maker: makers_book_one, AtFullSide/K14/MakersBookOne.lean).
  alike, member, seat, half, chain, ahead, table, fixed (the third statement alone)   on the thread:
                 fields of the other house's LaidU, or its letters.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LaysLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.TableShared
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.ProofFile.Honest.Thread.SaidField

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Alike₂)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K12 (P12 T12)
open Desc.K14 (St)
open P5J (TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open H2K.Member (piUFull)
open ProofFile.Honest.K12 (TestJob SeatOf proverSideOfProximityTest seedRound laysB)
open ProofFile.Honest.K12.Light (jobAtU jobAtOmega)
open ProofFile.Honest.K12.AtProof (fourOf membersU membersO freshU freshO)
open ProofFile.Honest.K12.AtFile (tableShared)

/-- **The book lends a test on G_u**: at every job with that test's three public fields. -/
def BookLendsATestOnU : Prop :=
  ∀ (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl), P5J.AtMg o Z D r Zp Np cF →
    ∀ (Bk : ProverCoinCounts) (W X : Type) (job : TestJob W X),
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk →
    job.p = (fourOf Np).U → job.members = membersU ⟨K1.qAt Zp Np, 0⟩ → job.fresh = freshU →
    laysB Bk 1 job = true

/-- **The book lends a test on G_omega.** -/
def BookLendsATestOnOmega : Prop :=
  ∀ (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl), P5J.AtMg o Z D r Zp Np cF →
    ∀ (Bk : ProverCoinCounts) (W X : Type) (job : TestJob W X) (record : P12),
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk →
    (fourOf Np).O = some record →
    job.p = record → job.members = membersO ⟨K1.qAt Zp Np, 0⟩ → job.fresh = freshO →
    laysB Bk 1 job = true

/-- **So at the library's job of the test on G_u**, at every door, reader and handed vector. -/
def BookLendsTheJobOnU : Prop :=
  ∀ (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl), P5J.AtMg o Z D r Zp Np cF →
    ∀ (Bk : ProverCoinCounts) (W X : Type) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (handed : Option (W → Front X → Nat → OnBytes.E)),
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk →
    laysB Bk 1 (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door weights rand handed).toRun.toTest = true

/-- **And at the library's job of the test on G_omega.** -/
def BookLendsTheJobOnOmega : Prop :=
  ∀ (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl), P5J.AtMg o Z D r Zp Np cF →
    ∀ (Bk : ProverCoinCounts) (W X : Type) (record : P12) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (handed : Option (W → Front X → Nat → OnBytes.E)),
    bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk →
    (fourOf Np).O = some record →
    laysB Bk 1 (jobAtOmega ⟨K1.qAt Zp Np, 0⟩ record door weights rand handed).toRun.toTest = true

/-- **The new trees of the test on G_u are the thread's tables**: TreesNext at 9, at every Said and
every door. -/
def NewTreesOfTheTestOnUAreTheThreadsTables : Prop :=
  ∀ (o : SecondHashFunctionArgument) (Z : VerifierAndGoals.PublicFiles) (D : WholeD) (r : LPFD.Full.RunPF) (Zp : Pub)
    (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl), P5J.AtMg o Z D r Zp Np cF →
    ∀ (W₀ Rc X₀ Cl V Pb : Type) (Bk : ProverCoinCounts)
    (T : Thread Bk St Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (Said : Nat → Coins Bk → Mid (Common W₀ Rc TableKey) X₀ → Prop)
    (weights : W₀ → Weights) (rand : Rc → TableRand)
    (testOnOmega : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (door : Common W₀ Rc TableKey → Front X₀ → T12) (block : Block St Cl),
    List.Forall₂ Alike₂ WP.shared.blocksInOrder T.bs →
    T.bs[9]? = some block →
    SeatOf block
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door (fun c => weights c.w₀) (fun c => rand c.rc)
        none).toRun.toTest
      (VerifiableInference.Desc.K12.Seat.enter (·.gU) (·.firstMask))
      VerifiableInference.Desc.K12.Seat.leave →
    (T.hs.find? fun g => g.place == (fourOf Np).U.place) = some (proverSideOfProximityTest
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door (fun c => weights c.w₀) (fun c => rand c.rc)
        none).toRun.toTest) →
    T.chain = 1 → T.ahead = [] →
    T.table = tableShared (K1.qAt Zp Np) weights rand
      (jobAtU ⟨K1.qAt Zp Np, 0⟩ (fourOf Np).U door (fun c => weights c.w₀) (fun c => rand c.rc)
        none).toRun.toTest
      testOnOmega own₀ →
    (∀ τ, τ + 1 < 5 → T.fixed (.own (3 + τ)) = 8 + seedRound piUFull.nums.stages τ) →
    TreesNext T Said 9

end ProofFile.Honest.K12.Part4

end
