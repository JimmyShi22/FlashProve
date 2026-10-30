--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/OwnTakenStatements.lean: THE KEY FILE's OWN PROXIMITY TEST
(number 2 of its last chain): "THE JOB's THREE TREES ARE THE TABLES TAKEN OVER", AS STATEMENTS.
Definitions alone. The proofs: K12/Part4/OwnTaken*.lean.

WHAT IT IS NOT.
  * Nothing is proved here: every statement is a definition of type Prop.
  * NOT IN FRONT OF A LAW OVER COINS: each statement speaks of one list of a run's coins k, one
    state m and what the frame has lent the test's two parts at k.
  * THAT THE FRAME LENDS THE TEST's TWO PARTS ANYTHING (`lendRow` returns) IS NOT SHOWN HERE: where
    it does not, the four statements `Taken…` say nothing.
  * THAT THE PREMISES ARE MET TOGETHER AT THE OFFLINE PROVER's PARTS IS SHOWN BY NOBODY HERE.
  * NOT A STATEMENT ON A RUN. No thread's stand is asked and none is shown: the statements hold at
    every state m. That a run reaches the test is said nowhere here.
  * NOT WITHOUT PREMISES. `OwnTestGround` holds them, each under its name. Four of its fields are
    premises on LETTERS, which can be false at a filling:
      `senders`, `idxPlace`, `wPlace`   the two sendings have the written messages, codes, rides and
                  places, and the shared chain's parameters are the written ones: `OwnSenders`
                  (K12/AtKey/OwnJob.lean) and two equations beside it. THE FIRST TWO ISSUES ASKED
                  THE TWO SENDINGS' WHOLE PARAMETERS TO BE THE WRITTEN ONES: that is false at the
                  verifier's own plans, in the field `groups`: there the statements said nothing.
                  No proof reads that field. That all eight fields of `OwnTestGround` are met
                  together at the offline description's senders and a thread made for it, in scope,
                  where the offline description and the key's public part return and the place is
                  the written one: `ground_p3` (E2E/LotTreesSentBeforeOwnTestProved.lean); `senders` at parts
                  whose plans are the verifier's own, in scope: `ownSenders_of_plans`
                  (K12/AtKey/OwnSendersAt.lean)
      `tables`    WHAT THE THREAD's TABLE IS AT THE THREE SOURCES: the first chain's two sendings'
                  own texts of a tree's table (`K1.treeTbl`, Honest/K1/ScriptLots.lean) at the
                  parts' own jobs, and the shared chain's sending's (`sendTable`,
                  Honest/K14/SendingsPaid.lean) at the parts' own public data; and after how many
                  challenges each is fixed. THAT THE OFFLINE PROVER's SCRIPT LAYS JUST THESE TEXTS
                  IS NOT SHOWN HERE
      `omegaReads`   the one challenge that the data of "send o_omega" reads is heard before its
                  tree is sent: the parts' number of "LIN point" against the description's rounds
      `wReads`    the data of W's sending reads of a front the challenges alone, and of these no
                  more than were heard when its tree was sent
  * The full size, the key file's book at the written sizes alone.
  * Nothing on completeness, on soundness or on what is hidden.

WHY. What a stand of this test owes on the trees in front is the last clause of `OwnAsks.opens`
(E2E/KeyOwnAccepted.lean): the job's three trees stand among the tables at hand, at their sources
(`OldAt`). `TakenAtTheOwnTest` says that each of the job's three trees has the depth and the columns
of the thread's table at its source (`TakenIs`, K12/AtFile/WAtHead.lean); from it `lot_p3`
(E2E/LotTreesSentBeforeOwnTestProved.lean) has that clause, under premises of its own. The three tables'
widths are stated beside it.

  `ownTestJob`        the job: `jobKWAt` (E2E/KeyProverSideOfOwnTest.lean) at the parts' two sendings and public
                      data; its reader of the shared chain's rows is the text of `askTests`
                      (AtFullSide/K12/KeyFourTests.lean)
  `TablesTakenOver`, `OwnTestGround`   the premises
  `ownTestTrees`      the job's trees at a state and at what the frame has lent
  `TakenIndexMasks`   tree 0 is the table of the index masks' sending: source «first chain, tree 0»
  `TakenVectorW`      tree 1 is the table of W's sending, with the first fresh table that rides in
                      it: source «first chain, tree 5»
  `TakenOmega`        tree 2 is the table of "send o_omega": source «shared chain, tree 1»
  **`TakenAtTheOwnTest`**   all three
  `WidthsAtTheOwnTest`   the three tables have 3, 12 and 36 words, at all coins, inputs and
                      challenges
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WAtHead
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnLinesGuards
import Johnson.Desc.ProofFile.Honest.K12.AtKey.OwnJob
import Johnson.Desc.ProofFile.Honest.K1.ScriptLots
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import E2E.KeyProver
import E2E.KeyProverSideOfOwnTest
import E2E.KeyThreadBase
import E2E.KeyBookAtWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.Key (Source LaterPlaces descriptionFromSource)
open H2K.Member (piKWFull)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub)
open AtPublicFiles.KeyFile (KeyParts In1 In2 randK14)
open AtPublicFiles.KeyLay (jobKWAt pWK)
open AtPublicFiles.KeyThread (fixedLast)
open ProofFile.Honest.K12.Light (ManyJob askOf)
open ProofFile.Honest.K12.AtFile (TakenIs)
open ProofFile.Honest.K12.AtKey (takenOwn OwnSenders)

variable {S Cl V Pb W₀ Rc X₀ X Wk : Type} {K₀ : KeyPub}

/-- **The job of the own test at a prover's parts.** -/
abbrev ownTestJob (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) : ManyJob (In1 W₀ Rc) X :=
  jobKWAt Xs Nr Pl K.idx K.w K.send id
    (askOf K.send (fun w => K.weights w.w₀) fun w => randK14 (K.rand w.rc))

/-- **What the thread's table is at the three sources taken over, and when each is fixed.**
toCommon: the shared chain's input, of the last chain's. -/
structure TablesTakenOver (T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb)
    (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
    (toCommon : In1 W₀ Rc → In2 W₀ Rc) : Prop where
  chain : T.chain = 2
  indexMasks : T.table (.taken 0 0) = K1.treeTbl 0 id K.idx K.own₀ 0
  vectorW : T.table (.taken 0 5) = K1.treeTbl 0 id K.w K.own₀ 0
  omega : T.table (.taken 1 1) = fun k w h =>
    K14.sendTable (K14.jobOmega K.send)
      (K14.witOf K.send.P K.weights fun c => randK14 (K.rand c)) (K14.sendPlace 5) 1 0 k
      (toCommon w) (h.drop ((descriptionFromSource Xs Nr Pl).first.blocksInOrder.flatMap (·.rounds)).length)
  fixed : ∀ σ ∈ takenOwn, T.fixed σ = fixedLast (descriptionFromSource Xs Nr Pl) σ
  index : ∀ w, (toCommon w).w₀ = w.w₀
  committed : ∀ w, (toCommon w).rc = w.rc

/-- **All premises.** -/
structure OwnTestGround (T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb)
    (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces)
    (toCommon : In1 W₀ Rc → In2 W₀ Rc) : Prop where
  book : fullPub = some K₀
  place : pWK Pl = piKWFull
  senders : OwnSenders K
  idxPlace : K.idx.P.place = ⟨1, none, 1, .K1⟩
  wPlace : K.w.P.place = ⟨1, none, 14, .K1⟩
  tables : TablesTakenOver T K Xs Nr Pl toCommon
  omegaReads : K.send.atPoint <
    AtPublicFiles.KeyThread.sentIn (AtPublicFiles.KeyThread.decl₂ (descriptionFromSource Xs Nr Pl)) 1
  wReads : ∀ x (fr fr' : Front X),
    fr.heard.take (fixedLast (descriptionFromSource Xs Nr Pl) (.taken 0 5)) =
      fr'.heard.take (fixedLast (descriptionFromSource Xs Nr Pl) (.taken 0 5)) → K.w.data x fr = K.w.data x fr'

/-- What the frame lends the test's two parts. -/
abbrev OwnTestCoins (V : Type) (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) : Type :=
  RowCoins [(firstPart (ownTestJob K Xs Nr Pl).toRun.toTest : Part V (In1 W₀ Rc) X),
    restPart (ownTestJob K Xs Nr Pl).toRun.toTest]

/-- The frame has lent c, at the run's coins k. -/
def Lent (T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb) (K : KeyParts W₀ Rc X₀ X Wk)
    (Xs : Source) (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (k : Coins (keyBook K₀))
    (c : OwnTestCoins V K Xs Nr Pl) : Prop :=
  lendRow (keyBook K₀) ((keyBook K₀).rowsOf T.chain) (k.look T.chain)
    (ownTestJob K Xs Nr Pl).p.place
    [(firstPart (ownTestJob K Xs Nr Pl).toRun.toTest : Part V (In1 W₀ Rc) X),
      restPart (ownTestJob K Xs Nr Pl).toRun.toTest] 0 = .ok c

/-- **The job's trees**, at a state and at what the frame has lent. -/
abbrev ownTestTrees (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source) (Nr : H2U.PlaceNums)
    (Pl : LaterPlaces) (m : Mid (In1 W₀ Rc) X) (c : OwnTestCoins V K Xs Nr Pl) :=
  (ownTestJob K Xs Nr Pl).toRun.toTest.trees₀ m.st.input (frontOf m)
    (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1).mem
    ((ownTestJob K Xs Nr Pl).toRun.toTest.first m.st.input (frontOf m)
      (restCoins (ownTestJob K Xs Nr Pl).toRun.toTest c.2.1))

/-- Tree number i of the job is the thread's table at the source σ: the form of the three
statements. -/
def TakenAt (i : ℕ) (σ : Fmt.TreeSource) : Prop :=
  ∀ (S Cl V Pb W₀ Rc X₀ X Wk : Type) (K₀ : KeyPub)
    (T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb) (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source)
    (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (toCommon : In1 W₀ Rc → In2 W₀ Rc),
    OwnTestGround T K Xs Nr Pl toCommon →
    ∀ (k : Coins (keyBook K₀)) (m : Mid (In1 W₀ Rc) X) (c : OwnTestCoins V K Xs Nr Pl),
      Lent T K Xs Nr Pl k c → TakenIs T k m (ownTestTrees K Xs Nr Pl m c) i σ

/-- **Tree 0 is the table of the index masks' sending.** -/
def TakenIndexMasks : Prop := TakenAt 0 (.taken 0 0)

/-- **Tree 1 is the table of W's sending**, with the first fresh table that rides in it. -/
def TakenVectorW : Prop := TakenAt 1 (.taken 0 5)

/-- **Tree 2 is the table of "send o_omega".** -/
def TakenOmega : Prop := TakenAt 2 (.taken 1 1)

/-- **THE JOB's THREE TREES ARE THE TABLES TAKEN OVER**, at every state. -/
def TakenAtTheOwnTest : Prop :=
  ∀ (S Cl V Pb W₀ Rc X₀ X Wk : Type) (K₀ : KeyPub)
    (T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb) (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source)
    (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (toCommon : In1 W₀ Rc → In2 W₀ Rc),
    OwnTestGround T K Xs Nr Pl toCommon →
    ∀ (k : Coins (keyBook K₀)) (m : Mid (In1 W₀ Rc) X) (c : OwnTestCoins V K Xs Nr Pl),
      Lent T K Xs Nr Pl k c →
      ∀ i (hi : i < takenOwn.length), TakenIs T k m (ownTestTrees K Xs Nr Pl m c) i takenOwn[i]

/-- **The three tables' widths**, at all coins, inputs and challenges. -/
def WidthsAtTheOwnTest : Prop :=
  ∀ (S Cl V Pb W₀ Rc X₀ X Wk : Type) (K₀ : KeyPub)
    (T : Thread (keyBook K₀) S Cl V (In1 W₀ Rc) X Pb) (K : KeyParts W₀ Rc X₀ X Wk) (Xs : Source)
    (Nr : H2U.PlaceNums) (Pl : LaterPlaces) (toCommon : In1 W₀ Rc → In2 W₀ Rc),
    OwnTestGround T K Xs Nr Pl toCommon →
    ∀ x ∈ ([(.taken 0 0, 3), (.taken 0 5, 12), (.taken 1 1, 36)] : List (Fmt.TreeSource × ℕ)),
      ∀ k w h, (T.table x.1 k w h).2.words = x.2

end ProofFile.Honest.K12.Part4
