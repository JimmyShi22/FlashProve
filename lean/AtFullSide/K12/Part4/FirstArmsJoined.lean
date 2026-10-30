-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/FirstArmsJoined.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the place
W): THE PREMISE FirstArms (K12/AtFile/WJointArms.lean: trees 0 and 1 of the test's job are the first
chain's tables taken over), FROM WHAT THE THREAD's TWO TABLES ARE.

WHAT IT IS NOT.
  * IT IS CONDITIONAL. The two arms (armIndex, armW: the thread's tables at the sources .taken 0 1
    and .taken 0 82 are the tables of two sendings' jobs) are premises: they are letters of the
    thread, and whoever lays the thread pays them. So are dataIndex and dataOfW: that the data which
    a sender read when its table was fixed is the data which the test's member reads at its own
    front.
  * hB, that the book is the one made of the written description, and that it covers the two
    senders' counts (coverIndex, coverW) are premises here; the covers are paid under hB in
    BookCoversTheSenders.lean.
  * That a filling's job is of this make (members, the two trees, fits, atW) is a premise here; it
    is paid under the library's hypothesis in JobAtTheHead.lean. FirstArmsUnderTheHead.lean lays
    both in.
  * The stand is not spent: the clause is shown at every state at which the frame lends, and is
    stated so (FirstArmsAtEveryLending). That says nothing on whether the frame lends.
  * It pays one clause of what a stand of this test owes (StandRest.taken, with tree 2 by another
    author's tree2_at_W). It does not say that a stand is reached, that a part plays or that a
    verifier accepts.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. One definition; four theorems.

  addressesOfTheSenders    the two written plans' places are the two senders' addresses
  FirstArmsAtEveryLending  the text of FirstArms without its premise that the thread stands
  firstArmsOfEveryLending  what holds at every lending holds at a stand
  everyLendingOfTheTables  **FirstArmsAtEveryLending**, under the premises above
  firstArmsOfTheTables     **FirstArms**, under the same

CALLED. columnsAtTheBook (AtFullSide/K12/Part4/ColumnsAtTheBook.lean). Of other authors:
treeTbl_col, treeTbl_depth, cols_written (AtFullSide/K12/FirstArmsK1.lean); depth_three
(K12/AtFile/WJointTree.lean); own_two (Johnson/Desc/K1/Law/RadiiAtTwo.lean).
-/
import AtFullSide.K12.Part4.ColumnsAtTheBook
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WJointArms
import Johnson.Desc.K1.Law.RadiiAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Part4
open VerifiableInference.Desc.K1 (parGF parWF own_two)
open ProofFile.Honest.K12.Light (ManyJob Mem depth_three)
open ProofFile.Honest.K12.AtProof (memK1 senderI senderW placeW)
open ProofFile.Honest.K12.AtFile (FirstArms TakenIs)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)

/-- The two written plans' places are the two senders' addresses. -/
theorem addressesOfTheSenders :
    (⟨parGF.place, 0⟩ : Addr) = senderI ∧ (⟨parWF.place, 0⟩ : Addr) = senderW := ⟨rfl, rfl⟩

variable {S Cl V Pb W X WI WW WS XS : Type} {Bk : ProverCoinCounts}

/-- **Trees 0 and 1 at the first chain's tables, at every state and at the coins lent**: the text of
FirstArms without its premise that the thread stands. -/
def FirstArmsAtEveryLending (T : Thread Bk S Cl V W X Pb) (B : ManyJob W X) : Prop :=
  ∀ k (m : Mid W X)
    (c : RowCoins [(firstPart B.toRun.toTest : Part W W X), restPart B.toRun.toTest]),
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) B.p.place
      [(firstPart B.toRun.toTest : Part W W X), restPart B.toRun.toTest] 0 = .ok c →
    TakenIs T k m
        (B.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins B.toRun.toTest c.2.1).mem
          (B.toRun.toTest.first m.st.input (frontOf m) (restCoins B.toRun.toTest c.2.1)))
        0 (.taken 0 1) ∧
      TakenIs T k m
        (B.toRun.toTest.trees₀ m.st.input (frontOf m) (restCoins B.toRun.toTest c.2.1).mem
          (B.toRun.toTest.first m.st.input (frontOf m) (restCoins B.toRun.toTest c.2.1)))
        1 (.taken 0 82)

/-- What holds at every lending holds at a stand. -/
theorem firstArmsOfEveryLending {T : Thread Bk S Cl V W X Pb} {B : ManyJob W X}
    (atEveryLending : FirstArmsAtEveryLending T B) (Said : ℕ → Coins Bk → Mid W X → Prop) :
    FirstArms T Said B :=
  fun k _ m _ c _ lent => atEveryLending k m c lent

/-- **Trees 0 and 1 are the first chain's tables at every lending, from what the thread's two tables
are.** sentI, sentW, numberI, numberW, witness, own₀: the two sendings' jobs as the first chain's
thread has them, at the written plans and rides. The other letters: as in columnsAtTheBook. -/
theorem everyLendingOfTheTables
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (T : Thread Bk S Cl V W X Pb)
    (B : ManyJob W X) (firstI firstW : ℕ)
    (dataI : WI → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (dataW : WW → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (liftI : W → WI) (liftW : W → WW) (f0 f1 : Option ℕ × Option ℕ) (mC : Mem W X)
    (members : B.mems =
      [memK1 ⟨parGF, firstI, rideGF, dataI⟩ liftI senderI (parGF.sent.size - 1) f0,
        memK1 ⟨parWF, firstW, rideWF, dataW⟩ liftW senderW 0 f1, mC])
    (tree0 : B.trees[0]? = some (13, [.mask 0]))
    (tree1 : B.trees[1]? = some (22, [.main 1, .mask 1, .fresh]))
    (fits : SentMembersFit B.s₀ parGF parWF rideWF f0 f1) (atW : B.p.place = placeW)
    (lastChain : T.chain = 2) (numberI numberW : ℕ)
    (sentI sentW : WS → Front XS → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (witness : W → WS) (own₀ : XS)
    (armIndex : ∀ k w h, T.table (.taken 0 1) k w h =
      K1.treeTbl 0 witness ⟨parGF, numberI, rideGF, sentI⟩ own₀ 1 k w h)
    (armW : ∀ k w h, T.table (.taken 0 82) k w h =
      K1.treeTbl 0 witness ⟨parWF, numberW, rideWF, sentW⟩ own₀ 0 k w h)
    (dataIndex : ∀ m : Mid W X, sentI (witness m.st.input)
        { heard := m.st.heard.take (T.fixed (.taken 0 1)), own := own₀, seen := .bare [] } =
      dataI (liftI m.st.input) (frontOf m))
    (dataOfW : ∀ m : Mid W X, sentW (witness m.st.input)
        { heard := m.st.heard.take (T.fixed (.taken 0 82)), own := own₀, seen := .bare [] } =
      dataW (liftW m.st.input) (frontOf m))
    (coverIndex : ∀ k : Coins Bk, ∃ c,
      (k.look 0 senderI).2.cut ⟨0, 0⟩ (K1.dueR parGF rideGF) = some c)
    (coverW : ∀ k : Coins Bk, ∃ c,
      (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c) :
    FirstArmsAtEveryLending T B := by
  intro k m c lent
  rw [lastChain] at lent
  obtain ⟨cI, cutIndex⟩ := coverIndex k
  obtain ⟨cW, cutW⟩ := coverW k
  obtain ⟨-, -, -, -, treesI, treesW, depthI, depthW⟩ := cols_written
  have columns := columnsAtTheBook hB B firstI firstW dataI dataW liftI liftW f0 f1 mC members
    tree0 tree1 fits atW k c lent cutIndex cutW m.st.input (frontOf m)
  refine ⟨⟨?_, fun x _ => ?_⟩, ⟨?_, fun x _ => ?_⟩⟩
  · rw [depth_three B _ _ mC members m.st.input (frontOf m) _ _ 0 13 [.mask 0] tree0]
    show 13 =
      (T.table (.taken 0 1) k m.st.input (m.st.heard.take (T.fixed (.taken 0 1)))).2.logLength
    rw [armIndex, treeTbl_depth 0 witness ⟨parGF, numberI, rideGF, sentI⟩ own₀ 1 k _ _ cutIndex
      treesI]
    exact depthI.symm
  · show (T.table (.taken 0 1) k m.st.input (m.st.heard.take (T.fixed (.taken 0 1)))).2.col x = _
    rw [armIndex, treeTbl_col 0 witness ⟨parGF, numberI, rideGF, sentI⟩ own₀ 1 k _ _ cutIndex
      own_two.1 treesI x, (columns x).1, ← dataIndex m]
    rfl
  · rw [depth_three B _ _ mC members m.st.input (frontOf m) _ _ 1 22 [.main 1, .mask 1, .fresh]
      tree1]
    show 22 =
      (T.table (.taken 0 82) k m.st.input (m.st.heard.take (T.fixed (.taken 0 82)))).2.logLength
    rw [armW, treeTbl_depth 0 witness ⟨parWF, numberW, rideWF, sentW⟩ own₀ 0 k _ _ cutW treesW]
    exact depthW.symm
  · show (T.table (.taken 0 82) k m.st.input (m.st.heard.take (T.fixed (.taken 0 82)))).2.col x = _
    rw [armW, treeTbl_col 0 witness ⟨parWF, numberW, rideWF, sentW⟩ own₀ 0 k _ _ cutW own_two.2
      treesW x, (columns x).2, ← dataOfW m]
    rfl

/-- **FirstArms, from what the thread's two tables are.** The premises: those of
everyLendingOfTheTables. -/
theorem firstArmsOfTheTables
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (T : Thread Bk S Cl V W X Pb)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (B : ManyJob W X) (firstI firstW : ℕ)
    (dataI : WI → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (dataW : WW → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (liftI : W → WI) (liftW : W → WW) (f0 f1 : Option ℕ × Option ℕ) (mC : Mem W X)
    (members : B.mems =
      [memK1 ⟨parGF, firstI, rideGF, dataI⟩ liftI senderI (parGF.sent.size - 1) f0,
        memK1 ⟨parWF, firstW, rideWF, dataW⟩ liftW senderW 0 f1, mC])
    (tree0 : B.trees[0]? = some (13, [.mask 0]))
    (tree1 : B.trees[1]? = some (22, [.main 1, .mask 1, .fresh]))
    (fits : SentMembersFit B.s₀ parGF parWF rideWF f0 f1) (atW : B.p.place = placeW)
    (lastChain : T.chain = 2) (numberI numberW : ℕ)
    (sentI sentW : WS → Front XS → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (witness : W → WS) (own₀ : XS)
    (armIndex : ∀ k w h, T.table (.taken 0 1) k w h =
      K1.treeTbl 0 witness ⟨parGF, numberI, rideGF, sentI⟩ own₀ 1 k w h)
    (armW : ∀ k w h, T.table (.taken 0 82) k w h =
      K1.treeTbl 0 witness ⟨parWF, numberW, rideWF, sentW⟩ own₀ 0 k w h)
    (dataIndex : ∀ m : Mid W X, sentI (witness m.st.input)
        { heard := m.st.heard.take (T.fixed (.taken 0 1)), own := own₀, seen := .bare [] } =
      dataI (liftI m.st.input) (frontOf m))
    (dataOfW : ∀ m : Mid W X, sentW (witness m.st.input)
        { heard := m.st.heard.take (T.fixed (.taken 0 82)), own := own₀, seen := .bare [] } =
      dataW (liftW m.st.input) (frontOf m))
    (coverIndex : ∀ k : Coins Bk, ∃ c,
      (k.look 0 senderI).2.cut ⟨0, 0⟩ (K1.dueR parGF rideGF) = some c)
    (coverW : ∀ k : Coins Bk, ∃ c,
      (k.look 0 senderW).2.cut ⟨0, 0⟩ (K1.dueR parWF rideWF) = some c) :
    FirstArms T Said B :=
  firstArmsOfEveryLending (everyLendingOfTheTables hB T B firstI firstW dataI dataW liftI liftW f0
    f1 mC members tree0 tree1 fits atW lastChain numberI numberW sentI sentW witness own₀ armIndex
    armW dataIndex dataOfW coverIndex coverW) Said

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.addressesOfTheSenders
#print axioms AtFullSide.K12.Part4.firstArmsOfEveryLending
#print axioms AtFullSide.K12.Part4.everyLendingOfTheTables
#print axioms AtFullSide.K12.Part4.firstArmsOfTheTables
