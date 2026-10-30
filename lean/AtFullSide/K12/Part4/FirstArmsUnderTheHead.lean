-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/Part4/FirstArmsUnderTheHead.lean: THE LAST CHAIN's PROXIMITY TEST (the kind K12, the
place W): UNDER THE LIBRARY's HYPOTHESIS ON THE FIRST CHAIN AND AT THE MAKER's WRITTEN BOOK, AT THE
JOB THAT jobRealW RETURNS: THE PREMISE FirstArms (K12/AtFile/WJointArms.lean: trees 0 and 1 of the
test's job are the first chain's tables taken over), FROM WHAT THE THREAD's TWO TABLES ARE AND WHEN
THE SECOND IS FIXED.

WHAT IT IS NOT.
  * IT IS CONDITIONAL ON THE THREAD's LETTERS. armIndex, armW: the thread's tables at the sources
    .taken 0 1 and .taken 0 82 are the tables of the first opening's job and of W's sending's job;
    fixedW: the second is fixed by the rounds in front of member number 356; lastChain: the thread
    is chain number 2's. Whoever lays the thread pays them: no thread is laid here.
  * hB, that the book is the one made of the written description, is a premise; so are the
    hypothesis (P5J.AtMgA: the full size and the format's second hash function alone), its opening O, and
    "jobRealW returns a job" at the opening's ground Bs.G₀.
  * It pays one clause of what a stand of this test owes (StandRest.taken, with tree 2 by another
    author's tree2_at_W). It does not say that a stand is reached, that a part plays or that a
    verifier accepts.
  * In the side library.
  * Nothing on completeness, soundness or what a proof hides.

WHAT IT IS. No definition; three theorems.

  firstArmsOfTheJobs     FirstArms at a job of the make (OfTheMake), where the thread's two tables
                         are those of two sendings' jobs at the written plans and rides, and the
                         senders' data are the members'
  dataOfTheIndexMasks    the first opening's job's data, as the first chain's thread has it, is the
                         test's first member's data, at any two fronts
  firstArmsUnderTheHead  **the statement**

CALLED. firstArmsOfTheTables (FirstArmsJoined.lean); bookCoversTheSenders
(BookCoversTheSenders.lean); jobAtTheHeadIsOfTheMake, sendingsAtTheHead (JobAtTheHead.lean);
dataOfWBehind (DataOfWAtHead.lean). Of other authors: first_data_behind
(AtFullSide/K12/FirstArmsK1.lean); eG_atAll, pin1_atAll; firstRide_head
(AtFullSide/K12/StatedAtHeadW.lean); firstRide_eq (K1/PlaceJob.lean).
-/
import AtFullSide.K12.Part4.FirstArmsJoined
import AtFullSide.K12.Part4.BookCoversTheSenders
import AtFullSide.K12.Part4.DataOfWAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12.Part4
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Part4
open VerifiableInference.Desc (Chain Block FileDescription)
open VerifiableInference.Desc.K1 (parGF parWF qFull)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open ProofFile.Honest.K12.Light (ManyJob)
open ProofFile.Honest.K12.AtProof (jobRealW inOf)
open ProofFile.Honest.K12.AtFile (FirstArms)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (TS)

/-- **FirstArms at a job of the make**, where the thread's two tables are those of two sendings'
jobs at the written plans and rides, and the senders' data are the members'. -/
theorem firstArmsOfTheJobs {S Cl V Pb W X WI WW WS XS : Type} {Bk : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (T : Thread Bk S Cl V W X Pb)
    (Said : ℕ → Coins Bk → Mid W X → Prop) (B : ManyJob W X) (numberI numberW : ℕ)
    (dataI : WI → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (dataW : WW → Front X → ℕ → ℕ → ℕ → Option (OnBytes.Slice.GF ⊕ OnBytes.Slice.GE))
    (liftI : W → WI) (liftW : W → WW) (make : OfTheMake B numberI numberW dataI dataW liftI liftW)
    (lastChain : T.chain = 2) (sentI sentW : K1.SendJob WS XS) (planI : sentI.P = parGF)
    (rideI : sentI.ride = writtenRideOfTheIndexMasks) (planW : sentW.P = parWF)
    (rideW : sentW.ride = writtenRideOfW) (witness : W → WS) (own₀ : XS)
    (armIndex : ∀ k w h, T.table (.taken 0 1) k w h = K1.treeTbl 0 witness sentI own₀ 1 k w h)
    (armW : ∀ k w h, T.table (.taken 0 82) k w h = K1.treeTbl 0 witness sentW own₀ 0 k w h)
    (dataIndex : ∀ m : Mid W X, sentI.data (witness m.st.input)
        { heard := m.st.heard.take (T.fixed (.taken 0 1)), own := own₀, seen := .bare [] } =
      dataI (liftI m.st.input) (frontOf m))
    (dataOfW : ∀ m : Mid W X, sentW.data (witness m.st.input)
        { heard := m.st.heard.take (T.fixed (.taken 0 82)), own := own₀, seen := .bare [] } =
      dataW (liftW m.st.input) (frontOf m)) :
    FirstArms T Said B := by
  obtain ⟨f0, f1, mC, members, tree0, tree1, fits, atW⟩ := make
  obtain ⟨PI, nI, rI, dI⟩ := sentI
  obtain ⟨PW, nW, rW, dW⟩ := sentW
  obtain rfl : PI = parGF := planI
  obtain rfl : rI = writtenRideOfTheIndexMasks := rideI
  obtain rfl : PW = parWF := planW
  obtain rfl : rW = writtenRideOfW := rideW
  obtain ⟨coverIndex, coverW⟩ := bookCoversTheSenders hB
  exact firstArmsOfTheTables hB T Said B numberI numberW dataI dataW liftI liftW f0 f1 mC members
    tree0 tree1 fits atW lastChain nI nW dI dW witness own₀ armIndex armW dataIndex dataOfW
    coverIndex coverW

/-- **The first opening's job's data, as the first chain's thread has it, is the test's first
member's data**, at any two fronts. No premise. -/
theorem dataOfTheIndexMasks {X : Type} (S : OnBytes.HonestTrace.Sz) (Z : ProofFile.Pub) (G : ProofFile.Ground)
    (x : ProofFile.Inst) (R : Readers) (number : ℕ) (fr fr' : Front X) :
    (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar G.first
        (VerifiableInference.Desc.K1.gpOf Z)) number (K1.firstFold G.first)
        (K1.lotData S Z G)).data ⟨x, R⟩ fr' = (K1.firstJob (X := X) S Z G).data R fr := by
  funext k r j
  exact (first_data_behind S Z G x R number fr fr' k r j).symm

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : P5J.AtMgA OnBytes.secondHashFunction Z D₀ r₀ Zp Np cF x) {Bs : ProofFile.PureBase}
  {base : List (Block TS ProofFile.Cl)}
  (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
    (_root_.Desc.K14.Law.seatZ Zp Np) (_root_.Desc.K14.Law.secondAt Zp Np))
include h O

/-- **FirstArms at the job that jobRealW returns, under the hypothesis and at the maker's book**,
from the thread's two tables and the count that fixes the second. numberI, numberW: the numbers that
the two sendings' first new messages get in the first chain's thread's jobs. -/
theorem firstArmsUnderTheHead {S' Cl V Pb W₀ Rc Tr X : Type} {Bk : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok Bk) (S : OnBytes.HonestTrace.Sz)
    (Fd : FileDescription ProofFile.Inst) (enter : Fd.S₃ → Except String VerifiableInference.Desc.K12.T12)
    (pile : ProofFile.Pub → ProofFile.Ground → K13.PileOf ProofFile.Inst)
    (no : VerifiableInference.Desc.Place → ℕ) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (weights : Local W₀ Rc ProofFile.Inst Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc ProofFile.Inst Tr → TableRand)
    {M : ManyJob (Local W₀ Rc ProofFile.Inst Tr) X}
    (made : jobRealW S Fd enter pile no readers weights rand Zp Bs.G₀ = some M)
    (T : Thread Bk S' Cl V (Local W₀ Rc ProofFile.Inst Tr) X Pb)
    (Said : ℕ → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (lastChain : T.chain = 2)
    (numberI numberW : ℕ) (own₀ : X)
    (armIndex : ∀ k w hd, T.table (.taken 0 1) k w hd =
      K1.treeTbl 0 (inOf readers)
        (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
          (VerifiableInference.Desc.K1.gpOf Zp)) numberI (K1.firstFold Bs.G₀.first)
          (K1.lotData S Zp Bs.G₀)) own₀ 1 k w hd)
    (armW : ∀ k w hd, T.table (.taken 0 82) k w hd =
      K1.treeTbl 0 (inOf readers)
        (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull numberW (K13.wDataAt pile Zp Bs.G₀))
        own₀ 0 k w hd)
    (fixedW : T.fixed (.taken 0 82) = roundsTo cF.blocksInOrder 356) :
    FirstArms T Said M := by
  obtain ⟨planI, rideI, planW, rideW⟩ := sendingsAtTheHead (X := X) h O S numberW
    (K13.wDataAt pile Zp Bs.G₀)
  exact firstArmsOfTheJobs hB T Said M _ _ _ _ readers (inOf readers)
    (jobAtTheHeadIsOfTheMake h O S Fd enter pile no readers weights rand made) lastChain
    (K1.placeJob (X := X) (VerifiableInference.Desc.K1.firstPar Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp)) numberI (K1.firstFold Bs.G₀.first)
      (K1.lotData S Zp Bs.G₀))
    (K1.wJobAt (X := X) Zp.first (K1.wGp Zp) 4 wMsgFull numberW (K13.wDataAt pile Zp Bs.G₀))
    planI rideI planW rideW (inOf readers) own₀ armIndex armW
    (fun m => dataOfTheIndexMasks S Zp Bs.G₀ m.st.input.x (readers m.st.input) numberI
      (frontOf m) _)
    (fun m => (dataOfWBehind h pile Bs.G₀ (no ⟨1, none, 4, .K1⟩) numberW
      (inOf readers m.st.input) (frontOf m) _ (by rw [fixedW]; rfl)).symm)

end AtFullSide.K12.Part4

#print axioms AtFullSide.K12.Part4.firstArmsOfTheJobs
#print axioms AtFullSide.K12.Part4.dataOfTheIndexMasks
#print axioms AtFullSide.K12.Part4.firstArmsUnderTheHead
