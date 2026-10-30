-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K11/AtTheBook.lean: THE LAWS OF THE MERGE OF THE CLAIMS ON THE WEIGHTS (K11) THAT TAKE A
PUBLIC TEST ON THE BOOK AS A PREMISE, AT THE BOOK THAT `bookWhole` (Honest/BookWhole.lean) RETURNS
AT THE PROOF FILE's IOP AS WRITTEN IN LEAN (F0T), AT THE LIBRARY's WRITTEN SENDINGS AND THE MERGES
THAT `mergesByName` GUESSES: THERE, UNDER THE HEAD, THE TESTS ARE THEOREMS, AND THE LAWS STAND
WITHOUT THEM. Statements with their proofs: calls alone; no definition; nothing is evaluated here;
none of the library's goals.

  `tests_at_book`
      under the head's hypothesis h, at whatever book B bookWhole returns there: the locks' test
      `entryRunIs` accepts both entries of K11's part 1 at their written owners, starts and
      counts, and B.word F0T = none
  `book_with_tests`
      under h there is such a book
  `maskLot_agrees_at_book`
      `maskLot_agrees` (Honest/K2/Law/MaskLotAgrees.lean) at B, without its premise hE
  `indexLot_agrees_at_book`
      `indexLotAgreesAtHead` (Honest/K11/Plays/IndexLotAtHead.lean) at B, without its premise on
      the book
  `maskLot_once_at_book`, `indexLot_once_at_book`
      `maskLotOnce`, `indexLotOnce` (Honest/K11/Plays/LotsOnce.lean) at B, at the written numbers,
      without their two premises

By. `rawBook_at_head`, `RawBookFacts` (AtFullSide/K14/RawAtTheBookAtHead.lean, RawAtTheBook.lean),
`bookWhole_returns_written` (AtFullSide/K14/BookWholeWritten.lean),
`bookWhole_returns_at_head_of_written` (Honest/K14/BookWholeAtHead.lean): another group of authors'.
`bookWhole_word` (Honest/AtPureLaw.lean): the frame's authors'. NEAR, the next seam:
`atPure_book_at_head` (Honest/K14/AtPureBookAtHead.lean; this library may not hold it): where
`onlineProverFromPublicFiles` yields A, its own book A.B is what `bookWhole` returns at the public part's own three
lists: not called.

The file stands in this side library because its first imports do.

WHAT IT IS NOT. ALL THAT AtFullSide/K14/RawAtTheBook.lean DOES NOT CLAIM: a book's number is a claim
on a sender's text; the merges are a guess; the sendings are the written ones: THAT A THREAD's OWN
BOOK IS THIS BOOK IS NOT SAID: B is the caller's, under the caller's own return. The laws stay what
they were: wherever two texts both answer, they answer alike; no other part's entry meets these
coins. NO LOT IS LAID; that a text answers anywhere is not said. The head and the opening are
premises.

Limits. Letters laid at written numbers. The full size and the format's second hash function alone. Nothing
on any property.
-/
import AtFullSide.K14.RawAtTheBookAtHead
import Johnson.Desc.ProofFile.Honest.AtPureLaw
import Johnson.Desc.ProofFile.Honest.K2.Law.MaskLotAgrees
import Johnson.Desc.ProofFile.Honest.K11.Plays.IndexLotAtHead
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsOnce

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.Model (WsClaim)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.FillP1 (fvsAt)
open Johnson.Desc.First.Walk.Tied (rowsBefore)
open Johnson.Desc.First.ForkMerge.Exchange (lkAtFull)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)
open ProofFile.Honest
open ProofFile.Honest.K1 (SendJob msgTxt)
open ProofFile.Honest.K4.Lot (k4IndexRows k4IndexNum)
open ProofFile.Honest.K11 (k11MaskLot k11IndexLot)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchMsgTxt lotClosingAt segmentsOf)
open AtFullSide.K14 (rawBook_at_head bookWhole_returns_written)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {B : ProverCoinCounts}

/-- **At whatever book bookWhole returns at F0T both of the locks' tests accept, and the book fails
none of its own tests.** -/
theorem tests_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ ⟨23217, 3970⟩ ⟨0, 38⟩ =
        true ∧
      entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8659⟩ ⟨0, 1⟩ =
        true ∧
      B.word (F0T OnBytes.secondHashFunction Zp Np cF) = none :=
  ⟨(rawBook_at_head h hB).1, (rawBook_at_head h hB).2.1, bookWhole_word hB⟩

/-- **Under the head there is such a book.** -/
theorem book_with_tests (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∃ B, bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
        proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B ∧
      entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ ⟨23217, 3970⟩ ⟨0, 38⟩ =
        true ∧
      entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8659⟩ ⟨0, 1⟩ =
        true ∧
      B.word (F0T OnBytes.secondHashFunction Zp Np cF) = none := by
  obtain ⟨B, hB⟩ :=
    ProofFile.Honest.K14.bookWhole_returns_at_head_of_written bookWhole_returns_written h
  exact ⟨B, hB, tests_at_book h hB⟩

/-- **The merge's first lot and the switches' text, at that book.** -/
theorem maskLot_agrees_at_book {W₀ Rc Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (ch : Nat) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim)
    (weights : W₀ → Weights) (Dr : RowDataOf ProofFile.Inst)
    (readers : Local W₀ Rc ProofFile.Inst Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    {p : SwitchPlace} (hp : p ∈ switchPlaces Zp Bs.G₀) (hl : p.link = 24)
    (k : Coins B) (w : Local W₀ Rc ProofFile.Inst Tr) (hd hd' : List Fmt.Drawn) (mask : Bool)
    (row place : Nat) (y y' : Cb.Gl.E)
    (h1 : (k11MaskLot B (Rc := Rc) (Tr := Tr) X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
      weights (P5J.At.num Zp 24 0) 3531).txt k w hd mask row place = some y)
    (h2 : switchMsgTxt ch Dr readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p 2 k w hd' mask row
      place = some y') : y' = y := by
  have hk := (lkAtFull Z D r Zp Np cF x h Bs hb).1
  have g := (ProofFile.Honest.K2.Law.atLink24_gives
    (ProofFile.Honest.K2.Law.atLink24_at_head h.toAtMg O p hp) hl).1
  refine ProofFile.Honest.K2.Law.maskLot_agrees h O hb X ch claims weights Dr readers lay hp hl 23217 ?_
    k w hd hd' mask row place y y' h1 h2
  rw [hk, g]
  exact (tests_at_book h hB).1

/-- **The lot of the second join and the opening's message 4, at that book.** -/
theorem indexLot_agrees_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (W₀ Rc Tr X : Type) (ch : Nat)
    (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights) (W Y : Type)
    (wit : Local W₀ Rc ProofFile.Inst Tr → W) (J : SendJob W Y) (own₀ : Y)
    (hP : J.P = VerifiableInference.Desc.K1.firstPar Bs.G₀.first
      (VerifiableInference.Desc.K1.gpOf Zp))
    (hR : J.ride = ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.firstFold Bs.G₀.first)) :
    ∀ k w hd hd' mask row place y y',
      (k11IndexLot B (Rc := Rc) (Tr := Tr) X ch IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights (k4IndexNum Zp) (rowsBefore (fvsAt Zp) 24 % k4IndexRows Zp)
        (rowsBefore (fvsAt Zp) 24 / k4IndexRows Zp)).txt k w hd mask row place = some y →
      msgTxt ch wit J own₀ 4 k w hd' mask row place = some y' → y' = y :=
  ProofFile.Honest.K11.indexLotAgreesAtHead Z D r Zp Np cF x Bs base h O B W₀ Rc Tr X ch claims weights W
    Y wit J own₀ 25848 hP hR (tests_at_book h hB).2.1

/-- **No other part's entry meets the first lot's 38 coins, at that book.** -/
theorem maskLot_once_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    ∀ a', a' ≠ ⟨IM.k11Place, 1⟩ → ∀ e' ∈ spentE B a', e'.owner = ⟨⟨1, some 24, 2, .K2⟩, 0⟩ →
      ∀ i, i < 38 → ¬ (e'.start.e ≤ 3970 + i ∧ 3970 + i < e'.start.e + e'.count.e) := by
  have hk := (lkAtFull Z D r Zp Np cF x h Bs hb).1
  have t := ProofFile.Honest.K11.maskLotOnce ProofFile.Inst (F0T OnBytes.secondHashFunction Zp Np cF) B IM.k11Place
    (_root_.K11.parOf Zp Bs.G₀) ⟨⟨1, some 24, 2, .K2⟩, 0⟩ 23217 439 3531 (tests_at_book h hB).2.2
  rw [hk] at t
  exact t (tests_at_book h hB).1

/-- **No other part's entry meets the second lot's one coin, at that book.** -/
theorem indexLot_once_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    ∀ a', a' ≠ ⟨IM.k11Place, 1⟩ → ∀ e' ∈ spentE B a', e'.owner = ⟨⟨1, some 0, 1, .K1⟩, 0⟩ →
      ¬ (e'.start.e ≤ 8659 ∧ 8659 < e'.start.e + e'.count.e) :=
  ProofFile.Honest.K11.indexLotOnce ProofFile.Inst (F0T OnBytes.secondHashFunction Zp Np cF) B IM.k11Place
    ⟨⟨1, some 0, 1, .K1⟩, 0⟩ 25848 8659 (tests_at_book h hB).2.2 (tests_at_book h hB).2.1

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.tests_at_book
#print axioms AtFullSide.K11.book_with_tests
#print axioms AtFullSide.K11.maskLot_agrees_at_book
#print axioms AtFullSide.K11.indexLot_agrees_at_book
#print axioms AtFullSide.K11.maskLot_once_at_book
#print axioms AtFullSide.K11.indexLot_once_at_book
