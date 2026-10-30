-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K11/LotsAnswerAtTheBook.lean: THE KIND K11's TWO LOTS OF ENTRIES (`k11MaskLot`,
`k11IndexLot`) ANSWER AT THEIR ENTRIES, AT EVERY RUN's COINS, INPUT AND LIST OF CHALLENGES: UNDER
THE LIBRARY's HEAD, AT WHATEVER BOOK bookWhole RETURNS AT F0T, ON CHAIN 0. Why: the two laws
`k11MaskLot_covered` and `k11IndexLot_covered` of this folder are implications FROM "the kind's lot
answers some y": IF A LOT ANSWERED NOWHERE THEY WOULD HOLD FOR NOTHING BUT THE NUMBERS' EQUATION.
AND: at the two public tests on the book on which "where both
answer they agree" rests, the owner and the start bent: four controls. No definition; nothing is
evaluated here. Eleven lemmas; none of the library's goals. PUBLIC DATA ALONE, but for the letters
k, w, hd under "for all" in the two ends.

  `k11Lends_of_fields`
      the test `k11Lends` reads of the book its three tables and its entries, not its cuts
  `lendsPart_sum_of_lk`, `k11Lends_of_numbers`
      of the plan's numbers it reads the link, the piece and lk alone
  `fields_at_book`, `k11Lends_at_book`
      what bookWhole returns at F0T has the written four; so the test says yes there, at the
      plan's own numbers: by `k11LendsW` (LendsWritten.lean of this folder: the kernel's yes at
      the written book, with three controls)
  `k11MaskLot_answers_at_book`, `k11IndexLot_answers_at_book`
      THE TWO ENDS: at that book each text's "isSome" IS its own fence: so it answers at each of
      its entries (38; one), and nowhere else
  `maskLock_owner_bent`, `maskLock_start_bent`, `indexLock_owner_bent`, `indexLock_start_bent`
      at that book the lock's test says no with the owner's part number bent from 0 to 1; with the
      start one coin further

How. `maskLotAnswers`, `indexLotAnswers` (Honest/K11/Plays/LotsPublic.lean): at every book a text
answers just where `k11Lends` says yes and the entry lies inside the fence. The first congruence
goes by taking the two books apart. The second goes by `lendsPart_counts`
(Honest/Small/LendsRow.lean, another group of authors'), each part's three counts written out: asked
outright whether the two rows are one, Lean's kernel gave up ("deep recursion detected"); the
author's reading, not tried apart: it compares the two jobs, which hold functions over the whole
layout. The four bent tests go by law: an entry has one owner and one start (`entryRunIs_gives`,
Honest/Small/EntryRunIs.lean; `tests_at_book`, AtTheBook.lean of this folder): THEY ADD NO NEW FACT
ON THE BOOK.

WHAT IT MEANS FOR THE TWO LAWS. Their fronts are met ON CHAIN 0. `k11MaskLot_covered` stands at a
letter ch: by the control `k11LendsW_other_chain` the first lot answers nowhere at that book on
chain 1: THERE THAT LAW SAYS NOTHING.

WHAT IT IS NOT. WHETHER, NOT WHAT: nothing on what a text answers. That a thread's book is what
bookWhole returns at F0T is not said. The merges are mergesByName's, which the frame's own text
calls a guess. Nothing on what a coin is worth or how it is drawn.

Limits. Closed facts by Lean's kernel lie beneath, four of them in LendsWritten.lean. The full size;
the format's second hash function. All limits of LendsWritten.lean and AtTheBook.lean stand. Nothing on any
property.
-/
import AtFullSide.K11.AtTheBook
import AtFullSide.K11.LendsWritten
import AtFullSide.K14.RawBookRowsWritten
import AtFullSide.K14.RawAheadWritten
import Johnson.Desc.ProofFile.Honest.K11.Plays.LotsPublic
import Johnson.Desc.K11.Exchange.AtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K11
open OnBytes.Model (WsClaim WsLay)
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.ForkMerge (HeadMergeP)
open Johnson.Desc.First.ForkMerge.Exchange (lkAtFull headMergeAtFull)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open ProofFile.Honest
open ProofFile.Honest.K11 (k11MaskLot k11IndexLot k11Lends k11PublicRow maskLotAnswers indexLotAnswers
  HeadMergeAsk headMergeShape headMergeJob headMergePlace)
open AtFullSide.K14 (rawRowsFirstW rawRowsSharedW rawRowsSecondW rawAheadW rawBookRows_written
  rawAhead_written rawBook_same bookWhole_returns_raw bookRaw_returns_written)

/-- **The test reads the book's three tables and its entries, not its cuts.** -/
theorem k11Lends_of_fields {B B' : ProverCoinCounts} (h1 : B.first = B'.first) (h2 : B.shared = B'.shared)
    (h3 : B.second = B'.second) (h4 : B.ahead = B'.ahead) (ch : Nat) (pl : Place)
    (P : HeadMergeP) : k11Lends B ch pl P = k11Lends B' ch pl P := by
  obtain ⟨f, s, t, a, c⟩ := B
  obtain ⟨f', s', t', a', c'⟩ := B'
  obtain rfl : f = f' := h1
  obtain rfl : s = s' := h2
  obtain rfl : t = t' := h3
  obtain rfl : a = a' := h4
  rfl

/-- Two sum parts of one pair of names whose layouts have one number of column bits are lent alike:
each part's three counts are written out, so that no two jobs are ever compared. -/
theorem lendsPart_sum_of_lk (Bk : ProverCoinCounts) (rows : List (Addr × Due)) (due : Addr → Due) (a : Addr)
    (n e : String) {lay lay' : WsLay} (hk : lay.lk = lay'.lk) :
    lendsPart Bk rows due a (sumPart n e (headMergeJob lay) : Part Unit HeadMergeAsk Unit) =
      lendsPart Bk rows due a (sumPart n e (headMergeJob lay') : Part Unit HeadMergeAsk Unit) := by
  have ht : ∀ y : WsLay,
      (sumPart n e (headMergeJob y) : Part Unit HeadMergeAsk Unit).takes = ⟨0, 0⟩ := fun _ => rfl
  have hs : ∀ y : WsLay,
      (sumPart n e (headMergeJob y) : Part Unit HeadMergeAsk Unit).spends =
        (n, ⟨0, ownRun (headMergeShape y.lk)⟩) :: endRuns e (headMergeShape y.lk).ends :=
    fun _ => rfl
  have hc : ∀ y : WsLay,
      (sumPart n e (headMergeJob y) : Part Unit HeadMergeAsk Unit).carries = [] := fun _ => rfl
  exact lendsPart_counts Bk rows due a ((ht lay).trans (ht lay').symm)
    (by rw [hs lay, hs lay', hk]) ((hc lay).trans (hc lay').symm)

/-- **Of the plan's numbers it reads the link, the piece and lk alone.** -/
theorem k11Lends_of_numbers (Bk : ProverCoinCounts) (ch : Nat) (pl : Place) {P P' : HeadMergeP}
    (h1 : P.link = P'.link) (h2 : P.piece = P'.piece) (h3 : P.lay.lk = P'.lay.lk) :
    k11Lends Bk ch pl P = k11Lends Bk ch pl P' := by
  have hpl : headMergePlace P = headMergePlace P' := by
    unfold headMergePlace
    rw [h1, h2]
  unfold k11Lends k11PublicRow lendsRow
  rw [hpl]
  simp only [lendsRowAt]
  rw [lendsPart_sum_of_lk Bk _ _ _ _ _ h3]

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {B : ProverCoinCounts}

/-- **What bookWhole returns at F0T has the written three tables and the written entries.** -/
theorem fields_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    B.first = rawRowsFirstW ∧ B.shared = rawRowsSharedW ∧ B.second = rawRowsSecondW ∧
      B.ahead = rawAheadW := by
  obtain ⟨W, hW⟩ := bookRaw_returns_written
  rw [rawBook_same h.scope h.laid (bookWhole_returns_raw W hW) hB]
  exact ⟨(rawBookRows_written _ W hW).1, (rawBookRows_written _ W hW).2.1,
    (rawBookRows_written _ W hW).2.2, rawAhead_written W hW⟩

/-- THE HEAD, THE BASE AND THE BOOK ARE PREMISES. **At that book the merge's row is lent, at the
plan's own numbers.** -/
theorem k11Lends_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    k11Lends B 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) = true := by
  obtain ⟨Bs', _, _, hmade', _, _, _, _, _, hlink⟩ := headMergeAtFull Z D r Zp Np cF x h
  obtain rfl : Bs' = Bs := Except.ok.inj (hmade'.symm.trans hb)
  have hk := (lkAtFull Z D r Zp Np cF x h Bs' hb).1
  have g := fields_at_book h hB
  rw [k11Lends_of_numbers B 0 IM.k11Place (P' := k11ParW 18) hlink rfl hk,
    k11Lends_of_fields (B' := k11BookW) g.1 g.2.1 g.2.2.1 g.2.2.2]
  exact k11LendsW

/-- **THE FIRST LOT ANSWERS JUST INSIDE ITS FENCE**, at every run's coins, input and challenges. -/
theorem k11MaskLot_answers_at_book {W₀ Rc Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (n ν₀ : Nat) (k : Coins B) (w : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn) (mask : Bool)
    (row place : Nat) :
    ((k11MaskLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights n ν₀).txt k w hd mask row place).isSome =
      decide (mask = true ∧ row = 0 ∧ ν₀ ≤ place ∧ place < ν₀ + 38) := by
  have hk := (lkAtFull Z D r Zp Np cF x h Bs hb).1
  rw [maskLotAnswers B W₀ Rc ProofFile.Inst Tr X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims weights
    n ν₀ k w hd mask row place, k11Lends_at_book h hb hB, Bool.true_and, hk]

/-- **THE SECOND LOT ANSWERS JUST AT ITS ONE ENTRY**, at every run's coins, input and challenges.
-/
theorem k11IndexLot_answers_at_book {W₀ Rc Tr : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hb : ProofFile.baseOf Zp (ProofFile.pureSeat OnBytes.secondHashFunction Zp) = .ok Bs)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    (X : Type) (claims : ProofFile.Inst → List Fmt.Drawn → List WsClaim) (weights : W₀ → Weights)
    (n r₀ p₀ : Nat) (k : Coins B) (w : Local W₀ Rc ProofFile.Inst Tr) (hd : List Fmt.Drawn)
    (mask : Bool) (row place : Nat) :
    ((k11IndexLot B (Rc := Rc) (Tr := Tr) X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims
        weights n r₀ p₀).txt k w hd mask row place).isSome =
      decide (mask = true ∧ row = r₀ ∧ place = p₀) := by
  rw [indexLotAnswers B W₀ Rc ProofFile.Inst Tr X 0 IM.k11Place (_root_.K11.parOf Zp Bs.G₀) claims weights
    n r₀ p₀ k w hd mask row place, k11Lends_at_book h hb hB, Bool.true_and]

/-- A control on the first lock: the owner's part number bent from 0 to 1. -/
theorem maskLock_owner_bent (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 1⟩ ⟨23217, 3970⟩
      ⟨0, 38⟩ = false := by
  cases hx : entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 1⟩ ⟨23217, 3970⟩
      ⟨0, 38⟩ with
  | false => rfl
  | true =>
    obtain ⟨e, he, ho, _, _⟩ := entryRunIs_gives hx
    obtain ⟨e', he', ho', _, _⟩ := entryRunIs_gives (tests_at_book h hB).1
    rw [he] at he'
    obtain rfl : e = e' := Option.some.inj he'
    rw [ho] at ho'
    exact absurd ho' (by decide)

/-- A control on the first lock: the start one coin further. -/
theorem maskLock_start_bent (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ ⟨23217, 3971⟩
      ⟨0, 38⟩ = false := by
  cases hx : entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 0 ⟨⟨1, some 24, 2, .K2⟩, 0⟩ ⟨23217, 3971⟩
      ⟨0, 38⟩ with
  | false => rfl
  | true =>
    obtain ⟨e, he, _, hs, _⟩ := entryRunIs_gives hx
    obtain ⟨e', he', _, hs', _⟩ := entryRunIs_gives (tests_at_book h hB).1
    rw [he] at he'
    obtain rfl : e = e' := Option.some.inj he'
    rw [hs] at hs'
    exact absurd hs' (by decide)

/-- A control on the second lock: the owner's part number bent from 0 to 1. -/
theorem indexLock_owner_bent (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 1⟩ ⟨25848, 8659⟩
      ⟨0, 1⟩ = false := by
  cases hx : entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 1⟩ ⟨25848, 8659⟩
      ⟨0, 1⟩ with
  | false => rfl
  | true =>
    obtain ⟨e, he, ho, _, _⟩ := entryRunIs_gives hx
    obtain ⟨e', he', ho', _, _⟩ := entryRunIs_gives (tests_at_book h hB).2.1
    rw [he] at he'
    obtain rfl : e = e' := Option.some.inj he'
    rw [ho] at ho'
    exact absurd ho' (by decide)

/-- A control on the second lock: the start one coin further. -/
theorem indexLock_start_bent (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B) :
    entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8660⟩
      ⟨0, 1⟩ = false := by
  cases hx : entryRunIs (spentE B ⟨IM.k11Place, 1⟩) 1 ⟨⟨1, some 0, 1, .K1⟩, 0⟩ ⟨25848, 8660⟩
      ⟨0, 1⟩ with
  | false => rfl
  | true =>
    obtain ⟨e, he, _, hs, _⟩ := entryRunIs_gives hx
    obtain ⟨e', he', _, hs', _⟩ := entryRunIs_gives (tests_at_book h hB).2.1
    rw [he] at he'
    obtain rfl : e = e' := Option.some.inj he'
    rw [hs] at hs'
    exact absurd hs' (by decide)

end AtFullSide.K11

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms AtFullSide.K11.k11Lends_of_fields
#print axioms AtFullSide.K11.lendsPart_sum_of_lk
#print axioms AtFullSide.K11.k11Lends_of_numbers
#print axioms AtFullSide.K11.fields_at_book
#print axioms AtFullSide.K11.k11Lends_at_book
#print axioms AtFullSide.K11.k11MaskLot_answers_at_book
#print axioms AtFullSide.K11.k11IndexLot_answers_at_book
#print axioms AtFullSide.K11.maskLock_owner_bent
#print axioms AtFullSide.K11.maskLock_start_bent
#print axioms AtFullSide.K11.indexLock_owner_bent
#print axioms AtFullSide.K11.indexLock_start_bent
