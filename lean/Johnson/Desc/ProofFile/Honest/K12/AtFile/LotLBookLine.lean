-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookLine.lean

It states no goal. No property of the protocol is claimed.

THE PUBLIC TEST `wordsBookB`
(ClosingWordsBook.lean) SAYS YES AT THE MAKER's BOOK, at the last code switch's part and the closing
proximity test's second part, at the 184 stretches that the switch carries.

  `carries_at_written`             at the written plan and messages, at either of the two parts: what
                                   the maker lays to carry is `carriesByFlags` at the written Booleans
  `wordsBookB_at_written_book`     at whatever book the maker returns at the written description
  `wordsBookB_at_makers_book`      UNDER THE HEAD, at the maker's book, at the finish pl and the test's
                                   place: the premise hb of `carryRows_of_book`

By what. `bookWhole_carries` (Honest/BookCarryKit.lean): at an address of the first chain the book's
carrying entries ARE `segmentCarriesAt` at the chain's plan and messages · `sentIn_first_written`
(Honest/BookWritten/SentFirst.lean) · `wp_placesOk` (Johnson/AtFull/ProofPlan/At/PlacesOk.lean) ·
`segmentCarriesAt_by_flags` (LotLBookLineLetters.lean) · `rawFresh_rounds`
(AtFullSide/K14/RawReturnsWritten.lean) · the closed lines `foldFlags_written` (LotLBookLineFolds.lean),
`carriedEntriesTest_written` (LotLBookLineEntries.lean), LotLBookLinePlaces.lean's two ·
`book_is_written`, `finish_is_written` (LotLOwedAtHead.lean) · `numbersL_at_head`, `p12At_place`
(K12/AtProof/). The kernel reads the plan and the entries apart.

Hypotheses of the last. h: the head. hB: Bk is the maker's book. hG, hf: pl is the finish at the blank
ground.

Limits.
- `wordsBookB` compares owner, start and count of the first 184 carried entries of the two parts, and
  asks that the next entry of the second is the first part's own from 0. Nothing on the value of a coin.
- The limits of BookCarryKit.lean and SwitchesLend.lean stand: the sendings are found by labels; that
  `mergesByName`'s merges are the format's is a theorem nowhere.
- That the maker returns a book at the head's description is a premise here (hB).
- The full size alone. Closed lines by Lean's kernel.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineEntries
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLineFolds
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLinePlaces
import Johnson.Desc.ProofFile.Honest.BookCarryKit
import Johnson.Desc.ProofFile.Honest.BookWritten.SentFirst
import Johnson.AtFull.ProofPlan.At.PlacesOk
import AtFullSide.K14.RawReturnsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (carryE)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)
open AtFullSide.K14 (rawFreshRounds rawFresh_rounds)
open P5J (TS)

/-- **At the written plan and messages: what the maker lays for the two parts to carry.** -/
theorem carries_at_written :
    segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW ⟨⟨1, none, 1, .K2⟩, 0⟩ =
        carriesByFlags (foldFlagsW.map (·.1)) sentFirstW ⟨⟨1, none, 1, .K2⟩, 0⟩ ∧
      segmentCarriesAt (planOf WP.first.blocksInOrder) sentFirstW ⟨⟨1, none, 2, .K12⟩, 1⟩ =
        carriesByFlags (foldFlagsW.map (·.2)) sentFirstW ⟨⟨1, none, 2, .K12⟩, 1⟩ := by
  have hW := eq_of_beq foldFlags_written
  constructor
  · rw [segmentCarriesAt_by_flags, rawFresh_rounds, ← hW, List.map_map]
    refine congrArg (fun fl => carriesByFlags fl sentFirstW _) (List.map_congr_left fun i _ => ?_)
    show _ = (foldFlagsAtTwo _ _ _ i).1
    rw [foldFlagsAtTwo_eq]
  · rw [segmentCarriesAt_by_flags, rawFresh_rounds, ← hW, List.map_map]
    refine congrArg (fun fl => carriesByFlags fl sentFirstW _) (List.map_congr_left fun i _ => ?_)
    show _ = (foldFlagsAtTwo _ _ _ i).2
    rw [foldFlagsAtTwo_eq]

/-- **At whatever book the maker returns at the written description the test says yes.** -/
theorem wordsBookB_at_written_book {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) :
    wordsBookB B ⟨⟨1, none, 1, .K2⟩, 0⟩ ⟨⟨1, none, 2, .K12⟩, 1⟩ 184 = true := by
  have hp := closingPlaces_in_written_chain
  rw [Bool.and_eq_true] at hp
  obtain ⟨m1, hm1, e1⟩ := bookWhole_carries hB P2Law.ProofPlan.wp_placesOk
    (a := ⟨⟨1, none, 1, .K2⟩, 0⟩) (List.contains_iff_mem.1 hp.2)
  obtain ⟨m2, hm2, e2⟩ := bookWhole_carries hB P2Law.ProofPlan.wp_placesOk
    (a := ⟨⟨1, none, 2, .K12⟩, 1⟩) (List.contains_iff_mem.1 hp.1)
  obtain rfl : sentFirstW = m1 := Except.ok.inj (sentIn_first_written.symm.trans hm1)
  obtain rfl : sentFirstW = m2 := Except.ok.inj (sentIn_first_written.symm.trans hm2)
  apply wordsBookB_of_carriedEntriesTest
  rw [e1, e2, carries_at_written.1, carries_at_written.2]
  exact carriedEntriesTest_written

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bk : ProverCoinCounts}

/-- **UNDER THE HEAD, AT THE MAKER's BOOK**: the premise hb of `carryRows_of_book` and of
`carryRows_at_row_coins`, at the finish and the closing test's own place. -/
theorem wordsBookB_at_makers_book (h : P5J.AtMg o Z D₀ r₀ Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) :
    wordsBookB Bk ⟨pl.place, 0⟩ ⟨(H2U.p12OfMade Zp.made).place, 1⟩ pl.front.length = true := by
  have hw := (finish_is_written h hG hf).1
  have t := finish_place_and_stretches_written
  rw [hw] at t
  have t' : (pl.place, pl.front.length) = (⟨1, none, 1, .K2⟩, 184) := Option.some.inj t
  have hpl : (H2U.p12OfMade Zp.made).place = placeL := by
    rw [numbersL_at_head h]
    exact p12At_place _ _
  obtain ⟨e1, e2⟩ := Prod.mk.inj t'
  rw [e1, e2, hpl]
  exact wordsBookB_at_written_book (book_is_written h hB)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carries_at_written
#print axioms ProofFile.Honest.K12.AtProof.wordsBookB_at_written_book
#print axioms ProofFile.Honest.K12.AtProof.wordsBookB_at_makers_book
