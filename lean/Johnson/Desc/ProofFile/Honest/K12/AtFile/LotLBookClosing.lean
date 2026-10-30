-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLBookClosing.lean

It states no goal. No property of the protocol is claimed.

THE PUBLIC TEST `closingBookTest` (LOpensBook.lean)
SAYS YES AT THE MAKER's BOOK, at the finish of the code switch and the closing proximity test's second
part: by the light road of LotLBookLine.lean: the kernel reads the plan and the entries apart.

  `carried_at_written_book`          at whatever book the maker returns at the written description: what
                                     the two parts carry is `carriesByFlags` at the written Booleans
  `closingBookTest_at_makers_book`   UNDER THE HEAD, at the maker's book, at the finish pl and the test's
                                     own place
  `closingBookTest_at_base`          at the base prover's return A: the premise hbook of
                                     `acceptedS_at_first_thread` (LotLAccepted.lean), to the letter

By what. `bookWhole_carries` (Honest/BookCarryKit.lean), `sentIn_first_written`
(Honest/BookWritten/SentFirst.lean), `wp_placesOk` · `carries_at_written` (LotLBookLine.lean) ·
`closingCarriedTest_written` (LotLBookClosingEntries.lean), `closingBookTest_is`
(LotLBookClosingLetters.lean) · LotLBookLinePlaces.lean's two · `book_is_written`, `finish_is_written`
(LotLOwedAtHead.lean) · `numbersL_at_head`, `p12At_place` (K12/AtProof/) · `makersBook_at_base`,
`blankGround_at_base` (LotLSeatPlaysPremises.lean).

Hypotheses. h: the head. hB: Bk is the maker's book. hG, hf: pl is the finish at the blank ground. hA: the
maker returns A at the base prover's filling.

Limits.
- The test reads entries (owner, start, count), not the parts' texts. Nothing on the value of a coin.
- The limits of BookCarryKit.lean and SwitchesLend.lean stand: the sendings are found by labels; that
  `mergesByName`'s merges are the format's is a theorem nowhere.
- The full size alone. Closed lines by Lean's kernel. Public facts: nothing on a run.
- `closingBookTest_at_base` stands at the base prover's filling's return, at its own type of random
  values: NOT AT THE ONLINE PROVER, whose filling reads this one through the coins' map. The two in
  front of it stand at whatever book the maker returns.
- The statements at the maker's return are typed at `OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit`: they cannot
  even be written at the online prover's return (`OnlineProverWithDescription FullSizeMatrix (protocolAtFiles files).EncodingRandomness Cells Unit Unit`,
  E2E/TheHonestProver.lean): no law through `OnlineProverParts.through` is made here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookLine
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLBookClosingEntries
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLSeatPlaysPremises

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain)
open ProofFile.Honest (carryE)
open ProofFile.Honest.K12.LotL (makersBook_at_base blankGround_at_base)
open Johnson.G (proofSendsFull)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)

/-- **At whatever book the maker returns at the written description: what the two parts carry.** -/
theorem carried_at_written_book {B : ProverCoinCounts}
    (hB : bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B) :
    carryE B ⟨⟨1, none, 1, .K2⟩, 0⟩ =
        carriesByFlags (foldFlagsW.map (·.1)) sentFirstW ⟨⟨1, none, 1, .K2⟩, 0⟩ ∧
      carryE B ⟨⟨1, none, 2, .K12⟩, 1⟩ =
        carriesByFlags (foldFlagsW.map (·.2)) sentFirstW ⟨⟨1, none, 2, .K12⟩, 1⟩ := by
  have hp := closingPlaces_in_written_chain
  rw [Bool.and_eq_true] at hp
  obtain ⟨m1, hm1, e1⟩ := bookWhole_carries hB P2Law.ProofPlan.wp_placesOk
    (a := ⟨⟨1, none, 1, .K2⟩, 0⟩) (List.contains_iff_mem.1 hp.2)
  obtain ⟨m2, hm2, e2⟩ := bookWhole_carries hB P2Law.ProofPlan.wp_placesOk
    (a := ⟨⟨1, none, 2, .K12⟩, 1⟩) (List.contains_iff_mem.1 hp.1)
  obtain rfl : sentFirstW = m1 := Except.ok.inj (sentIn_first_written.symm.trans hm1)
  obtain rfl : sentFirstW = m2 := Except.ok.inj (sentIn_first_written.symm.trans hm2)
  exact ⟨e1.trans carries_at_written.1, e2.trans carries_at_written.2⟩

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {Bk : ProverCoinCounts}

/-- **UNDER THE HEAD, AT THE MAKER's BOOK**, at the finish and the closing test's own place. -/
theorem closingBookTest_at_makers_book (h : P5J.AtMg o Z D₀ r₀ Zp Np cF)
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {G : ProofFile.Ground} (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) :
    closingBookTest Bk pl ⟨(H2U.p12OfMade Zp.made).place, 1⟩ = true := by
  have hw := (finish_is_written h hG hf).1
  have t := finish_place_and_stretches_written
  rw [hw] at t
  have t' : (pl.place, pl.front.length) = (⟨1, none, 1, .K2⟩, 184) := Option.some.inj t
  obtain ⟨e1, -⟩ := Prod.mk.inj t'
  have hpl : (H2U.p12OfMade Zp.made).place = ⟨1, none, 2, .K12⟩ := by
    rw [numbersL_at_head h]
    exact p12At_place _ _
  obtain ⟨c1, c2⟩ := carried_at_written_book (book_is_written h hB)
  have hY := closingCarriedTest_written
  rw [hw] at hY
  rw [closingBookTest_is, hpl, e1, c1, c2]
  exact hY

/-- **At the base prover's return**: the premise hbook of `acceptedS_at_first_thread`. -/
theorem closingBookTest_at_base {W₀ : Type} {I : WiderIn W₀} {Sz : OnBytes.HonestTrace.Sz}
    {Op : OnlineProverArguments} {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r₀ A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction Sz Op) = .ok A)
    {pl : K2.SwitchPlace} (hf : finishAt A.Z A.G = some pl) :
    closingBookTest A.B pl ⟨(H2U.p12OfMade A.Z.made).place, 1⟩ = true :=
  closingBookTest_at_makers_book h.toAtMg (makersBook_at_base h hA) (blankGround_at_base h hA) hf

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.carried_at_written_book
#print axioms ProofFile.Honest.K12.AtProof.closingBookTest_at_makers_book
#print axioms ProofFile.Honest.K12.AtProof.closingBookTest_at_base
