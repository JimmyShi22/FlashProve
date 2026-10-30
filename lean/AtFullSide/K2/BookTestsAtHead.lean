-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K2/BookTestsAtHead.lean: the kind "the code switch" (K2): THE KIND's TWO TESTS ON THE
BOOK's CARRYING ENTRIES (`carriedFits`, `carriedSame`, Honest/K2/Law/CarriedAsks.lean) SAY YES AT
WHATEVER BOOK bookWhole RETURNS AT F0T, AT EACH WRITTEN SWITCH AND THE ONE IN FRONT OF IT: by Lean's
kernel at the written entries, under the library's head. PUBLIC DATA ALONE: a book's entries,
addresses, counts. A definition: a stand-in book; closed facts; statements with their proofs.

WHICH SLOT IT IS FOR. The binders hs and hf of `opener_at_join` (OpenerAtJoin.lean of this folder).

  `bookW`           a stand-in book that has the written entries `rawAheadW` and nothing else
  `carriedFits_entries`, `carriedSame_entries`   the two tests read of a book its entries alone
  `bookTestsW`      BY LEAN's KERNEL: both say yes at the stand-in, at the 25 written places; the
                    second at each place and the one with the link in front
  `bookTestsW_can_fail`, `bookTestsW_second_can_fail`   two controls: with the entries in the
                    reverse order each test says no, at the first place or the first two
  `book_tests_at_head`   THE END

By: `ahead_at_book` (CarriedAtTheBook.lean, of other authors) · `splitOn_eq`, `slice_toNat?_eq`
(Johnson/Unfolds/): two rewrites in front of the kernel.

Limits. THE HEAD AND hB ARE PREMISES. `rawAheadW` IS A LISTING OF THE WRITTEN BOOK's ENTRIES, OF
OTHER AUTHORS. Only neighbouring links are tested for the second test; a program's look at the
written entries counted 6 carried entries at link 1 and more beyond, so no pair is idle. The closed
facts ran with the limit on heartbeats lifted and a raised depth: about 14 minutes and 41 GB for
this file. CLOSED FACTS BY LEAN's KERNEL, REPLAYED BY NO INDEPENDENT CHECKER. The merges are
mergesByName's. The full size; the format's second hash function. No coin occurs. Nothing on any property.
-/
import AtFullSide.K2.CarriedAtTheBook
import Johnson.Desc.ProofFile.Honest.K2.Law.CarriedAsks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open VerifiableInference.Desc (Block Chain)
open Johnson.G (proofSendsFull)
open P5J (AtMgA F0T TS)
open OnBytes.Maker (WholeD)
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law
open AtFullSide.K14 (rawAheadW rawSegW)

/-- A stand-in book: the written entries and nothing else. -/
def bookW : ProverCoinCounts := { first := [], shared := [], second := [], cuts := [], ahead := rawAheadW }

/-- The first test reads of a book its entries alone. -/
theorem carriedFits_entries {B B' : ProverCoinCounts} (h : B.ahead = B'.ahead) (ps : List SwitchPlace)
    (p : SwitchPlace) : carriedFits B ps p = carriedFits B' ps p := by
  simp only [carriedFits, carriedEntryFits, carryE, h]

/-- The second test reads of a book its entries alone. -/
theorem carriedSame_entries {B B' : ProverCoinCounts} (h : B.ahead = B'.ahead) (p₀ p : SwitchPlace) :
    carriedSame B p₀ p = carriedSame B' p₀ p := by
  simp only [carriedSame, carryE, h]

/-- The same, with the list for the book's entries. -/
def bookLitW : ProverCoinCounts := { first := [], shared := [], second := [], cuts := [], ahead := carriedLitA }

theorem carriedFits_of_carry {B B' : ProverCoinCounts} {ps : List SwitchPlace} {p : SwitchPlace}
    (h : carryE B ⟨p.place, 0⟩ = carryE B' ⟨p.place, 0⟩) : carriedFits B ps p = carriedFits B' ps p := by
  simp only [carriedFits, carriedEntryFits, h]

theorem carriedSame_of_carry {B B' : ProverCoinCounts} {p₀ p : SwitchPlace}
    (h₀ : carryE B ⟨p₀.place, 0⟩ = carryE B' ⟨p₀.place, 0⟩)
    (h : carryE B ⟨p.place, 0⟩ = carryE B' ⟨p.place, 0⟩) : carriedSame B p₀ p = carriedSame B' p₀ p := by
  simp only [carriedSame, h₀, h]

theorem carryE_lit {p : SwitchPlace} (hp : p ∈ placesW) :
    carryE bookW ⟨p.place, 0⟩ = carryE bookLitW ⟨p.place, 0⟩ :=
  carry_at_place hp

theorem carryE_rev {p : SwitchPlace} (hp : p ∈ placesW) :
    carryE { bookW with ahead := rawAheadW.reverse } ⟨p.place, 0⟩ =
      carryE { bookLitW with ahead := carriedLitA.reverse } ⟨p.place, 0⟩ := by
  have e := carry_at_place hp
  simp only [carryOf] at e
  simp only [carryE, List.filter_reverse, e]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- BY LEAN's KERNEL, at the list. -/
theorem bookTestsLitW : (placesW.all fun p => carriedFits bookLitW placesW p &&
    placesW.all fun p₀ => decide (p₀.link + 1 ≠ p.link) || carriedSame bookLitW p₀ p) = true := by
  decide +kernel

/-- BY LEAN's KERNEL. -/
theorem bookTestsW : (placesW.all fun p => carriedFits bookW placesW p &&
    placesW.all fun p₀ => decide (p₀.link + 1 ≠ p.link) || carriedSame bookW p₀ p) = true := by
  refine Eq.trans (all_congr_mem ?_) bookTestsLitW
  intro p hp
  have e : (placesW.all fun p₀ => decide (p₀.link + 1 ≠ p.link) || carriedSame bookW p₀ p) =
      placesW.all fun p₀ => decide (p₀.link + 1 ≠ p.link) || carriedSame bookLitW p₀ p :=
    all_congr_mem fun p₀ hp₀ => by rw [carriedSame_of_carry (carryE_lit hp₀) (carryE_lit hp)]
  show (carriedFits bookW placesW p && _) = (carriedFits bookLitW placesW p && _)
  rw [carriedFits_of_carry (carryE_lit hp), e]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem bookTestsW_can_fail_lit :
    ((placesW.take 1).all fun p =>
      carriedFits { bookLitW with ahead := carriedLitA.reverse } placesW p) = false := by
  decide +kernel

/-- A control on the first test. -/
theorem bookTestsW_can_fail :
    ((placesW.take 1).all fun p =>
      carriedFits { bookW with ahead := rawAheadW.reverse } placesW p) = false := by
  refine Eq.trans (all_congr_mem ?_) bookTestsW_can_fail_lit
  exact fun p hp => carriedFits_of_carry (carryE_rev (List.mem_of_mem_take hp))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- By Lean's kernel, at the list. -/
theorem bookTestsW_second_can_fail_lit :
    ((placesW.take 1).all fun p₀ => (placesW.take 2).all fun p =>
      decide (p₀.link + 1 ≠ p.link) ||
        carriedSame { bookLitW with ahead := carriedLitA.reverse } p₀ p) = false := by
  decide +kernel

/-- A control on the second test: with the entries in the reverse order it says no at the first two
places. -/
theorem bookTestsW_second_can_fail :
    ((placesW.take 1).all fun p₀ => (placesW.take 2).all fun p =>
      decide (p₀.link + 1 ≠ p.link) ||
        carriedSame { bookW with ahead := rawAheadW.reverse } p₀ p) = false := by
  refine Eq.trans (all_congr_mem ?_) bookTestsW_second_can_fail_lit
  refine fun p₀ hp₀ => all_congr_mem fun p hp => ?_
  rw [carriedSame_of_carry (carryE_rev (List.mem_of_mem_take hp₀))
    (carryE_rev (List.mem_of_mem_take hp))]

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place} {B : ProverCoinCounts}

/-- h AND hB ARE PREMISES. **Both tests at the book, at a written switch and the one in front.** -/
theorem book_tests_at_head (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (hB : bookWhole (F0T OnBytes.secondHashFunction Zp Np cF) proofSendsFull.1 proofSendsFull.2.1
      proofSendsFull.2.2 (mergesByName (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok B)
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ placesW) (hp : p ∈ placesW) (hl : p₀.link + 1 = p.link) :
    carriedFits B placesW p = true ∧ carriedSame B p₀ p = true := by
  have e : B.ahead = bookW.ahead := ahead_at_book h hB
  have t := List.all_eq_true.1 bookTestsW p hp
  rw [Bool.and_eq_true] at t
  refine ⟨(carriedFits_entries e _ _).trans t.1, ?_⟩
  have q := List.all_eq_true.1 t.2 p₀ hp₀
  rw [Bool.or_eq_true] at q
  rcases q with q | q
  · exact absurd hl (of_decide_eq_true q)
  · exact (carriedSame_entries e _ _).trans q

end AtFullSide.K2

#print axioms AtFullSide.K2.bookW
#print axioms AtFullSide.K2.carriedFits_entries
#print axioms AtFullSide.K2.carriedSame_entries
#print axioms AtFullSide.K2.bookTestsW
#print axioms AtFullSide.K2.bookTestsW_can_fail
#print axioms AtFullSide.K2.bookTestsW_second_can_fail
#print axioms AtFullSide.K2.book_tests_at_head
