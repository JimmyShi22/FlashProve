-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/TestsWritten.lean: the tests with code that the law on the sub-protocol K1 asks
of the table's numbers and of the list of seats, at its fifty later places, AT THE WRITTEN VALUES OF
THE FULL SIZE: closed facts, each with a negative test. Definitions and statements with their
proofs.

THE ARGUMENTS, EACH WITH ITS WRITTEN TERM (their ties stand in their files):
  the numbers' core (sent, keptOf, index, w) · `P5T.N0Full` (Johnson/P5T/PlanSeatsFull.lean)
  the list of seats · `K13.Law.seatsFull` (Johnson/HB/LLHARD/IdxBelowWritten.lean)
  the two counts at the 359 borders · `K13.Law.countsFull` (Johnson/HB/LLHARD/ToldCounts.lean)
  the fifty places with their two counts as numerals · `K13.Law.laterFull`
    (Johnson/HB/LLHARD/PlanAtQFull.lean): segment, piece, moment, oracle messages in front, trees in
    front
  a place's parameters · `parX x` := `parLater qFull gpFull` at a row x of that list
  the request's shape · `shapeFull` (Johnson/Desc/ReqLit/Full.lean)

  `fifty_tie`, `fifty_at`: the row number 2 l + (0 | 1) of `laterFull` is the place (l, d) of the
    law's own letters `noL`, `k1Ix`, `momL`, and its two numerals are `countsFull`'s entry
    `noL l d`. `fifty_tie_rejects`: one border further on they are not.
  `laterSeats_written`: `laterSeatsB`: the seats that the core gives segment l at the moment are
    just the seats of the place's messages, behind the trees in front. `laterSeats_rejects`. (The
    like fact, by segment and moment, is `later_seats` in Johnson/Desc/AtSeats/PlanRestAtCut.lean.)
  `seatsAt_written`: from the count of oracle messages in front on, the list of seats goes on with
    the place's seats. `seatsAt_rejects`: one message earlier it does not.
  `ahead_written`: `aheadAtB` at the 25 digits' places. `ahead_rejects`: one tree earlier.
  `fenceBelowB`, `fence_written`, `fence_rejects`, `fence_at`: along ONE walk of the open sets:
    every tenant with an out-of-domain (OOD) sample whose pin is open at a border sits in a tree in
    front.
  `seats_nodup`: no seat stands twice in the list. `seats_nodup_rejects`.
By evaluations in Lean's kernel (`decide +kernel`): all but `fifty_at` and `fence_at`.
The recursion limit is raised for the elaboration of these evaluations alone (maxRecDepth 1000000).

What is not claimed. That a verifier computes these values: the ties are other files'. Closed facts
on written values. Nothing on soundness.

-/
import Johnson.HB.LLHARD.IdxBelowWritten
import Johnson.HB.LLHARD.PlanAtQFull
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K1.Law.WordsAtPlace
import Johnson.Desc.K1.Law.AheadAtDigits
import Johnson.Desc.K1.Law.TestsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First (Item Numbers flatPlacesOf openSets start sampledIn)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt countsFull laterFull seatsFull gpFull)
open VerifiableInference.Desc.ReqLit (shapeFull)
open P5T (N0Full)
open IM (k1Ix)

/-- The parameters of the place in a row of `laterFull`, at the written values. -/
def parX (x : ℕ × ℕ × ℕ × ℕ × ℕ) : Par := parLater qFull gpFull x.1 x.2.1 x.2.2.1

/-! ## 1 The fifty rows are the law's fifty places -/

theorem fifty_tie : ((List.range 25).all fun l => [false, true].all fun d =>
    decide (laterFull[2 * l + cond d 1 0]? = (countsFull[noL l d]?).map fun c =>
      (l, k1Ix l d + 1, momL d, c.1, c.2)) && (countsFull[noL l d]?).isSome) = true := by
  decide +kernel

/-- The negative test: one border further on the counts are others. -/
theorem fifty_tie_rejects :
    decide (laterFull[2 * 3 + 0]? = (countsFull[noL 3 false + 1]?).map fun c =>
      (3, k1Ix 3 false + 1, momL false, c.1, c.2)) = false := by
  decide +kernel

/-- **At each of the fifty**: the place's row stands in the list, with `countsFull`'s numerals. -/
theorem fifty_at (l : ℕ) (hl : l < 25) (d : Bool) : ∃ m t,
    (l, k1Ix l d + 1, momL d, m, t) ∈ laterFull ∧ countsFull[noL l d]? = some (m, t) := by
  have h := List.all_eq_true.1 (List.all_eq_true.1 fifty_tie l (List.mem_range.2 hl)) d
    (by cases d <;> simp)
  rw [Bool.and_eq_true] at h
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 h.2
  have h1 := of_decide_eq_true h.1
  rw [hc] at h1
  exact ⟨c.1, c.2, List.mem_of_getElem? h1, hc⟩

/-! ## 2 The tests at the fifty -/

theorem laterSeats_written : (laterFull.all fun x =>
    laterSeatsB N0Full (parX x) x.1 x.2.2.1 x.2.2.2.2) = true := by
  decide +kernel

/-- The negative test: behind one tree more. -/
theorem laterSeats_rejects : laterSeatsB N0Full (parX (3, 4, 1, 27, 11)) 3 1 12 = false := by
  decide +kernel

theorem seatsAt_written : (laterFull.all fun x =>
    (List.range (shapesOf (parX x)).length).all fun j =>
      decide (seatsFull[x.2.2.2.1 + j]? = some (seatOfMsg (parX x) x.2.2.2.2 j))) = true := by
  decide +kernel

/-- The negative test: one message earlier; and the place does send a message. -/
theorem seatsAt_rejects :
    decide (seatsFull[26 + 0]? = some (seatOfMsg (parX (3, 4, 1, 27, 11)) 11 0)) = false ∧
      0 < (shapesOf (parX (3, 4, 1, 27, 11))).length := by
  decide +kernel

theorem ahead_written : (laterFull.all fun x => x.2.2.1 != 2 ||
    aheadAtB shapeFull (N0Full.sent x.1) (parX x) x.1
      (cntAt shapeFull x.1 0 + cntAt shapeFull x.1 1) x.2.2.2.2) = true := by
  decide +kernel

/-- The negative test: behind one tree fewer. -/
theorem ahead_rejects : aheadAtB shapeFull (N0Full.sent 3) (parX (3, 6, 2, 28, 12)) 3
    (cntAt shapeFull 3 0 + cntAt shapeFull 3 1) 11 = false := by
  decide +kernel

/-! ## 3 The fence -/

/-- A test: along the borders, every tenant with a sample whose pin is open at a border sits in a
tree below that border's count of trees. cnt: for each border the oracle messages and the trees in
front. ONE walk of the open sets. -/
def fenceBelowB (N : Numbers) (cnt : List (ℕ × ℕ)) : Bool :=
  ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).zip cnt).all fun x =>
    (sampledIn N x.1).all fun u => decide (u.1 < x.2.2)

theorem fence_written : fenceBelowB N0Full countsFull = true := by decide +kernel

/-- The negative test: with each border's counts taken one border earlier. -/
theorem fence_rejects : fenceBelowB N0Full ((0, 0) :: countsFull) = false := by decide +kernel

/-- So at each border. -/
theorem fence_at {k : ℕ} {c : ℕ × ℕ} (hc : countsFull[k]? = some c) :
    ∀ u ∈ sampledIn N0Full (openAt linksFull (flatPlacesOf linksFull true) k), u.1 < c.2 := by
  intro u hu
  unfold openAt at hu
  cases hO : (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]? with
  | none =>
    rw [hO] at hu
    exact (List.not_mem_nil (show u ∈ ([] : List (ℕ × ℕ)) from hu)).elim
  | some O =>
    rw [hO] at hu
    have hz : ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull)).zip
        countsFull)[k]? = some (O, c) := List.getElem?_zip_eq_some.2 ⟨hO, hc⟩
    have a := List.all_eq_true.1 fence_written _ (List.mem_of_getElem? hz)
    exact of_decide_eq_true (List.all_eq_true.1 a u hu)

/-! ## 4 The list of seats -/

theorem seats_nodup : seatsFull.Nodup := by decide +kernel

/-- The negative test: with its fifth seat once more in front. -/
theorem seats_nodup_rejects : ¬ ((1, 0) :: seatsFull).Nodup := by decide +kernel

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.fifty_tie
#print axioms VerifiableInference.Desc.K1.fifty_tie_rejects
#print axioms VerifiableInference.Desc.K1.fifty_at
#print axioms VerifiableInference.Desc.K1.laterSeats_written
#print axioms VerifiableInference.Desc.K1.laterSeats_rejects
#print axioms VerifiableInference.Desc.K1.seatsAt_written
#print axioms VerifiableInference.Desc.K1.seatsAt_rejects
#print axioms VerifiableInference.Desc.K1.ahead_written
#print axioms VerifiableInference.Desc.K1.ahead_rejects
#print axioms VerifiableInference.Desc.K1.fence_written
#print axioms VerifiableInference.Desc.K1.fence_rejects
#print axioms VerifiableInference.Desc.K1.fence_at
#print axioms VerifiableInference.Desc.K1.seats_nodup
#print axioms VerifiableInference.Desc.K1.seats_nodup_rejects
