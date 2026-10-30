-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HasCoinsWritten.lean: THE SHARED "SENDING" (the kind K1) AND
THE MAKER OF THE BOOK OF COINS: TWO HANDS, ONE COUNT: AT THE LIBRARY's WRITTEN DESCRIPTION AND
WRITTEN SENDINGS THE MAKER's ROWS OF THE FIRST CHAIN (rowsIn, Honest/BookRows.lean) HAVE, AT THE
ADDRESS OF EACH OF THE KIND's 52 SENDERS, A ROW, AND ITS COUNT IS OUR dueR (Honest/K1/Coins.lean) AT
THE SENDER's WRITTEN PLAN AND RIDE. PUBLIC DATA ALONE: how many coins a part has, never what they
are. Six theorems; no definition.

For what. The record of premises K1Seated (Honest/K1/Seated.lean) has a field hasCoins: the book's
count at ⟨J.P.place, 0⟩ is dueR J.P J.ride. It can be paid only at a named book. This is its closed
half: at the written data.

The written data. P2Law.ProofPlan.WP (Johnson/AtFull/ProofPlan/WP.lean): its first chain's flat list
and its second chain's rounds · Johnson.G.proofSendsFull.1 (Johnson/G/SendsWritten.lean) · the plans
K1.parGF, K1.placeL l d, K1.parWF, with the rides that placeJob lays: rideOf (firstFold K1.qFull),
rideOf none, rideOf (wFold K1.qFull.lin).

  - k1RowsW: the closed fact, by evaluation in Lean's kernel: rowsIn returns a list; in it the
    look-up at the opening's address, at each of the fifty's and at W's is SOME, and is our dueR.
    rowsIn asks of each sending whether it is a code switch, by String.splitOn, which the kernel
    does not unfold: the library's Johnson.Unfolds.splitOn_eq (Johnson/Unfolds/SplitOn.lean) leads
    it past.
  - k1RowsW_bites: A NEGATIVE TEST: AT EACH OF THE FIFTY the look-up is NOT the count of the link's
    other later sending ("digits" for "reads" and back).
  - k1RowsW_ride_bites, k1RowsW_rideW_bites: NEGATIVE TESTS: at the opening, and at W's sending,
    without the ride our count is another.
  - hasCoinsW: the same as sentences: there is a list that rowsIn returns, and dueAt of it at the 52
    addresses is dueR. (It says less than k1RowsW, which says that a row is there: dueAt has a
    default.)
  - hasCoinsW_head: UNDER h (the library's head: A HYPOTHESIS), O: at the plans and rides of the
    description's own ground, at the opening and the fifty.

Kin. Another house holds rowsIn's list at the same terms as 77 spelled rows (rowsIn_first_written),
and the raw book's three tables: not stated here; not called. What it has not is the tie of a row's
count to dueR: that is this file's.

Limits. THE WRITTEN DATA: that the prover's own book's first table begins with this list is not said
here: that wants (a) what "bookWhole returns" gives of the first table · (b) the congruence from the
head's description to WP · (c) that the maker's sendings are the written ones. THE FULL SIZE ALONE.
THE FIRST CHAIN ALONE: rows of the kind K1 in the shared chain's table are not here. W's plan under
the head: another file's. Evaluations in Lean's kernel (decide +kernel): no compiled code. Nothing
on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.K1.PlaceW
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.AtFull.ProofPlan.WP
import Johnson.G.SendsWritten
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF parWF placeL fiftyB fifty_of)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- **THE TWO HANDS' COUNTS AT THE 52 ADDRESSES, AT THE WRITTEN DATA.** -/
theorem k1RowsW :
    (match (rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds))) with
    | .ok r =>
      decide (r.lookup (⟨parGF.place, 0⟩ : Addr) =
          some (dueR parGF (rideOf (firstFold K1.qFull)))) &&
        (fiftyB fun l d => decide (r.lookup (⟨(placeL l d).place, 0⟩ : Addr) =
          some (dueR (placeL l d) (rideOf none)))) &&
        decide (r.lookup (⟨parWF.place, 0⟩ : Addr) =
          some (dueR parWF (rideOf (wFold K1.qFull.lin))))
    | .error _ => false) = true := by
  unfold rowsIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- A negative test: AT EACH OF THE FIFTY the look-up is not the other later sending's count. -/
theorem k1RowsW_bites :
    (match (rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds))) with
    | .ok r => fiftyB fun l d => !decide (r.lookup (⟨(placeL l d).place, 0⟩ : Addr) =
        some (dueR (placeL l (!d)) (rideOf none)))
    | .error _ => false) = true := by
  unfold rowsIn isSwitch
  simp only [Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- A negative test: at the opening, without the ride, our count is another. -/
theorem k1RowsW_ride_bites :
    dueR parGF (rideOf none) ≠ dueR parGF (rideOf (firstFold K1.qFull)) := by
  decide +kernel

/-- A negative test: at W's sending, without the ride, our count is another. -/
theorem k1RowsW_rideW_bites :
    dueR parWF (rideOf none) ≠ dueR parWF (rideOf (wFold K1.qFull.lin)) := by
  decide +kernel

/-- **THE SAME AS SENTENCES**: the closed half of the record's field hasCoins. It says less than
k1RowsW: dueAt has a default, ⟨0, 0⟩, where the list has no row; k1RowsW says that a row is there.
-/
theorem hasCoinsW : ∃ rs, (rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds))) = .ok rs ∧
    dueAt rs ⟨parGF.place, 0⟩ = dueR parGF (rideOf (firstFold K1.qFull)) ∧
    (∀ l, l < 25 → ∀ d, dueAt rs ⟨(placeL l d).place, 0⟩ = dueR (placeL l d) (rideOf none)) ∧
    dueAt rs ⟨parWF.place, 0⟩ = dueR parWF (rideOf (wFold K1.qFull.lin)) := by
  have h := k1RowsW
  cases e : (rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds))) with
  | error s =>
    rw [e] at h
    simp at h
  | ok rs =>
    rw [e] at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨rs, rfl, ?_, ?_, ?_⟩
    · unfold dueAt
      rw [h.1.1]
      rfl
    · intro l hl d
      have := of_decide_eq_true (fifty_of h.1.2 l hl d)
      unfold dueAt
      rw [this]
      rfl
    · unfold dueAt
      rw [h.2]
      rfl

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **AT THE PLANS AND RIDES OF THE DESCRIPTION's OWN GROUND**, under the head: the opening and the
fifty. -/
theorem hasCoinsW_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) : ∃ rs, (rowsIn P2Law.ProofPlan.WP.first.blocksInOrder
          Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds))) = .ok rs ∧
    dueAt rs ⟨(K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place, 0⟩ =
      dueR (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) ∧
    ∀ l, l < 25 → ∀ d, dueAt rs ⟨(K1.parL Zp Bs.G₀ l d).place, 0⟩ =
      dueR (K1.parL Zp Bs.G₀ l d) (rideOf none) := by
  obtain ⟨rs, e, h1, h2, -⟩ := hasCoinsW
  refine ⟨rs, e, ?_, ?_⟩
  · rw [K1.eG_atAll h O (K1.pin1_atAll h),
      firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
    · exact h1
    · rfl
  · intro l hl d
    rw [parL_written h O l d]
    exact h2 l hl d

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1RowsW
#print axioms ProofFile.Honest.K1.k1RowsW_bites
#print axioms ProofFile.Honest.K1.k1RowsW_ride_bites
#print axioms ProofFile.Honest.K1.k1RowsW_rideW_bites
#print axioms ProofFile.Honest.K1.hasCoinsW
#print axioms ProofFile.Honest.K1.hasCoinsW_head
