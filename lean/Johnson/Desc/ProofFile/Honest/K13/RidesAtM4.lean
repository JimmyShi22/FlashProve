-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K13/RidesAtM4.lean: WHICH ITEMS GO PAST THE SUB-PROTOCOL AT THE PLACE
"M:4", AND THE SHARE OF `RidesPast` AT THE ITEM "unmarked". Statements with their proofs.

An item goes past a sub-protocol where it is open in front, and the forward row neither shuts it nor
owes it (`passBy`, RidesAtM3.lean of this folder). `RidesPast` (Honest/Thread/Pays.lean) is cut into
shares, one an item (`RidesPastAt`, `ridesPast_of`: Thread/Shares.lean).
Main names:
  `m4_open_is`, `m4_none_shut`, `m4_pass_is`: **at the library's own lists and number 356, by the
    kernel**: just four items are open in front: "unmarked", `pinI`, `pinW`, `pileOne`; the row
    shuts none; JUST TWO GO PAST: "unmarked" AND `pinI`. (The row owes `pinV`, `pileOne`, `pinW`,
    `wrow`: `owes_at_m4`, ExchangeM4Proof.lean. Number 356 of these lists is the place "M:4":
    `m4_place`, ExchangeM4At.lean, by the kernel too.) The first two are stated for the reader: no
    theorem calls them.
  `k13_m4_unmarked`: **the share at "unmarked"**, at every thread of the first chain's form. IT IS
    ITS PREMISE hkeep, UNFOLDED: the item "unmarked" says failed = none; hkeep asks of the field
    `keeps` that it give failed = none behind.
  `k13_m4_rides`: **`RidesPast` at a border past which these two alone go**, from that and the share
    at `pinI`: A PREMISE: `pinI` is the pin of the index masks' message: whoever fills that item
    shows its share; what it has of this sub-protocol is `keeps`: of the second half:
    `K13RowsKeeps.same` (Johnson/Desc/K13/Honest/RowsKeeps.lean): every oracle message's sample rows
    stay.
  `k13_m4_rides_at`: **the same at number 356 of the thread at the library's own parameters**:
    `m4_pass_is` is spent there.

What is not claimed. The share at `pinI`. hkeep: the field `keeps` has no text at the library's own
parameters. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.RidesAtM3
import Johnson.Desc.ProofFile.Honest.Thread.Shares
import Johnson.Desc.ProofFile.Honest.K13.ExchangeM4At

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K13
open VerifiableInference.Desc.First (S Item start)
open VerifiableInference.Desc (Chain Strs)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (Letters lettersAt Script WtF)

set_option maxRecDepth 100000 in
/-- Just four items are open at the border number 356. -/
theorem m4_open_is :
    (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 356).length = 4 ∧
    ([Item.unmarked, Item.pinI, Item.pinW, Item.pileOne].all fun i =>
      (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 356).contains i) =
        true := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The forward row number 356 shuts none. -/
theorem m4_none_shut : (FirstRows.rows P5J.At.links P5J.At.ps 356).shuts = [] := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- **Whatever goes past number 356 is "unmarked" or `pinI`**; and both do. -/
theorem m4_pass_is :
    ((passBy (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 356)
      (FirstRows.rows P5J.At.links P5J.At.ps 356)).all fun i =>
        i == Item.unmarked || i == Item.pinI) = true ∧
    ([Item.unmarked, Item.pinI].all fun i =>
      (passBy (fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 356)
        (FirstRows.rows P5J.At.links P5J.At.ps 356)).contains i) = true := by
  decide +kernel

variable {Bk : ProverCoinCounts} {Cl W₀ Rc Xi Tr X Pp Cells Tok M : Type}
  (L : Letters Bk Cl W₀ Rc Xi Tr X Pp Cells Tok M)

/-- **The share at "unmarked".** hkeep: what is asked of the field `keeps`. -/
theorem k13_m4_unmarked {b : Nat}
    (hkeep : ∀ k s m En s', Thr L.thread b k s m En → L.keeps b s s' → s'.failed = none) :
    RidesPastAt L.thread b Item.unmarked :=
  fun k s m En s' _ _ hT hk _ => hkeep k s m En s' hT hk

/-- **`RidesPast` at a border past which these two alone go.** hI: the share at `pinI`. -/
theorem k13_m4_rides {b : Nat}
    (hO : ((passBy (L.thread.opened b) (L.thread.row b)).all fun i =>
      i == Item.unmarked || i == Item.pinI) = true)
    (hkeep : ∀ k s m En s', Thr L.thread b k s m En → L.keeps b s s' → s'.failed = none)
    (hI : RidesPastAt L.thread b Item.pinI) : RidesPast L.thread b := by
  refine ridesPast_of L.thread fun i h1 h2 h3 => ?_
  have hi := List.all_eq_true.1 hO i (mem_passBy h1 h2 h3)
  rcases Bool.or_eq_true_iff.1 hi with e | e
  · rw [beq_iff_eq.1 e]
    exact k13_m4_unmarked L hkeep
  · rw [beq_iff_eq.1 e]
    exact hI

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`RidesPast` at number 356 of the thread at the library's own parameters**: there
`m4_pass_is` is spent. That number 356 is the place "M:4": `m4_place` (ExchangeM4At.lean). -/
theorem k13_m4_rides_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr X : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) X))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop)
    (hkeep : ∀ k s m En s',
      Thr (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 k s m
        En → keeps 356 s s' → s'.failed = none)
    (hI : RidesPastAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      356 Item.pinI) :
    RidesPast (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread 356 :=
  k13_m4_rides _ m4_pass_is.1 hkeep hI

end ProofFile.Honest.K13

#print axioms ProofFile.Honest.K13.m4_open_is
#print axioms ProofFile.Honest.K13.m4_none_shut
#print axioms ProofFile.Honest.K13.m4_pass_is
#print axioms ProofFile.Honest.K13.k13_m4_unmarked
#print axioms ProofFile.Honest.K13.k13_m4_rides
#print axioms ProofFile.Honest.K13.k13_m4_rides_at
