-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/K11RowPile.lean: the item `pile` passes over sub-protocol
number 346 of the first chain, the merge (kind K11), at the invariant at the full size
(`lettersHead`, FirstHead.lean). The general lemma is `ridesPastAt_pile` (RowPileRides.lean). Its
hypothesis on `keeps` comes from the kind's clause `K11Keeps`, which writes out the state after the
step. K11PinRides.lean does the same for `pin`, `pinI` and `unmarked`. For the items `row m c` the
authors of K11's lemmas have `k11RowsRide` (Johnson/Desc/ProofFile/Honest/K11/Plays/RowRides.lean).
No definition.

  1  `k11Keeps_book`, `k11Keeps_rows`   the clause leaves the field `book` and `S.rows`
  2  `k11_rides_pile`   the item passes over number 346

Limits.
  * The hypothesis `hk`, that `keeps` at 346 gives `K11Keeps`, is proved at no `Thread` here.
  * Of the 17 items that pass over number 346, eight are not treated here, in K11PinRides.lean or by
    `k11RowsRide`: six items `forms` and two items `worth`.
  * Full size only, and only under the library's hypothesis `AtMgA` at the hash function `secondHashFunction`
    (FirstAt.lean says which that is).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.RowPileRides
import Johnson.Desc.ProofFile.Honest.Thread.K11PinRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc (Chain Strs Wit Place)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open Johnson.Desc.First.ForkMerge.Returns (K11Keeps)

/-- `K11Keeps` leaves the book of trees as it was. -/
theorem k11Keeps_book {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {s s' : TS}
    (h : K11Keeps P s s') : s'.book = s.book := by
  obtain ⟨⟨a, wo, v, β, -, -, -, -, -, -, rfl⟩, -⟩ := h
  rfl

/-- `K11Keeps` leaves the pending rows on the table of weights as they were. -/
theorem k11Keeps_rows {P : Johnson.Desc.First.ForkMerge.HeadMergeP} {s s' : TS}
    (h : K11Keeps P s s') : s'.rows = s.rows := by
  obtain ⟨⟨a, wo, v, β, ha, -, -, -, -, -, rfl⟩, -⟩ := h
  unfold VerifiableInference.Desc.First.S.rows
  rw [ha]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

/-- The item `pile` passes over sub-protocol number 346. -/
theorem k11_rides_pile (P : Johnson.Desc.First.ForkMerge.HeadMergeP)
    (hk : ∀ s s', (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.keeps 346 s s' →
      K11Keeps P s s') :
    RidesPastAt (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread 346 Item.pile :=
  ridesPastAt_pile h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w fun s s' hK =>
    ⟨k11Keeps_st (hk s s' hK), k11Keeps_book (hk s s' hK), k11Keeps_rows (hk s s' hK)⟩

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.k11Keeps_book
#print axioms ProofFile.Honest.FirstThread.k11Keeps_rows
#print axioms ProofFile.Honest.FirstThread.k11_rides_pile
