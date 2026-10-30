-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/AtDescLotsSpenders.lean: wherever the maker returns (IM.Open), at each job of
the two lots of the kind K1, the field fresh needs its premise on the book only at the addresses
that have a spending entry on its coins. It claims no property of the protocol: not hiding, not zero
knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. The premise is IM.Open. J is any job of lotJobs and wJobs, and σ any side that
Side.seated returns at J's place for our row.
  freshAtLots_of_spenders   For every book and order: if, at each address that has a spending entry
                            on the coins of J's sender, the entries that this address spends or
                            knows are within the sender's number of coins and the address is clear
                            (SpendersClearAny, Johnson/SendSim/At/SpendersAlone.lean), then σ has
                            fresh.
  freshAtLots_idle          So, if no address has a spending entry on the coins of J's sender, σ has
                            fresh with no further premise on the book. This says little: the coins
                            that fresh speaks of are then none, and both sides of its equation are
                            the same distribution.
  spendersAny_of_clearAny   BookClearAny implies SpendersClearAny. So the premise here asks no more
                            of the book than part (3) of Spec.fieldsAtLots does.

How it fits. A corollary beside Spec.fieldsAtLots (AtDescLots.lean). It serves a test on the book
that runs over the owners and spenders of spending entries alone (lotsOkB, LotsGuard.lean): such a
test never asks anything at a sender of whom nobody spends. Where the request's shape is the
library's full-size value, at a book that is clear at a segment's reads or digits no address spends
a coin of that sender (clear_at_later_open, LotsTestTie.lean). It rests on seatedAt_job
(AtDescStands.lean) and sendFreshAtSpendersWide (Johnson/SendSim/At/SpendersAloneProofs.lean). Meant
as steps toward index privacy (Johnson/WholeKey/Statement.lean); nothing in this folder derives
index privacy from them. Not one of the release's goal statements.

Limits. All limits of AtDescLots.lean hold here too. An address to which coins are carried alone
spends nothing; of what is known at such an address nothing is said.
-/
import Johnson.SendSim.Seat.AtDescLots
import Johnson.SendSim.At.SpendersAloneProofs

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Params OnBytes.Slice VerifiableInference.Desc
open OnBytes.SendSim.At

variable {V W X Xi Pb : Type}

/-- The premise of part (3) of Spec.fieldsAtLots implies the premise at the spenders alone. -/
theorem spendersAny_of_clearAny {P : K1.Par} {ride : Nat → Option Ride} {Bk : ProverCoinCounts}
    {ord : List Place} {a : Addr} (h : BookClearAny P ride Bk ord a) :
    SpendersClearAny P ride Bk ord a :=
  fun p _ => ⟨withinAt_of_takes h.1 ord p, h.2 p⟩

section
variable {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub}
  {Bs : ProofFile.PureBase} {base : List (Block First.S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain First.S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **Where the description's maker returns, at every job of the two lots, fresh follows from the
premise at the spenders alone.** -/
theorem freshAtLots_of_spenders (O : IM.Open o pol lay KL F Z Bs base c A B) (φ : Face V W Pb)
    (wit : W → PlaceIn Xi)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) {fs : List (Fall F.S₁)}
    {σ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (jobRow (V := V) (Pb := Pb) wit J).place (jobRow wit J).row fs =
      some σ) (Bk : ProverCoinCounts) (ord : List Place)
    (hB : SpendersClearAny J.P J.ride Bk ord ⟨J.P.place, 0⟩) :
    FreshAt φ σ Bk ord (jobRow (V := V) (Pb := Pb) wit J).bud :=
  At.sendFreshAtSpendersWide _ _ V W X Pb φ σ (jobOver J wit) Bk ord
    (seatedAt_job O wit no D hJ hσ)
    (by rw [place_of_seated hσ]; exact hB)

/-- Where the description's maker returns: if no address has a spending entry on the coins of the
job's sender, fresh holds with no further premise on the book. It says little: no coin is then
spoken of. -/
theorem freshAtLots_idle (O : IM.Open o pol lay KL F Z Bs base c A B) (φ : Face V W Pb)
    (wit : W → PlaceIn Xi)
    (no : Place → Nat) (D : ProofFile.Pub → ProofFile.Ground → RowDataOf Xi) {J : SendJob (PlaceIn Xi) X}
    (hJ : J ∈ lotJobs no D Z Bs.G₀ ++ wJobs no D Z Bs.G₀) {fs : List (Fall F.S₁)}
    {σ : Side F.S₁ F.Cl V W X Pb}
    (hσ : Side.seated F.first.blocksInOrder (jobRow (V := V) (Pb := Pb) wit J).place (jobRow wit J).row fs =
      some σ) (Bk : ProverCoinCounts) (ord : List Place)
    (h0 : ∀ p, Bk.spentBy ⟨J.P.place, 0⟩ p = []) :
    FreshAt φ σ Bk ord (jobRow (V := V) (Pb := Pb) wit J).bud :=
  freshAtLots_of_spenders O φ wit no D hJ hσ Bk ord fun p hp => absurd (h0 p) hp

end

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.spendersAny_of_clearAny
#print axioms OnBytes.SendSim.Seat.freshAtLots_of_spenders
#print axioms OnBytes.SendSim.Seat.freshAtLots_idle
