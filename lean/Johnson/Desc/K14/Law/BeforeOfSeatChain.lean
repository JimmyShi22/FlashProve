-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BeforeOfSeatChain.lean: the field "before" of `Written Z x`
(Johnson/Goal/Numbers/WrittenAtZ.lean) at the public part Z of the IOP as written in Lean, where the
value is laid: UNDER ONE NAMED PREMISE, `SeatChainOk`. A definition and two statements with proofs.

  `before_of_chain`: where the shared chain's sub-protocols (our files: blocks), as they are seated,
    pass their tests on the list of rounds, `beforePointOf N` is not empty: by
    `ToldDesc.blocksOr_ok` (ToldDesc/PlacesAtTable.lean) and `before_at_seat`
    (Johnson/Desc/K14/Law/BeforeOfAll.lean).
  `SeatChainOk o pol lay KL`: THE PREMISE: the first three clauses of
    `chain_at_descPure` (Johnson/Desc/K14/Law/LedgerSeatChain.lean), to the letter, by reading. It
    is a premise here so that this file stands without what that file imports beside; it is paid in
    Johnson/Desc/K14/Law/BeforeInScope.lean.
  `before_of_seatChain`: from the premise, "the public part is made" and "the value is laid"
    (`proofDataAndDecisionOfPublicFiles`, Johnson/Desc/Laid/ProofFull.lean).

Can the premises be met? `SeatChainOk`: a theorem of another file. That the public part is made and
the value is laid at any files: the reference run's to show; no theorem. Limits. Nothing on which
message is named. Nothing on soundness.
-/
import Johnson.Desc.K14.Law.BeforeOfAll
import Johnson.Desc.Laid.ProofFullLaw
import Johnson.ToldDescR.PlacesAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.Desc (Block FileDescription blocksOk)
open VerifiableInference.OnPublicFiles

/-- Where the shared chain's sub-protocols, as they are seated, pass their tests on the list of
rounds, a message is named. -/
theorem before_of_chain (c : OnBytes.Model.Verify.Chains) (N : H2U.Places4)
    (ts : List (Block St Unit)) (last : List (Block St Unit) → Block St Unit)
    (h : blocksOk (chainOf c (p14Of c (beforePointOf N)) ts last).blocksInOrder = true) :
    beforePointOf N ≠ [] :=
  before_at_seat c N (ToldDesc.blocksOr_ok c _ ts last h)

/-- What is asked of the seat: where the IOP as written in Lean is made and passes its tests on the
list of rounds, the shared chain's sub-protocols at the seat's own parameters pass theirs. -/
def SeatChainOk (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : Prop :=
  ∀ F : FileDescription ProofFile.Inst, ProofFile.onlineDescription o pol lay KL = .ok F → F.planOk = true →
    ∃ (Z : ProofFile.Pub) (N : H2U.Places4), ProofFile.pureRoad.pub o pol lay KL = .ok Z ∧
      H2U.placesOfMade Z.made = .ok N ∧
      blocksOk (chainOf Z.p.chains (p14Of Z.p.chains (beforePointOf N))
        (VerifiableInference.Desc.K12.Seat.tests N)
        VerifiableInference.Desc.K12.Seat.last).blocksInOrder = true

/-- **"before" at the public part of the IOP as written in Lean**, where the value is laid. -/
theorem before_of_seatChain {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub}
    {D} {r} (hS : SeatChainOk o pol lay KL)
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∀ N, H2U.placesOfMade Z.made = .ok N → beforePointOf N ≠ [] := by
  intro N hN
  obtain ⟨F, hF, hp, -⟩ := LPFD.Full.laidPOf_ok hl
  obtain ⟨Z', N', hZ', hN', hc⟩ := hS F hF hp
  obtain rfl : Z' = Z := Except.ok.inj (hZ'.symm.trans h)
  obtain rfl : N' = N := Except.ok.inj (hN'.symm.trans hN)
  exact before_of_chain _ _ _ _ hc

end Desc.K14.Law

#print axioms Desc.K14.Law.before_of_chain
#print axioms Desc.K14.Law.before_of_seatChain
