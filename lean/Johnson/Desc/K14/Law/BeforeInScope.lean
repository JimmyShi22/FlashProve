-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/BeforeInScope.lean: the field "before" of `Written Z x`
(Johnson/Goal/Numbers/WrittenAtZ.lean) at the public part Z of the IOP as written in Lean, where
the value is laid: with no premise beside these two. Two statements with their proofs.

  `seatChainOk`: the premise `SeatChainOk` (Johnson/Desc/K14/Law/BeforeOfSeatChain.lean) holds at
    all files: by `chain_at_descPure` (Johnson/Desc/K14/Law/LedgerSeatChain.lean).
  `before_in_scope`: **the statement**: from "the public part is made" and "the value is laid"
    (`proofDataAndDecisionOfPublicFiles`, Johnson/Desc/Laid/ProofFull.lean): wherever the four places of the proximity tests
    are made of Z, `beforePointOf` at them is not empty. The goals' scope is not asked.

Can the premises be met? That the public part is made and the value is laid at any files is the
reference run's to show; no theorem. Limits. Nothing on which message is named. Nothing on
soundness.
-/
import Johnson.Desc.K14.Law.BeforeOfSeatChain
import Johnson.Desc.K14.Law.LedgerSeatChain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open VerifiableInference.OnPublicFiles

/-- The premise of `before_of_seatChain` holds at all files. -/
theorem seatChainOk (o : ProofFile.SecondHashFunctionArgument) (pol lay KL : ByteArray) : SeatChainOk o pol lay KL :=
  fun _ hF hp =>
    let ⟨Z, N, hZ, hN, hc, _⟩ := chain_at_descPure hF hp
    ⟨Z, N, hZ, hN, hc⟩

/-- **"before" at the public part of the IOP as written in Lean**, where the value is laid. -/
theorem before_in_scope {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {Z : ProofFile.Pub} {D} {r}
    (h : ProofFile.pureRoad.pub o pol lay KL = .ok Z)
    (hl : LPFD.Full.proofDataAndDecisionOfPublicFiles o pol lay KL = .ok (D, r)) :
    ∀ N, H2U.placesOfMade Z.made = .ok N → beforePointOf N ≠ [] :=
  before_of_seatChain (seatChainOk o pol lay KL) h hl

end Desc.K14.Law

#print axioms Desc.K14.Law.seatChainOk
#print axioms Desc.K14.Law.before_in_scope
