-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K12/HandedAtHeadW.lean: THE SEVEN WRITTEN ENTRIES THAT W's PAIR CARRIES: OWNER AND
START, EACH: owner and start at
all seven: three to the first part, four to the second. Evaluations in Lean's kernel.
PUBLIC DATA ALONE.

  `entries_W`, `entries_W_bite`   to each part, in the book's order: each entry's owner and start:
                 the starts against `K1.startR`; Omega's start a literal 0; a control

Limits.
- OF THE SEVEN STARTS, THREE CAN SAY NO: the index-mask message's at both parts, W's second at the
  second; W's first is `startR` at 0, Omega's a literal: those four hold by make. All seven owners
  can say no.
- OF THE WRITTEN LIST `rawCarriesWW`: the lending is at the maker's book: the bridge is
  `bookWhole_returns_written_ahead`: not called here.
- Numbers against numbers: that a sender lays its message's run there is `K1.rowsR`'s text.
- What may be said of this pair on hiding stands in the head of
  Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean.
- The full size alone. It moves no count. Nothing on completeness, soundness or hiding.
Terms: Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import AtFullSide.K12.LendsAtHeadW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K12
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open AtFullSide.K14 (rawCarriesWW)

/-- The index-mask message's start, by the sender's reckoning. -/
abbrev startI : Due :=
  K1.startR VerifiableInference.Desc.K1.parGF
    (ProofFile.Honest.K1.firstRide VerifiableInference.Desc.K1.qFull)
    (VerifiableInference.Desc.K1.parGF.sent.size - 1)

/-- W's messages' starts, by the sender's reckoning. -/
abbrev startW (k : Nat) : Due :=
  K1.startR VerifiableInference.Desc.K1.parWF
    (ProofFile.Honest.K1.rideOf (ProofFile.Honest.K1.wFold VerifiableInference.Desc.K1.qFull.lin)) k

set_option maxRecDepth 1000000 in
/-- **EACH OF THE SEVEN: OWNER AND START.** The first part is carried the three members; the second
those and W's fresh table. -/
theorem entries_W :
    (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 0⟩).map (fun e => (e.owner, e.start)) =
      [(senderI, startI), (senderW, startW 0), (senderO, ⟨0, 0⟩)] ∧
    (rawCarriesWW.filter fun e => e.spender == ⟨placeW, 1⟩).map (fun e => (e.owner, e.start)) =
      [(senderI, startI), (senderW, startW 0), (senderO, ⟨0, 0⟩), (senderW, startW 1)] ∧
    rawCarriesWW.length = 7 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The evaluation can fail: with the first part's owners turned it says no. -/
theorem entries_W_bite :
    decide ((rawCarriesWW.filter fun e => e.spender == ⟨placeW, 0⟩).map
      (fun e => (e.owner, e.start)) =
      [(senderW, startW 0), (senderI, startI), (senderO, ⟨0, 0⟩)]) = false := by decide +kernel

end AtFullSide.K12

#print axioms AtFullSide.K12.startI
#print axioms AtFullSide.K12.startW
#print axioms AtFullSide.K12.entries_W
#print axioms AtFullSide.K12.entries_W_bite
