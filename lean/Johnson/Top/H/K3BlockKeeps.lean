-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3BlockKeeps.lean: the kind "lookup" (K3): what one place's BLOCK leaves of what the
link's other place has heard. Statements and proofs.

Johnson/Top/H/K3DecideMore.lean says it of the seats' `put` and `mark`. A caller
asks it of the block's own field decide. Here it is, by decide's unfolding (decide_ok).

Main names:
  `digitsBlock_keeps_calls`: where K3.block at the seat on the digits says yes, what the seat on the
    link's calls reads as heard is what it read in front.
  `callsBlock_keeps_digits`: the other way round.

Limits. Of decide alone, at the two seats of Johnson/Desc/First/Look/K3Seat.lean. The runs of claims
lay a ledger by `mark`: K3DecideMore.lean's mark_keeps_calls, mark_keeps_digits. Nothing is said of
any other kind's block between the two places. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideMore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K3 (seatCalls seatDigits)

/-- The block at the digits leaves what was heard at the calls. -/
theorem digitsBlock_keeps_calls {Cl Cl' : Type} (claim : Aff → Cl) (claim' : Aff → Cl')
    (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (seatDigits claim) piece laid before p guests).decide s rs cols = .ok s') :
    (seatCalls claim').heard s' = (seatCalls claim').heard s := by
  obtain ⟨F, x, -, -, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact digits_keeps_calls claim claim' s x.1 x.2

/-- The block at the calls leaves what was heard at the digits. -/
theorem callsBlock_keeps_digits {Cl Cl' : Type} (claim : Aff → Cl) (claim' : Aff → Cl')
    (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl)) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (seatCalls claim) piece laid before p guests).decide s rs cols = .ok s') :
    (seatDigits claim').heard s' = (seatDigits claim').heard s := by
  obtain ⟨F, x, -, -, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact calls_keeps_digits claim claim' s x.1 x.2

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.digitsBlock_keeps_calls
#print axioms VerifiableInference.OnPublicFiles.callsBlock_keeps_digits
