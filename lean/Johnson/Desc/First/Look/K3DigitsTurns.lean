-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3DigitsTurns.lean: the lookup on the digits of a link's smallness test:
WHAT A YES OF K3.block's decide LEAVES IN THE CARRIED RECORD: SameBut
(Johnson/Desc/First/Look/K3CallsTurns.lean) at the digits' seat: the record's eight fields beside
«here», the link's context and the sort of «here» do not turn. Statements and proofs. A tie: no
error term.

Main names.
  putDigits_sameBut: of what the digits' seat lays, where a ledger is open.
  k3_digits_sameBut: of a yes of decide.
  k3_digits_mark_stays: so a mark stays, and none comes.
OBJECT. Desc.K3.block's decide at Desc.K3.seatDigits, as K3.theOwn lays it where digits = true.
USER. K3DigitsSeatedYes.lean, K3DigitsStep.lean, Johnson/Top/H/Keep/K3PassOf.lean and
Johnson/Desc/Kinds/Law/DigitsKeptAtDecide.lean
call k3_digits_sameBut.
LETTERS. claim, piece, laid, before, p, guests: free.
Compiled with the whole library.
Limits. SameBut SAYS NOTHING OF THE REST OF THE OPEN LINK's OWN PART (what the other lookup heard,
the caller's fields): the proof of putDigits_sameBut knows more than its statement keeps. At the
digits' seat alone. It speaks of the record; that the oracles' strings in front of the block's base
stay is the rule's (Johnson/Desc/Sound/StringsStay.lean).
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

theorem putDigits_sameBut {Cl : Type} (claim : Aff → Cl) (s : Desc.First.S) (g : Forest.Heard)
    (F Gk : Fork) (hF : (Desc.K3.seatDigits claim).fork s = some F) :
    SameBut s ((Desc.K3.seatDigits claim).put s g Gk) := by
  simp only [Desc.K3.seatDigits] at hF ⊢
  cases hh : s.here with
  | between => simp [Desc.First.S.fork?, hh] at hF
  | fin _ => simp [Desc.First.S.fork?, hh] at hF
  | mem _ => simp [Desc.First.S.fork?, hh] at hF
  | lay a =>
    constructor <;>
      simp [Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
        Desc.First.S.link?, hh]
  | att a =>
    constructor <;>
      simp [Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
        Desc.First.S.link?, hh]
  | head a =>
    cases ho : a.opened with
    | false => simp [Desc.First.S.fork?, hh, ho] at hF
    | true =>
      constructor <;>
        simp [Desc.First.S.tl?, Desc.First.S.fork?, Desc.First.S.putTl, Desc.First.S.putFork,
          Desc.First.S.link?, hh, ho]

/-- **A yes of decide at the digits leaves what SameBut names.** -/
theorem k3_digits_sameBut {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') : SameBut s s' := by
  obtain ⟨F, y, hF, -, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putDigits_sameBut claim s y.1 F y.2 hF

/-- So a mark stays, and none comes. -/
theorem k3_digits_mark_stays {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) (s s' : Desc.First.S)
    (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide s rs cols =
      .ok s') : s'.failed = s.failed :=
  (k3_digits_sameBut claim piece laid before p guests s s' rs cols h).failed

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.putDigits_sameBut
#print axioms VerifiableInference.OnPublicFiles.k3_digits_sameBut
#print axioms VerifiableInference.OnPublicFiles.k3_digits_mark_stays
