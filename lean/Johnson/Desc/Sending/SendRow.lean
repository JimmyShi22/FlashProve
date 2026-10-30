-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sending/SendRow.lean: the general sending and the later moment
(Johnson/Desc/Sending/Send.lean) in the one type of a step of a proof file's chains: state, this
stretch's rounds, the opened columns not yet taken; it returns the state and how many columns it
took, or refuses.

This file holds definitions only; no theorem is stated. No body is written again: each is a wrap.

The type is written out here
(S → List Fmt.RoundView → List (Nat × Nat × List UInt64) → Option (S × Nat)); Johnson/Desc/Step.lean, which
names it, is not imported.
The plan's two entries are parameters of whoever makes the table of rows, not of the step.
A sending takes no column. It refuses a stretch of more or fewer than two rounds.

Main names: usedUp; sendRow (any sending that closes its own round of answers); laterRow (a later
moment).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.Sending.Send

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Send
open OnBytes OnBytes.Params Desc.Plain

variable {L : Type}

/-- What is left of a stretch that a step has used up: the state, and no column taken. -/
def usedUp (m : Mid L) : Option (DState L × Nat) :=
  if m.rounds.isEmpty && m.entries.isEmpty then some (m.d, 0) else none

/-- A sending that closes its own round of answers, as a step. -/
def sendRow (G : Ground L) (p : GPar) (owed : Option Nat) (sent : Array OracleNotice)
    (put : L → Array Nat → List E → List E → L) (e₁ e₂ : Fmt.Entry) (d : DState L)
    (rs : List Fmt.RoundView) (_ : List (Nat × Nat × List UInt64)) : Option (DState L × Nat) :=
  (({ d := d, entries := [e₁, e₂], rounds := rs } : Mid L).send owed sent
    (sendStep G p sent put)).bind usedUp

/-- A later moment of the present link, as a step. -/
def laterRow (G : Ground L) (p : GPar) (owed : Option Nat) (get : L → ReqFrame)
    (put : L → ReqFrame → Array Nat → L) (e₁ e₂ : Fmt.Entry) (d : DState L) (rs : List Fmt.RoundView)
    (_ : List (Nat × Nat × List UInt64)) :
    Option (DState L × Nat) :=
  (laterStep G p owed get put { d := d, entries := [e₁, e₂], rounds := rs }).bind usedUp

end VerifiableInference.Desc.First.Send
