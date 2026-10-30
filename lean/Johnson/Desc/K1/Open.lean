-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Open.lean: the kind K1's own decision where the sending does not close its own round
of answers: the answers are the first items of a round in which the caller goes on (a code switch).

decideOpen is decideSend (Johnson/Desc/K1/Own.lean) at the second round cut to its first
P.answers items: one text, no clause written twice. It returns the new messages' numbers, how many
items of the second round it took, and the state. Of the second round it reads these items alone:
nothing is asked of what that round draws or of its other items: the caller asks "no item left", its
own entry and its draws.
If one of these first items is no answer, or the round holds fewer items, an answer lacks:
"K1: an answer lacks for a row".

It is written after the program's sending at the flag ownRound := false (OnBytes/Iop/Send.lean;
called at OnBytes/Iop/Cs.lean), of which Johnson/Desc/Sending/Send.lean's sendOpen is another form.
Like decideSend it calls none of the program's Send.cube, Send.pad, Send.front, Send.form and
Send.seedsOf.

decide stands behind Block.step, as in Johnson/Desc/K1/Own.lean: that round 1 shows no item and
draws seeds * (v + 1) elements, no position and no matrix entry is asked by roundsFit, out of
ROUNDS. So THE CALLER's BLOCK DECLARES seedEntry P AS THE ENTRY OF THE FIRST OF THE TWO ROUNDS
(openRound), and asks planOkOwn P in its test on the plan. Whoever calls decideOpen without these
has no such asker.

Main names: openRound; decideOpen; decideOpen_own (where the second round holds no more than the
answers, decideOpen is decideSend).

What is not claimed here. That a row made here is the program's, or that decideOpen's yes is
sendOpen's: no theorem of this file says so. No fold over blocks calls decideOpen yet. Nothing on
soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes Desc.Plain

/-- ROUNDS, the first of the two: the seeds' round, as the caller's block is to declare it. -/
def openRound (P : Par) : Fmt.DeclaredRound := { entry := seedEntry P }

/-- **The sending's decision where the caller goes on in the round of the answers.** Returns the new
messages' numbers, how many items of the second round were taken, and the state. -/
def decideOpen {L : Type} (P : Par) (owed : Option Nat) (d : DState L) :
    List Fmt.RoundView → Except String (Array Nat × Nat × DState L)
  | [r₁, r₂] =>
    (decideSend P owed d [r₁, { r₂ with vals := r₂.vals.take P.answers }]).map fun x =>
      (x.1, P.answers, x.2)
  | _ => .error "K1: not two rounds"

/-- Where the second round holds no more items than the answers, decideOpen is decideSend. -/
theorem decideOpen_own {L : Type} (P : Par) (owed : Option Nat) (d : DState L) (r₁ r₂ : Fmt.RoundView)
    (h : r₂.vals.length ≤ P.answers) :
    decideOpen P owed d [r₁, r₂] =
      (decideSend P owed d [r₁, r₂]).map fun x => (x.1, P.answers, x.2) := by
  simp only [decideOpen, List.take_of_length_le h]

end VerifiableInference.Desc.K1
