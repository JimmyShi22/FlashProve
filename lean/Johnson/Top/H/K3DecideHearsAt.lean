-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3DecideHearsAt.lean: the kind "lookup" (K3): the law `K3DecideHears`
(Johnson/Top/H/K3LawKind.lean), to the letter, of the field decide of `K3.block`
(Johnson/Desc/First/Look/K3Lookup.lean), with no premise left but the seat's two laws; and at the two
seats that run, with none. Theorems with their proofs.

In words: where the lookup's decide says yes on the rounds of a view, the record that it leaves
holds what was heard, the rounds have the sizes of the shape's own plan of rounds, and (where the
ledger in front has its sizes) the public tests have passed, the ledger behind is as the library's
dictionary says, and what was heard meets the library's record of end values AT THESE VERY ROUNDS,
under every reading of the field's words into a commutative ring. It is a TIE between the text
that runs and the flat function from which the proved block's out-statement is made: it has no
error term, and it says nothing on soundness by itself.

It joins four pieces, each proved in a file of its own:

  `k3DecideHears_of` (Johnson/Top/H/K3DecideHearsOf.lean): the wrapper: decide, hear, the tape of
    a view's rounds.
  `Fo.Tp.lkPad_law` (Johnson/Top/H/FlPort/LkPadLaw.lean): the law of the library's flat copy
    `lkPad` on a tape: the library's own proof of hcOut2, carried by a program from the routines
    in a context to the flat copies.
  `K3Cut.messages_lkPad` (Johnson/Top/H/Cut/CutPad.lean): where the kind's own `messages` returns,
    `lkPad` returns the same.
  `SeatReads` (Johnson/Desc/First/Look/K3SeatLaw.lean) and `SeatKeeps`
    (Johnson/Top/H/K3SeatFits.lean), of both seats.

THE MEMBER THAT SAYS YES TO ALL fails the law: `yesToAll_not`
(Johnson/Top/H/K3DecideHearsOf.lean). THE MEMBER THAT SAYS NO TO ALL meets it emptily, as it meets
every law of the form "decide's yes gives …"; that the kind's own decide is no such member is
shown by runs, not here.

Limits. Those of the four files. `Sized F` is a premise inside the law: whoever opens the link's
ledger pays it. lm is free. Whether a routine in a context is reached from these proofs is held by
a walk over constants in a file of its own (Johnson/Top/H/K3Walk.lean), not here.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3DecideHearsOf
import Johnson.Top.H.FlPort.LkPadLaw
import Johnson.Top.H.Cut.CutPad

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- The first premise of the wrapper: the carried law at a tape that is used up. -/
theorem lkPadHears : LkPadHears := by
  intro K _ ρ calls pub lid lm F F' t g h
  obtain ⟨taken, e, hs, hr⟩ := _root_.Fo.Tp.lkPad_law ρ calls pub lid lm F F' t [] g h
  have e' : taken = t := by rw [e, List.append_nil]
  subst e'
  exact ⟨hs, hr⟩

/-- The second: the bridge. -/
theorem messagesCut : MessagesCut := fun _ _ _ _ _ _ _ hS hN hm =>
  Desc.K3Cut.messages_lkPad hS hN hm

/-- **(L2a), of `K3.block`'s decide, at every seat that reads back what it lays.** -/
theorem k3DecideHears {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hfork : SeatKeeps seat) (hheard : Desc.K3.SeatReads seat) :
    K3DecideHears seat.fork seat.heard p.calls p.pub p.lid
      (Desc.K3.block seat piece laid before p guests).decide :=
  k3DecideHears_of seat piece laid before p guests hfork hheard lkPadHears messagesCut

/-- **(L2a) at the seat of the lookup on a link's calls.** -/
theorem k3DecideHears_calls {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) :
    K3DecideHears (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard p.calls p.pub p.lid
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before p guests).decide :=
  k3DecideHears _ piece laid before p guests (seatCalls_keeps claim) (Desc.K3.seatCalls_reads claim)

/-- **(L2a) at the seat of the lookup on the smallness test's digits.** -/
theorem k3DecideHears_digits {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl)) :
    K3DecideHears (Desc.K3.seatDigits claim).fork (Desc.K3.seatDigits claim).heard p.calls p.pub
      p.lid
      (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before p guests).decide :=
  k3DecideHears _ piece laid before p guests (seatDigits_keeps claim)
    (Desc.K3.seatDigits_reads claim)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3DecideHears
#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_calls
#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_digits
