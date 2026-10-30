--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/K3Via/DecideHearsVia.lean: the kind "lookup" (K3): the law on what decide hears
(Johnson/Top/H/K3DecideHearsAt.lean) carried to the block with the hearing exchanged. Theorems; each
is one line over blockVia_decide (Johnson/Top/H/K3Via/Blocks.lean).

Main theorems:
  `k3DecideHears_via`: K3DecideHears (Johnson/Top/H/K3LawKind.lean), to the letter, of
    Law.blockVia's decide, at every seat that reads back what it lays, where the new block's planOk
    says yes: a public test, which the fold itself asks.
  `k3DecideHears_via_calls`, `k3DecideHears_via_digits`: at the two seats that run, with no premise
    but that.

How. Where blockVia's decide says .ok s', K3.block's decide says .ok s' (the same s'); of that the
older law speaks. So beneath this law lie four texts of the hearing: messagesV, messagesG, messages,
lkPad; the last three do not run in blockVia: they are middle terms of the proof.

Limits. One way. A tie: it has no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3Via.Blocks
import Johnson.Top.H.K3DecideHearsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model

/-- **(L2a), of the new block's decide, at every seat that reads back what it lays.** -/
theorem k3DecideHears_via {S Cl : Type} (seat : Desc.K3.Seat S Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hplan : (Desc.K3.Law.blockVia seat piece laid before p guests).planOk = true)
    (hfork : SeatKeeps seat) (hheard : Desc.K3.SeatReads seat) :
    K3DecideHears seat.fork seat.heard p.calls p.pub p.lid
      (Desc.K3.Law.blockVia seat piece laid before p guests).decide :=
  fun K _ ρ lm s s' rs cols ho h =>
    k3DecideHears seat piece laid before p guests hfork hheard K ρ lm s s' rs cols ho
      (Desc.K3.Law.blockVia_decide hplan h)

/-- **(L2a) of the new block at the seat of the lookup on a link's calls.** -/
theorem k3DecideHears_via_calls {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : Desc.First.Look.P)
      (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before p guests).planOk =
      true) :
    K3DecideHears (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard p.calls p.pub p.lid
      (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before p guests).decide :=
  k3DecideHears_via _ piece laid before p guests hplan (seatCalls_keeps claim)
    (Desc.K3.seatCalls_reads claim)

/-- **(L2a) of the new block at the seat of the lookup on the smallness test's digits.** -/
theorem k3DecideHears_via_digits {Cl : Type} (claim : Aff → Cl) (piece : Nat) (laid : Array Nat)
    (before : List (Nat × Nat)) (p : Desc.First.Look.P)
      (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) piece laid before p guests).planOk =
      true) :
    K3DecideHears (Desc.K3.seatDigits claim).fork (Desc.K3.seatDigits claim).heard p.calls p.pub
      p.lid
      (Desc.K3.Law.blockVia (Desc.K3.seatDigits claim) piece laid before p guests).decide :=
  k3DecideHears_via _ piece laid before p guests hplan (seatDigits_keeps claim)
    (Desc.K3.seatDigits_reads claim)

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_via
#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_via_calls
#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_via_digits
