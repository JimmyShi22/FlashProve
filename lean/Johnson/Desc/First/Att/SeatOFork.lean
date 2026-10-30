-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/SeatOFork.lean: two seats read one field. The ledger that the hearing's seat
of the kind K5 reads (`seatSO`, Johnson/Desc/First/Att/SeatO.lean) is the ledger that the seat of
the lookup on a link's calls reads (`K3.seatCalls`, Johnson/Desc/First/Look/K3Seat.lean): the field
F of the open attention link.

Statements and proofs.
Main names:
  `ledgerO_att`: where seatSO.ledger s = some G, an attention link is open at s and G is its F.
  `ledgerO_fork`: where seatSO.ledger s = some G, (K3.seatCalls claim).fork s = some G. This is the
    first field of `K5Entry` (Johnson/Desc/First/Att/K05Entry.lean) at these two seats.
Limits: nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.First.Look.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model

/-- Where the hearing's seat reads a ledger an attention link is open, and the ledger is its own. -/
theorem ledgerO_att {s : First.S} {G : Fork} (h : seatSO.ledger s = some G) : ∃ a, s.here = .att a ∧ a.F = G := by
  unfold seatSO at h
  simp only at h
  split at h
  · rename_i a e
    exact ⟨a, e, Option.some.inj h⟩
  · cases h

/-- **The two seats read one field.** -/
theorem ledgerO_fork {Cl : Type} (claim : Aff → Cl) {s : First.S} {G : Fork} (h : seatSO.ledger s = some G) :
    (VerifiableInference.Desc.K3.seatCalls claim).fork s = some G := by
  obtain ⟨a, e, rfl⟩ := ledgerO_att h
  show s.fork? = some a.F
  unfold First.S.fork?
  rw [e]

end VerifiableInference.Desc.First.Att.P
