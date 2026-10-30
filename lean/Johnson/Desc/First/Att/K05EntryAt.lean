-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05EntryAt.lean: the record at the entry of the kind K5 (`K5Entry`,
Johnson/Desc/First/Att/K05Entry.lean) from a promise on the carried record behind the lookup, and at
the two seats `seatSO` (Johnson/Desc/First/Att/SeatO.lean) and `K3.seatCalls`
(Johnson/Desc/First/Look/K3Seat.lean).

Definitions, statements and proofs.
Main names:
  `K3LeftAtIs fork heard h lm first Q s`: there are F, F', g and rs with Q F, F.next = first,
    `K3LeftIs` h lm F F' g rs, heard s = some g and fork s = some F'. The ledger in hand is F'
    itself.
  `entry_of_leftAtIs`: `K3LeftAtIs` at Q := `Room` · ns nx (Forest.elems x.fs + (slotsOf (script
    own) + k)), with the tie of the two seats' readers, gives `K5Entry` for some F, F', g and rs.
  `entry_at_seats`: the same at `seatSO` and `K3.seatCalls` claim. The tie of the readers is
    `ledgerO_fork` (Johnson/Desc/First/Att/SeatOFork.lean), so the promise is the only premise.
Limits: `K3LeftAtIs` is a record of this file's own, until the lookup's kind has one; it is shown
for no run in this file or in what it imports. No soundness of the protocol is claimed. Nothing on
completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Entry
import Johnson.Desc.First.Att.SeatOFork

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model OnBytes.Model.Road

/-- **The lookup's sharp promise, as far as the kind K5 spends it**: the ledger in hand is F'. -/
def K3LeftAtIs {S : Type} (fork : S → Option Fork) (heard : S → Option Forest.Heard)
    (h : Forest.Shape) (lm first : ℕ) (Q : Fork → Prop) (s : S) : Prop :=
  ∃ (F F' : Fork) (g : Forest.Heard) (rs : TwV.Rounds Cb.Gl.E), Q F ∧ F.next = first ∧
    K3LeftIs h lm F F' g rs ∧ heard s = some g ∧ fork s = some F'

/-- **The promise, with the tie of the two readers, is the record at the kind's entry.** -/
theorem entry_of_leftAtIs {St : Type} (seat : Seat St) (fork : St → Option Fork) (heard : St → Option Forest.Heard)
    (x : VerifiableInference.Desc.First.Look.Place) (own : Params.AttentionRounds) (s : St) (ns nx k : ℕ)
    (same : ∀ G, seat.ledger s = some G → fork s = some G)
    (A : K3LeftAtIs fork heard x.fs x.lm x.F.next
      (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script own) + k))) s) :
    ∃ F F' g rs, K5Entry seat fork heard x own s ns nx k F F' g rs := by
  obtain ⟨F, F', g, rs, q, hn, L, hh, hf⟩ := A
  exact ⟨F, F', g, rs, same, hf, hh, hn, L, q⟩

/-- **At the two seats that sit**: the promise alone. -/
theorem entry_at_seats {Cl : Type} (claim : Aff → Cl) (x : VerifiableInference.Desc.First.Look.Place)
    (own : Params.AttentionRounds) (s : First.S) (ns nx k : ℕ)
    (A : K3LeftAtIs (VerifiableInference.Desc.K3.seatCalls claim).fork (VerifiableInference.Desc.K3.seatCalls claim).heard
      x.fs x.lm x.F.next (fun F => Room F ns nx (Forest.elems x.fs + (slotsOf (script own) + k))) s) :
    ∃ F F' g rs, K5Entry seatSO (VerifiableInference.Desc.K3.seatCalls claim).fork
      (VerifiableInference.Desc.K3.seatCalls claim).heard x own s ns nx k F F' g rs :=
  entry_of_leftAtIs seatSO _ _ x own s ns nx k (fun _ h => ledgerO_fork claim h) A

end VerifiableInference.Desc.First.Att.P
