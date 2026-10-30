--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/K4LotRest.lean: WHAT EVERY SUB-PROTOCOL OF THE KIND K4 IN THE LOTS OF THE IOP AS
WRITTEN IN LEAN LEAVES OF THE VERIFIER's STATE: ITS DECISION, EACH OF ITS RUNS OF CLAIMS AND EACH OF
ITS RUNS BEHIND THE BATCHING KEEP `Rest` (Johnson/Desc/First/K4/ReadsAtS.lean). Two statements with
their proofs: calls.

  `Rest s s'` (landed) says: st · book · roots · failed · check · out · req ARE AS THEY WERE; so are
    the readers link? · tl? · look? · lookHeard?; and where s stands in a feed-forward segment, s'
    does, with the same link context, what the lookup heard, the approximate range proof's
    parameters and the lookup's heard mark. What may turn: the open segment's ledger, K4's own part
    of the state (the field own) and the pending row.
  `k4Block_whole`: the lot's sub-protocol is K4's own term with another test on the plan: `Whole
  Rest` (`k4C_whole_rest`, K4WholeSt.lean).
  **`k4_lot_whole`**: b' of a lot of the seat, of the kind K4 ⟹ `Whole Rest b'`. NO OTHER PREMISE.

HOW IT IS SPENT. For a fact of the sort "left by every sub-protocol, laid by the start" that reads
fields of the list above alone, K4's twelve places are `whole_mono (fun _ _ h => …) (k4_lot_whole
lot hk)` (K4WholeSt.lean).

Limits. It says what K4's sub-protocols LEAVE: nothing of what they make. K04_law, the law of K4's
sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.K4WholeSt
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.IMR.LotKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Desc.First.K4 (Rest)
open VerifiableInference.Desc (Block KindName)
open VerifiableInference.Desc.Keeps (Whole)
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

/-- The lot's sub-protocol keeps Rest: its decision and runs are K4's own term's. -/
theorem k4Block_whole (x : Bool × OnBytes.Desc.First.K4.Par) : Whole Rest (ProofFile.k4Block x) :=
  k4C_whole_rest { x.2 with k3Runs := true }

/-- **Every sub-protocol of the kind K4 in the seat's lots keeps Rest.** -/
theorem k4_lot_whole {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {b' : Block S Cl}
    (lot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀) (hk : b'.place.kind = KindName.K4) :
    Whole Rest b' := by
  obtain ⟨L, hL, hb⟩ := lot
  obtain rfl : L = ProofFile.k4Lot Z := IM.lot_of_kind hL hb (by rw [hk]; rfl)
  have hm : b' ∈ (ProofFile.k4Lot Z).hearC G₀ := by
    rcases IM.blocks_mem hb with ⟨x, hx, -⟩ | h
    · cases hx
    · exact h
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
  exact k4Block_whole x

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4Block_whole
#print axioms OnBytes.Road.K4.k4_lot_whole
