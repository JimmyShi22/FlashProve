-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ObjectsStates.lean: A NAMED PREMISE ON THE IOP AS WRITTEN IN LEAN: which runs
of claims sub-protocol number b of a segment states under the names "objects" and "guests". A
definition and two small theorems. Light imports, no Mathlib: so that a file over the IOP's own
value can import it.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  ObjectsStates states b: sub-protocol number b states a run "objects" and a run "guests"; an accept
      of the first is an accept of K9.objectsCalls
      (Johnson/Desc/First/Batch/BlindK3.lean: the rows that the lookup on the calls keeps, as
      claims; one owed claim is marked as added), an accept of the second of K9.guestsNone
      (Johnson/Desc/First/Batch/BlindAtt.lean: no claim; the state is left).
  objectsStates_block: it holds where that sub-protocol's runs are those of the lookup's own
      K3.block at the calls, with no guest.
  objectsStates_of_guarded: it holds where the two runs stand behind a guard that only adds rejects.

Who spends it: Johnson/Desc/Kinds/Law/K6RidersAtMgAll.lean.
Every letter under "there is": run, twice: each pinned by its equation on states b.
What it does not say. One direction alone: that those two runs' accepts are accepts of the stated
runs is not asked. That the IOP's own segment meets it is not said here. Nothing on soundness.

-/
import Johnson.Desc.First.Batch.BlindK3
import Johnson.Desc.First.Batch.BlindAtt
import Johnson.Desc.First.Batch.ReadersOfLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K9 (RunOf)

/-- **A NAMED PREMISE**: what sub-protocol number b of the segment states under "objects" and under
"guests". -/
def ObjectsStates (states : Nat → List (RunOf S)) (b : Nat) : Prop :=
  (∃ run, (states b).find? (fun r => r.1 == "objects") = some ("objects", run) ∧
    ∀ k t y, run k t = .ok y → K9.objectsCalls k t = .ok y) ∧
  ∃ run, (states b).find? (fun r => r.1 == "guests") = some ("guests", run) ∧
    ∀ k t y, run k t = .ok y → K9.guestsNone k t = .ok y

/-- The premise holds where the runs are those of the lookup's own sub-protocol at the calls, with
no guest. -/
theorem objectsStates_block (piece : Nat) (laid : Array Nat) (before : List (Nat × Nat))
    (p : First.Look.P) (states : Nat → List (RunOf S)) (b : Nat)
    (h : states b = (K3.block (K3.seatCalls fun a => ({ form := a } : Claim)) piece laid before p
      []).claims) : ObjectsStates states b :=
  ⟨⟨K9.objectsCalls, by rw [h]; rfl, fun _ _ _ e => e⟩,
    K9.guestsNone, by rw [h]; rfl, fun _ _ _ e => e⟩

/-- The premise holds where the two runs stand behind a guard that only adds rejects. -/
theorem objectsStates_of_guarded
    (guard : (Nat → S → Except String (List Claim × S)) → Nat → S →
      Except String (List Claim × S))
    (hg : ∀ r k t y, guard r k t = .ok y → r k t = .ok y) {states : Nat → List (RunOf S)} {b : Nat}
    (ho : (states b).find? (fun r => r.1 == "objects") = some ("objects", guard K9.objectsCalls))
    (hs : (states b).find? (fun r => r.1 == "guests") = some ("guests", guard K9.guestsNone)) :
    ObjectsStates states b :=
  ⟨⟨_, ho, hg _⟩, _, hs, hg _⟩

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.objectsStates_block
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.objectsStates_of_guarded
