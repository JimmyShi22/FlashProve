-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/ObjectsAtK3.lean: THE TWO PREMISES ON THE LOOKUP's RUNS OF
Johnson/Road/K4/Riders/Objects.lean (ObjRun, GuestRun, and that the runs are found under their
names) ARE MET BY THE KIND's OWN BLOCK AT THE SEAT ON A LINK's CALLS, with no guest handed in
(Law.blockVia (seatCalls …) … [], Johnson/Desc/First/Look/Via/Via.lean, K3Seat.lean), and by that
block with a block without runs laid behind it (Block.andThen, roundlessBlock, Johnson/Desc/Block.lean).
Statements and proofs.

  `via_runs`: the block's list of runs is "objects", "guests"; the first is an ObjRun, the second a
    GuestRun.
  `find_objects`, `find_guests`: of any list of runs of that form: each is found under its name.
  `via_quiet_runs`: the same list behind andThen with a quiet block.
No new argument: the texts unfolded.
**Limits.** claim is the literal "the form a as a claim, no run of entries, its own number's
weight". THE BLOCK AT A SEATED LINK IS NOT THIS TERM: the lot's make gives this term's runs
(Johnson/Road/K4/Riders/ObjectsAtLot.lean), and the driver lays its guard behind each run
(Johnson/Road/K4/Riders/ObjectsGuarded.lean). Nothing on soundness. K04_law, the law of K4's block
itself, IS NOT PROVED.


-/
import Johnson.Road.K4.Riders.Objects
import Johnson.Desc.First.Look.K3Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Riders

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block named roundlessBlock K3.seatCalls K3.Law.blockVia
  First.Look.P)
open VerifiableInference.Desc.First (S)

/-- The form a as a claim. -/
abbrev lit (a : Aff) : Claim := { form := a }

/-- **The kind's own block at the seat on the calls, no guest.** -/
theorem via_runs (piece : Nat) (laid : Array Nat) (sent : List (Nat × Nat)) (p : First.Look.P) :
    ∃ R1 R2, (K3.Law.blockVia (K3.seatCalls lit) piece laid sent p []).claims =
      [("objects", R1), ("guests", R2)] ∧ ObjRun R1 ∧ GuestRun R2 := by
  refine ⟨_, _, rfl, ?_, ?_⟩
  · intro s F g hF hg
    simp only [K3.seatCalls, hF, hg, named, bind, Except.bind, pure, Except.pure]
  · intro s
    rfl

theorem find_objects {β : Type} (R1 R2 : β) :
    ([("objects", R1), ("guests", R2)].find? fun r => r.1 == "objects") = some ("objects", R1) := by
  simp

theorem find_guests {β : Type} (R1 R2 : β) :
    ([("objects", R1), ("guests", R2)].find? fun r => r.1 == "guests") = some ("guests", R2) := by
  simp

/-- The same list behind a block without runs. -/
theorem via_quiet_runs (piece : Nat) (laid : Array Nat) (sent : List (Nat × Nat)) (p : First.Look.P)
    (nm nq : String) (chain : Nat) (link : Option Nat) (pc : Nat) (f : S → Except String S) :
    ∃ R1 R2, ((K3.Law.blockVia (K3.seatCalls lit) piece laid sent p []).andThen nm
        (roundlessBlock nq chain link pc f)).claims = [("objects", R1), ("guests", R2)] ∧
      ObjRun R1 ∧ GuestRun R2 := by
  obtain ⟨R1, R2, e, h1, h2⟩ := via_runs piece laid sent p
  refine ⟨R1, R2, ?_, h1, h2⟩
  show (K3.Law.blockVia (K3.seatCalls lit) piece laid sent p []).claims ++ [] = _
  rw [List.append_nil, e]

end OnBytes.Desc.First.K4.Riders

#print axioms OnBytes.Desc.First.K4.Riders.via_runs
#print axioms OnBytes.Desc.First.K4.Riders.find_objects
#print axioms OnBytes.Desc.First.K4.Riders.find_guests
#print axioms OnBytes.Desc.First.K4.Riders.via_quiet_runs
