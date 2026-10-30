-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/Desc/First/Att/Door/Law/RoundsWritten.lean: **IN SCOPE, WHERE THE VALUE IS LAID, THE ENTRIES OF THE PLAN's DECLARED ROUNDS ARE THE WRITTEN LISTS'**: a closed list. Kind-free. A join of four lemmas that lie:
the description's own test on the plan says that its sub-protocols' declared rounds in a row are the plan's (decl_of_planOk, Johnson/Desc/Sound/ReadsOkProofs.lean) · in scope the written plan's test says that these, written out, are
the written lists (seat_in_scope, Johnson/Goal/Numbers/PlanWrittenDescScope.lean; asks_written, Johnson/Desc/Laid/ProofAsksLaw.lean) · writing out keeps each round's entry (writtenOf_entries, Johnson/G/DataEntries.lean) · the seated
description's plan is the public part's own field D (by unfolding).
Why. The table's seats (P5T.planSeats | planSeatsAll, Johnson/P5T/PlanSeats.lean) read of the public part's declared rounds one thing: how many roots the rounds in front send. With this file that is a number off written data: a test on
the seats need not be run anew at each head.

Main names:
  plans_entries_written: at any description F: in scope, F.planOk, the written plan's test → the three equations on F.plans.
  entries_written: under the one head AtMg (at any SecondHashFunctionArgument o): the three equations at Zp.D. roots_written: the first chain's numbers of roots.
  rootsBefore_written | …₂ | …₃: P5T.rootsBefore at each of the three lists is a sum over a prefix of a closed list.
IS IT EMPTY HERE? Equations under the head. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE
(AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.P5J.AtMg
import Johnson.Desc.Laid.ProofFullScope
import Johnson.G.DataEntries
import Johnson.Desc.Sound.ReadsOkProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc (FileDescription Chain)
open OnBytes.Maker (WholeD)
open Johnson.G (dryProofFull)
open P5J (AtMg F0T TS)

/-- **At any description.** -/
theorem plans_entries_written {Xi : Type} (F : FileDescription Xi) {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) (hp : F.planOk = true)
    (hs : VerifiableInference.PlanWritten.seatPinnedProof Z.pol F = true) :
    F.plans.1.map (·.entry) = dryProofFull.1.map (·.1.entry) ∧ F.plans.2.1.map (·.entry) = dryProofFull.2.1.map (·.1.entry) ∧
      F.plans.2.2.map (·.entry) = dryProofFull.2.2.map (·.1.entry) := by
  have hw := (VerifiableInference.PlanWritten.seat_in_scope Xi F Z hZ hs).1
  rw [VerifiableInference.Desc.Sound.decl_of_planOk F hp] at hw
  obtain ⟨e1, e2, e3⟩ := Johnson.G.OfPlan.writtenOf_entries hw
  exact ⟨e1.symm, e2.symm, e3.symm⟩

section
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  (h : AtMg o Z D r Zp Np cF)
include h

/-- **Under the one head: the public part's declared rounds have the written lists' entries.** -/
theorem entries_written :
    Zp.D.1.map (·.entry) = dryProofFull.1.map (·.1.entry) ∧ Zp.D.2.1.map (·.entry) = dryProofFull.2.1.map (·.1.entry) ∧
      Zp.D.2.2.map (·.entry) = dryProofFull.2.2.map (·.1.entry) :=
  plans_entries_written (F0T o Zp Np cF) h.scope h.laid.planOk (LPFD.asks_written h.laid.asks)

/-- The first chain's numbers of roots, round by round: a closed list. -/
theorem roots_written : (Zp.D.1.map fun r => r.entry.roots) = dryProofFull.1.map fun x => x.1.entry.roots := by
  have e := congrArg (List.map (·.roots)) (entries_written h).1
  rw [List.map_map, List.map_map] at e
  exact e

/-- How many roots the first chain's rounds in front of the k-th send. -/
theorem rootsBefore_written (k : ℕ) : P5T.rootsBefore Zp.D.1 k = ((dryProofFull.1.map fun x => x.1.entry.roots).take k).sum := by
  unfold P5T.rootsBefore
  rw [← roots_written h, List.map_take]

/-- The like at the shared chain. -/
theorem rootsBefore_written₂ (k : ℕ) : P5T.rootsBefore Zp.D.2.1 k = ((dryProofFull.2.1.map fun x => x.1.entry.roots).take k).sum := by
  have e := congrArg (List.map (·.roots)) (entries_written h).2.1
  rw [List.map_map, List.map_map] at e
  have e' : (Zp.D.2.1.map fun r => r.entry.roots) = dryProofFull.2.1.map fun x => x.1.entry.roots := e
  unfold P5T.rootsBefore
  rw [← e', List.map_take]

/-- The like at the last chain. -/
theorem rootsBefore_written₃ (k : ℕ) : P5T.rootsBefore Zp.D.2.2 k = ((dryProofFull.2.2.map fun x => x.1.entry.roots).take k).sum := by
  have e := congrArg (List.map (·.roots)) (entries_written h).2.2
  rw [List.map_map, List.map_map] at e
  have e' : (Zp.D.2.2.map fun r => r.entry.roots) = dryProofFull.2.2.map fun x => x.1.entry.roots := e
  unfold P5T.rootsBefore
  rw [← e', List.map_take]

end

end H2K5.Door

#print axioms H2K5.Door.plans_entries_written
#print axioms H2K5.Door.entries_written
#print axioms H2K5.Door.roots_written
#print axioms H2K5.Door.rootsBefore_written
#print axioms H2K5.Door.rootsBefore_written₂
#print axioms H2K5.Door.rootsBefore_written₃
