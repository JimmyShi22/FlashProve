--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeyFacesFull.lean: THE KEY FILE'S LOOKUPS: FROM THE SUB-PROTOCOL'S OWN TEST ON THE PLAN TO WHAT
THE HONEST SIDE OF A LOOKUP ASKS OF THE FACE AND THE ENTRIES; and two closed facts on the two faces
at the library's written sizes of a key of the full size (`Lk6.AtPlan.keyFull`). Statements and
proofs.

What is shown.
  **`fit_of_planOk`**: where a place's tests on the plan pass (`PG.planOk`,
    Johnson/Desc/First/Look/K3LookupGeneral.lean: it is `K3.lookupKind`'s field planOk): the face passes its
    own test; the planner makes the place's entries; these pass `entriesFit`
    (Johnson/Desc/First/Look/Via/Rounds.lean: round for round, but for the work bits, those that the
    hearing goes by): E2E/PlannerLookup.lean's `fit_of_planner`. General: any place.
  `rounds_of_planOk`: there the sub-protocol's declared rounds and oracle messages are the entries',
    bare.
  **`parts_full`**: two lookups; EACH HAS TWELVE PARTS OF KEYS (the numbers in the lookup's public
    data: twelve times 36; twelve times 35: part i has 2 ^ parts[i] keys, OnBytes/Iop/Lkp.lean). By
    Lean's kernel.
  **`ok_full`**: both faces pass the face's own test. By Lean's kernel.

Limits.
- THAT THE PLANNER MAKES THE TWO PLACES' ENTRIES AT THE WRITTEN SIZES IS NOT SHOWN HERE. Lean's
  evaluator says so (9,581 and 9,220 entries): an evaluation is no proof. It is a clause of the
  sub-protocol's own test on the plan: so it is had wherever that test is known to pass.
- That any sub-protocol's test on the plan passes at any public files is shown nowhere here.
- Nothing on completeness, on soundness or on what is hidden.


-/
import E2E.KeyNumbers
import E2E.PlannerLookup
import Johnson.Desc.Key.Link

set_option autoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyFaces
open OnBytes
open Lk6.AtPlan (keyFull)
open VerifiableInference.Desc.K3 (faceOfLkp entriesG entriesFit PG SeatG lookupKind)

/-! ## 1. From the test on the plan -/

theorem fit_of_planOk {S Cl : Type} {p : PG} {before : List (ℕ × ℕ)} {bits : ℕ}
    {guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)}
    (h : p.planOk before bits guests = true) :
    p.face.ok = true ∧ ∃ es, p.entries = some es ∧ entriesFit p.face es = true := by
  unfold VerifiableInference.Desc.K3.PG.planOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hok, hes⟩, -⟩, -⟩, -⟩ := h
  obtain ⟨es, e⟩ := Option.isSome_iff_exists.1 hes
  exact ⟨hok, es, e, AtPublicFiles.PlanLookup.fit_of_planner hok e⟩

theorem rounds_of_planOk {S Cl : Type} (seat : SeatG S Cl) {p : PG} {before : List (ℕ × ℕ)}
    {bits : ℕ} {guests : List (VerifiableInference.Desc.First.Look.Guest S Cl)}
    {es : List Fmt.Entry} (e : p.entries = some es) :
    (lookupKind seat before bits guests p).rounds = es.map (fun y => { entry := y }) ∧
      (lookupKind seat before bits guests p).oracles = es.map fun _ => [] := by
  constructor
  · show (p.entries.getD []).map _ = _
    rw [e]
    rfl
  · show (p.entries.getD []).map _ = _
    rw [e]
    rfl

/-! ## 2. At the written sizes of a key of the full size -/

/-- The key file's lookups at these sizes. -/
abbrev looksFull := Wf.lookupsOf keyFull.ranges.x (Wf.matrixOf keyFull.once.shape)

/-- Two lookups; each has TWELVE parts of keys. -/
theorem parts_full : looksFull.map (fun y => y.parts) =
    [List.replicate 12 36, List.replicate 12 35] := by decide +kernel

/-- Both faces pass the face's own test. -/
theorem ok_full : looksFull.all (fun y => (faceOfLkp y).ok) = true := by decide +kernel

end AtPublicFiles.KeyFaces

#print axioms AtPublicFiles.KeyFaces.fit_of_planOk
#print axioms AtPublicFiles.KeyFaces.rounds_of_planOk
#print axioms AtPublicFiles.KeyFaces.parts_full
#print axioms AtPublicFiles.KeyFaces.ok_full
