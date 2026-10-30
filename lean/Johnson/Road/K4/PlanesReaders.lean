-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/PlanesReaders.lean: WHERE K4's `planesParts` RETURNS, EVERY READER OF THE PLANES'
THREE TABLES THAT IT CALLS HAS RETURNED: a refusing reader makes `planesParts` refuse. One statement
with its proof: read off `planesParts_some` (PlanesMembers.lean) and `foldlM_some_all`
(OnBytes/Desc/First/P1/LevelKit.lean: where a fold over `Option` returns, every step has returned).

  `planesParts_readers`: where `planesParts v fo` returns: the three tables have their numbers tB0,
    tB1, tP, and at every column col below NC * 2 ^ (kT + 5 - lmb): `k4Bit v tB0 tB1 0 col`,
    `k4Bit v tB0 tB1 1 col` and `k4Pin v tP col` are there (the lookup's files' names for
    `planesParts`' own readers, Johnson/Top/H/K4PlanesWorth.lean).
So the default in `K4ReadsTrue` ("(k4Bit …).getD {}") is never taken where
`planesParts` has returned, at the columns of which `K4ReadsTrue` speaks.

Limits. On the READERS alone. The weights inside `planesAt` are read by `getD … zeroE` off two
equality tables: nothing on these here. Which wrong indices `U3at` does not refuse: its own
docstring. Nothing on soundness.
-/
import Johnson.Road.K4.PlanesMembers
import Johnson.Top.H.K4PlanesWorth
import OnBytes.Desc.First.P1.LevelKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env)
open OnBytes.Desc.First.K4 (planesParts planesAt)
open OnBytes.Desc.First.P1 (foldlM_some_all)
open VerifiableInference.OnPublicFiles (k4Bit k4Pin k4Col)

/-- Where a mapped optional value is there, the value is. -/
theorem isSome_of_map {α β : Type} {x : Option α} {f : α → β} {b : β} (h : x.map f = some b) :
    x.isSome = true := by
  cases x with
  | none => cases h
  | some a => rfl

/-- **Where `planesParts` returns, each of its readers has returned.** -/
theorem planesParts_readers {v : Env} {fo : Forest.Heard} {pp : Aff × List Aff}
    (h : planesParts v fo = some pp) :
    ∃ tB0 tB1 tP, v.tabAt "b-bits-0" = some tB0 ∧ v.tabAt "b-bits-1" = some tB1 ∧
      v.tabAt "b-pin" = some tP ∧
      ∀ col, col < fo.shape.NC * 2 ^ (fo.shape.kT + 5 - v.y.h.lmb) →
        (k4Bit v tB0 tB1 0 col).isSome = true ∧ (k4Bit v tB0 tB1 1 col).isSome = true ∧
          (k4Pin v tP col).isSome = true := by
  obtain ⟨tB0, tB1, tP, at0, at1, count, e0, e1, eP, _, h0, h1, hc, _⟩ := planesParts_some h
  refine ⟨tB0, tB1, tP, e0, e1, eP, fun col hcol => ⟨?_, ?_, ?_⟩⟩
  · unfold planesAt at h0
    exact foldlM_some_all (P := fun c => (k4Bit v tB0 tB1 0 c).isSome = true)
      (fun _ _ _ e => isSome_of_map e) _ _ _ h0 col (List.mem_range.mpr hcol)
  · unfold planesAt at h1
    exact foldlM_some_all (P := fun c => (k4Bit v tB0 tB1 1 c).isSome = true)
      (fun _ _ _ e => isSome_of_map e) _ _ _ h1 col (List.mem_range.mpr hcol)
  · exact foldlM_some_all (P := fun c => (k4Pin v tP c).isSome = true)
      (fun _ _ _ e => isSome_of_map e) _ _ _ hc col (List.mem_range.mpr hcol)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.planesParts_readers
