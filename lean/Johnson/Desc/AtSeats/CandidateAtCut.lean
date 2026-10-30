-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/CandidateAtCut.lean: DEFINITIONS ALONE: one closed candidate for the
letters that the tests of the kind K1's law's top read of the table's numbers and of the list of
seats: so that the closed facts of several files meet at one term. No statement, no proof.
  toldC: what each of the first chain's 358 sub-protocols declares, off the written cut
      (cutFirstFull, Johnson/Desc/Ok/PlanWritten/CutLit.lean)
  psF: the written list of the 358 places
  NC: the table's numbers: the core off the written seats (P5T.N0Full), its counts
      filled off toldC (Numbers.withTold)
  seatsC: the written seats' (tree, tenant), in order
What is not claimed. That toldC is what the IOP as written in Lean declares: no theorem says that
the written cut is the cut of that IOP. That the composed meaning's numbers (P5J.At.N,
Johnson/P5J/LettersAt.lean) are NC. Nothing on soundness.

-/
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.First.BookNumbers
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HashBuild
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (Numbers flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.PlanWritten (cutFirstFull)

/-- What each sub-protocol of the first chain declares, off the written cut. -/
def toldC : List (List VerifiableInference.Desc.Oracle) :=
  cutFirstFull.map fun r => r.2.2.2.2.1.flatMap (·.2)

/-- The written list of places. -/
def psF : List Place := flatPlacesOf linksFull true

/-- The candidate numbers. -/
def NC : Numbers := P5T.N0Full.withTold psF toldC

/-- The candidate list of seats. -/
def seatsC : List (Nat × Nat) := P5T.psFull.map fun p => (p.j, p.t)

end HashBuild
