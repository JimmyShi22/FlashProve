-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Caller/PlacesWritten.lean: AT THE WRITTEN VALUES OF THE FULL SIZE THE LIST OF
PLACES THAT THE FIRST PROOF CHAIN's SENDINGS LAY (K12.Door.laidAtCodes,
Johnson/Desc/K12/Door/LaidAt.lean) IS THE LIST OF THE PLAN's TENANTS (P5T.psFull,
Johnson/P5T/PlanSeatsFull.lean), MEMBER BY MEMBER: by Lean's kernel; and the same at a public part
whose codes, sendings and tenants are the written ones. NO SUB-PROTOCOL IMPORTS THIS FILE.
WHY. «The state's book follows the list» (placesAre, Johnson/Desc/Sound/SmpPlaces.lean) is had at
the laid list's places; the named reader of OOD samples finds a member by its tenant's place in the
plan's own list. Two makers walk the same sendings; that they give one list is said by no law.
  tenantsFull       the written tenants, as pairs (tree, tenant)
  laid_here         laidAtCodes returns the closed term LFull there: by laid_at
                    (Johnson/HB/LLHARD/LaidWritten.lean, which also has why the sorting in
                    laidAtCodes turns nothing) and codes_full2
                    (Johnson/Second/Seam/CodesOneInScope.lean)
  places_written    THE CLOSED EQUATION
  places_count      how many: so that the equation is not idle
  places_struck · places_raised   two negative tests: the last member struck; the first member's
                    tenant raised by one: the comparison rejects
  places_at         at a public part Z, under three equations
LIMITS. The full size alone. places_at's three equations are premises: other files have each from
a pinned test, in the goals' scope: not called here. No law general in Z. No soundness is claimed.

-/
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.K12.Door.LaidAt
import Johnson.G.SendsWritten
import Johnson.HB.LLHARD.LaidWritten
import Johnson.Second.Seam.CodesOneInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1Named
open Johnson.G (proofSends0)
open VerifiableInference.Desc.K12.Door (Laid laidAtCodes)
open VerifiableInference.Desc.K13.Law (LFull laid_at)

/-- The written tenants. -/
def tenantsFull : List (Nat × Nat) := P5T.psFull.map fun p => (p.j, p.t)

/-- The laid list is the written one. -/
theorem laid_here : laidAtCodes proofSends0.codes proofSends0 = some LFull :=
  laid_at Second.Seam.codes_full2 rfl

/-- **The closed equation.** -/
theorem places_written :
    (laidAtCodes proofSends0.codes proofSends0).map (·.places) = some tenantsFull := by
  rw [laid_here]
  decide +kernel

theorem places_count : tenantsFull.length = 199 := by decide +kernel

theorem places_struck :
    decide ((laidAtCodes proofSends0.codes proofSends0).map (·.places) =
      some tenantsFull.dropLast) = false := by
  rw [laid_here]
  decide +kernel

theorem places_raised :
    decide ((laidAtCodes proofSends0.codes proofSends0).map (·.places) =
      some (tenantsFull.zipIdx.map fun x => if x.2 = 0 then (x.1.1, x.1.2 + 1) else x.1)) =
      false := by
  rw [laid_here]
  decide +kernel

/-- **At a public part whose codes, sendings and tenants are the written ones.** -/
theorem places_at {Z : ProofFile.Pub} {Ld : Laid} (hc : Z.first.codes = proofSends0.codes)
    (hs : Z.made.proof.1 = proofSends0) (hp : P5T.planSeats Z Z.D.1 = P5T.psFull)
    (hLd : laidAtCodes Z.first.codes Z.made.proof.1 = some Ld) :
    Ld.places = (P5T.planSeats Z Z.D.1).map fun p => (p.j, p.t) := by
  rw [hc, hs] at hLd
  have h := places_written
  rw [hLd] at h
  rw [hp]
  exact Option.some.inj h

end P1Named

#print axioms P1Named.laid_here
#print axioms P1Named.places_written
#print axioms P1Named.places_count
#print axioms P1Named.places_struck
#print axioms P1Named.places_raised
#print axioms P1Named.places_at
