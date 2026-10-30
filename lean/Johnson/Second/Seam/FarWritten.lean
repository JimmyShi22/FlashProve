-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/FarWritten.lean: THE SHARED TABLE's CONSTANT's FIVE «testsFar» (Johnson/Desc/K14/Law/SharedConstFar.lean) AT THE WRITTEN VALUES, DECIDED BY LEAN's KERNEL, WITH THE LAW THAT CARRIES THEM TO ANY PUBLIC VALUE WHOSE FIVE READ PARTS ARE THE WRITTEN ONES. They buy the fold fact FarFrom. Nothing that lies is typed here: the tests foundFirstB | foundLaterB are those of Johnson/P5T/FoundInList.lean; the written seats psFull, the ties planSeats_at | chainSeats_at | psFull_is, the written list LFull with laid_written | laid_sizes are other files' (Johnson/P5T/PlanSeatsFull.lean · PlanSeatsAt.lean · PlanSeatsAllAt.lean · Johnson/HB/LLHARD/LaidWritten.lean).
  sharedFull          the shared chain's seats at the written values: the middle piece of seatsAllFull (PlanSeatsFull.lean).
  firstAt q · laterAt q   the two tests' texts at psFull | sharedFull.
  THE CLOSED FACTS, each by «decide +kernel»:
  hpl_written         every place of LFull is found among the first chain's seats. A List.all IS TRUE OF AN EMPTY LIST: BESIDE IT: LFull.places.length = 199, and laidAtCodes … = some LFull: laid_sizes | laid_written (LaidWritten.lean): called in far_written.
  seats_are_places    MORE THAN hpl: psFull's seats ARE LFull.places, entry for entry: planSeats' and K12.Door.laidOf's ways of counting trees agree at the written values.
  hwi_written         foundFirstB's text at W's and the index masks' seats (N0Full.w | N0Full.index: (82, 0) | (1, 0) by N0Full_seats, PlanSeatsFull.lean).
  hten_written        o_u's, o_omega's and o_sp's tenants (tenantSh 83 at the two typed layouts of ToldFitWritten.lean) are found among the shared chain's seats and not among the first chain's; under realSized.any: false at none. Which three seats they are: tenants_are.
  (hlen: 82 ≤ 1000: laid_sizes' first clause.)
  far_not             NEGATIVE TWINS, each = false: W's seat (82, 0) is NOT «later» · o_u's seat (83, 0) is NOT «first» · the written places with (83, 0) in front fail hpl · the three tenants at 82 in the place of 83 fail hten.
  THE LAW:
  seats_first | seats_shared   at Z, D whose first and shared lists of sendings, shape of the request's own rounds, and first and shared chains' declared entries are the written ones: planSeats Z D.1 = psFull · chainSeats 1 (rootsBefore D.1 D.1.length) Z.made.proof.2.1 D.2.1 = sharedFull.
  far_written       so at such Z, D and every x that realSized returns: the five tests accept: foundLaterB Z D at the three tenants · LFull.places.all (foundFirstB Z D) · Z.made.proof.1.sends.length ≤ 1000; with LFull.places.length = 199 and laidAtCodes codesFull2 Z.made.proof.1 = some LFull beside; and foundFirstB Z D at N0Full.w | N0Full.index.
Limits. That a seat's Z, D have the five written parts is other files' to show (seats_in_scope, Johnson/P5T/PlanSeatsTie.lean | laid_in_scope, Johnson/HB/LLHARD/PlanInScope.lean). That K14's files' t₁ | layU | layO (planAt …, Johnson/Desc/K14/Law/SharedConstAt.lean) are 83 and the two typed layouts is K14's files' to show. The full size; the proof file. No soundness is claimed.

-/
import Johnson.Second.Seam.ToldFitWritten
import Johnson.P5T.FoundInList
import Johnson.P5T.PlanSeatsFull
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open OnBytes OnBytes.Params Johnson.G P5T
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K13.Law (LFull laid_sizes laid_written)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Desc.K14.Law.Fence (tenantSh)

/-- The shared chain's seats at the written values. -/
def sharedFull : List PSeat :=
  chainSeatsBy (rootsRuns dryProofRecsFull dryProofRunsFull1) 1 83 proofSends1

def firstAt (q : Nat × Nat) : Bool := (psFull.find? (atSeat q)).isSome
def laterAt (q : Nat × Nat) : Bool :=
  (psFull.find? (atSeat q)).isNone && (sharedFull.find? (atSeat q)).isSome

/-- The three tenants at a base and the typed layouts. -/
def tenantsAt (lo : Nat) (x : LinSized) : List (Nat × Nat) :=
  [tenantSh lo (layUAt x) (layOAt x) .oU, tenantSh lo (layUAt x) (layOAt x) .oOmega,
    tenantSh lo (layUAt x) (layOAt x) .oSp]

theorem hpl_written : LFull.places.all firstAt = true := by decide +kernel

/-- **The first chain's seats ARE the written places, entry for entry**: the two ways of counting
trees (planSeats' · K12.Door.laidOf's) agree at the written values. -/
theorem seats_are_places : psFull.map (fun p => (p.j, p.t)) = LFull.places := by decide +kernel

/-- W's and the index masks' seats (N0Full_seats, PlanSeatsFull.lean: (82, 0) · (1, 0)) are found
among the first chain's. -/
theorem hwi_written : firstAt N0Full.w = true ∧ firstAt N0Full.index = true := by decide +kernel

theorem hten_written : (realSized.any fun p => (tenantsAt 83 p.1).all laterAt) = true := by
  decide +kernel

theorem tenants_are : (realSized.any fun p =>
    decide (tenantsAt 83 p.1 = [(83, 0), (84, 0), (85, 0)])) = true := by decide +kernel

theorem far_not : laterAt (82, 0) = false ∧ firstAt (83, 0) = false ∧
    ((83, 0) :: LFull.places).all firstAt = false ∧
    (realSized.any fun p => (tenantsAt 82 p.1).all laterAt) = false := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

section
variable (Z : ProofFile.Pub) (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)

theorem seats_first (h1 : Z.made.proof.1 = proofSendsFull.1) (hS : Z.first.shape = shapeFull)
    (hD1 : D.1.map (·.entry) = esFull.1) : planSeats Z D.1 = psFull := by
  rw [planSeats_at, h1, hS, hD1, psFull_is]

theorem roots_first : rootsIn esFull.1 esFull.1.length = 83 := by
  have e1 : esFull.1 = (unrunR dryProofRecsFull dryProofRunsFull0).map (·.1.entry) := rfl
  have l1 : esFull.1.length = 48293 := by
    rw [show esFull.1 = dryProofFull.1.map (·.1.entry) from rfl, List.length_map]
    exact congrArg (·.1) dryProofFull_length
  rw [l1, e1, rootsIn_unrun]
  exact congrArg (·.1) roots_all

theorem seats_shared (h2 : Z.made.proof.2.1 = proofSendsFull.2.1)
    (hD1 : D.1.map (·.entry) = esFull.1) (hD2 : D.2.1.map (·.entry) = esFull.2.1) :
    chainSeats 1 (rootsBefore D.1 D.1.length) Z.made.proof.2.1 D.2.1 = sharedFull := by
  have e2 : esFull.2.1 = (unrunR dryProofRecsFull dryProofRunsFull1).map (·.1.entry) := rfl
  have f2 : rootsIn esFull.2.1 = rootsRuns dryProofRecsFull dryProofRunsFull1 := by
    funext k
    rw [e2, rootsIn_unrun]
  have hl : D.1.length = esFull.1.length := by rw [← hD1, List.length_map]
  rw [chainSeats_at, rootsBefore_entries, hD1, hD2, hl, roots_first, h2, f2]
  rfl


theorem far_written (h1 : Z.made.proof.1 = proofSendsFull.1)
    (h2 : Z.made.proof.2.1 = proofSendsFull.2.1) (hS : Z.first.shape = shapeFull)
    (hD1 : D.1.map (·.entry) = esFull.1) (hD2 : D.2.1.map (·.entry) = esFull.2.1)
    (x : LinSized) (hx : realSized = some (x, codesFull2)) :
    (∀ q ∈ tenantsAt 83 x, foundLaterB Z D q = true) ∧
      LFull.places.all (foundFirstB Z D) = true ∧ Z.made.proof.1.sends.length ≤ 1000 ∧
      LFull.places.length = 199 ∧
      VerifiableInference.Desc.K12.Door.laidAtCodes codesFull2 Z.made.proof.1 = some LFull ∧
      foundFirstB Z D N0Full.w = true ∧ foundFirstB Z D N0Full.index = true := by
  have a := seats_first Z D h1 hS hD1
  have b := seats_shared Z D h2 hD1 hD2
  have t := hten_written
  rw [hx] at t
  have f : foundFirstB Z D = firstAt := by
    funext q
    unfold foundFirstB firstAt
    rw [a]
  refine ⟨fun q hq => ?_, ?_, ?_, laid_sizes.2.1, ?_, ?_, ?_⟩
  · unfold foundLaterB
    rw [a, b]
    exact List.all_eq_true.1 t q hq
  · rw [f]
    exact hpl_written
  · rw [h1, laid_sizes.1]
    decide
  · rw [h1]
    exact laid_written
  · rw [f]
    exact hwi_written.1
  · rw [f]
    exact hwi_written.2

end

end Second.Seam

#print axioms Second.Seam.hpl_written
#print axioms Second.Seam.seats_are_places
#print axioms Second.Seam.hwi_written
#print axioms Second.Seam.hten_written
#print axioms Second.Seam.tenants_are
#print axioms Second.Seam.far_not
#print axioms Second.Seam.seats_first
#print axioms Second.Seam.seats_shared
#print axioms Second.Seam.far_written
