-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.WrittenAtSeats
import Johnson.Loose.H2K12.ClosedAtSeats
import Johnson.Desc.K12.Law.SitsBats
import Johnson.Desc.K12.Law.StretchFull
import Johnson.Goal.Numbers.PlanWrittenDescScope
/-
Johnson/Loose/H2K12/OmegaIsSome.lean: IN THE GOALS' SCOPE THE PLAN HAS A PLACE FOR OMEGA's TEST:
`N.O = some nO`.

Why. Every top at the seat of Omega's test (the kind K12, place ⟨2, none, 10⟩) stands under two
letters: (nO) (hO : N.O = some nO). `placesOfMade` makes that place only where the made plan's
shared chain has a second round "BAT", its stretch has the test's names, and the plan's shape asks
for the split; else it is `none`, and the shared chain's description has no entry there. If nothing
said that it is `some`, all these tops could be idle in scope.
How: by counting. The description's shared chain declares: what stands in front of the folded row's
test (no round named "BAT"); that test's own rounds (one); an entry for each member of `N.O.toList`;
the chain's end (one round, "SEAL"). Where its declared rounds, written out, are the written
lists, the shared chain has as many rounds named "BAT" as the written list: two, by the kernel. With
`N.O = none` it would have one.
Main names:
  `batsR_append`, `sharedEnd_rounds`: tools.
  `bats_shared_full`: the written list of the shared chain has two rounds named "BAT": by the
    kernel.
  `omega_some_at_seat`: from the description's tests on the plan, and "its declared rounds, written
    out, are the written lists".
  `omega_some_in_scope`: from `VerifierAndGoals.InScope S`, the description's tests on the plan, and a yes of
    the test `seatPinnedProof`.
Limits: it says that the place is there, not what it holds (that is PlacesAtScope.lean's and its
like). The premise `seatPinnedProof` is asked by the value that is laid for the proof file, not by
the description. The written lists are what a print showed (Johnson/G/DryProofLit.lean). The
full size's scope only. Nothing on soundness. Nothing on hiding.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Made (batsR bats)
open H2K.Member (xsShared)
open Johnson.G (dryProofFull)

theorem batsR_append (a b : List Fmt.DeclaredRound) : batsR (a ++ b) = batsR a + batsR b := by
  unfold batsR bats
  rw [List.map_append, List.filter_append, List.length_append]

/-- The shared chain's end declares one round: the sealing round. -/
theorem sharedEnd_rounds (Cl' : Type) (P : _root_.Desc.K14.P14) (N : H2U.Places4) :
    (sharedEnd Cl' P N).rounds = [ChainEnd.sealRound] := rfl

/-- The written list of the shared chain has two rounds named "BAT". -/
theorem bats_shared_full : bats (xsShared.map (·.entry)) = 2 := by decide +kernel

/-- **The plan has a place for Omega's test**, where the description's declared rounds, written out,
are the written lists. -/
theorem omega_some_at_seat (o : ProofFile.SecondHashFunctionArgument) (mk : ProofFile.LinksBy) (Z : ProofFile.Pub)
    (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hW : Johnson.G.OfPlan.writtenOf "proof file" (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks =
      .ok dryProofFull) : ∃ nO, N.O = some nO := by
  cases hO : N.O with
  | some nO => exact ⟨nO, rfl⟩
  | none =>
    exfalso
    have h2 : batsR (descN o mk guardedProximityTestParts Z N c).roundsDeclaredByBlocks.2.1 = 2 := by
      unfold batsR
      rw [← entries_of_rounds (H2K.Pub.chains_of_written hW).2.1]
      exact bats_shared_full
    have hd := decl_atU o mk Z N c
    rw [hO] at hd
    have hE : batsR ((((none : Option H2U.PlaceNums).toList.map fun nO => omegaEntry ProofFile.Cl nO) ++
        [sharedEnd ProofFile.Cl (p14N Z N) N]).flatMap (·.rounds)) = 0 := by
      show batsR ([sharedEnd ProofFile.Cl (p14N Z N) N].flatMap (·.rounds)) = 0
      rw [List.flatMap_singleton, sharedEnd_rounds]
      rfl
    rw [hd, batsR_append, batsR_append, sharedPre_bats,
      k12_bats guardedProximityTestParts (pGu N) (plan_at_seat_U o Z mk N c hp), hE] at h2
    omega

/-- **In the goals' scope.** -/
theorem omega_some_in_scope {o : ProofFile.SecondHashFunctionArgument} {S : VerifierAndGoals.PublicFiles} (hS : VerifierAndGoals.InScope S = true)
    (Z : ProofFile.Pub) (mk : ProofFile.LinksBy) (N : H2U.Places4) (c : Chain First.S ProofFile.Cl)
    (hp : (descN o mk guardedProximityTestParts Z N c).planOk = true)
    (hpin : VerifiableInference.PlanWritten.seatPinnedProof S.pol
      (descN o mk guardedProximityTestParts Z N c) = true) : ∃ nO, N.O = some nO :=
  omega_some_at_seat o mk Z N c hp
    (VerifiableInference.PlanWritten.seat_in_scope _ _ S hS hpin).1

end H2K.JointK

#print axioms H2K.JointK.bats_shared_full
#print axioms H2K.JointK.omega_some_at_seat
#print axioms H2K.JointK.omega_some_in_scope
