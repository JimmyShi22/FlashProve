-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/StagesAtHead.lean: under the library's head of a counted statement
(`P5J.AtMg`, Johnson/P5J/AtMg.lean), at the numbers at which the proof file's description seats its
four proximity tests (`AtProof.fourOf Np`, AtProof/Places.lean), the stages are the written lists of
the full size (Johnson/Desc/K12/Law/PlacesFull.lean), and so they pass `StagesOk` (RunBy.lean), the
hypothesis of `runBy_eq`.

  `nums_at_head`   the seated numbers are the planner's own at all four places: the maker of a
                 place's numbers has not fallen to its empty value
  `stages_at_head`   the public part has its four places, Omega's among them, and the stages at
                 each are the written list
  `stagesOk_at_head`   `StagesOk` at each

By what. Calls of the library's theorems. The planner's sized stages are the typed sizes at all
public files in the goals' scope (`atFull_of_pubPlain`, Johnson/Loose/H2K12/AtFullPlain.lean); the
places made of them have the written lists (`place_U_of_full` and its fellows,
Johnson/Desc/K12/Law/Sizes/PlacesAtScope.lean); where the description passes its own test on the
plan each seated place has the numbers that it was made of (`RowK12.nums` over `k12_sits_row`,
Johnson/Loose/H2K12/SitsRow.lean); Omega's place is there (`omega_some_in_scope`,
Johnson/Loose/H2K12/OmegaIsSome.lean). Then the kernel's theorems at the written lists
(RunBySpecAt.lean).

Limits. This file's own yield is the equations with the written lists: `StagesOk` alone is had in
StagesOfPlan.lean (`stagesOk_seated`) without a written list, without the premise on the layout
file, and with Omega's place under "there is". It speaks of the seated numbers: `fourOf`'s four
terms are the library's `pGu`, `pGomega`, `pOwn`, `pL` (`fourOf_eq`, StagesOfPlan.lean), on whose
blocks the description's entries of the kind sit (`RowK12`, Johnson/Loose/H2K12/SitsRow.lean). That
a job is laid at these numbers is for whoever lays the job to show: `jobAtU` and `jobAtOmega`
(JobShared.lean) take their `P12` as a parameter. Under the head: that the head holds is a theorem
at one set of public files (`headMember_zFull`, AtFullSide/Top/HeadMemberAtFull.lean). The full size
alone: the head has the goals' scope as a field; nothing on the smaller example's places. That the
makers return is part of the head, not shown here. The first chain's last test stands under the
closed sentence `LayoutGroupsAre` on the stored layout file
(Johnson/Desc/K12/Law/Sizes/LastAtScope.lean), a premise here; it is a theorem in the side library
(`layoutGroupsAre`, AtFullSide/LayoutRead/GroupsPaid.lean), which no file under Johnson/ imports.
The key file's tests: at three of its four, at written parameter sets, RunBySpecAt.lean. `StagesOk`
reads public numbers alone: nothing here speaks of a random value. Words: the head is the structure
`P5J.AtMg`; a test on the plan is the field `planOk` of a block or of a description; the public part
is what `ProofFile.pubPlain` makes of the three public files; the scope is `VerifierAndGoals.InScope`; a place is a
`VerifiableInference.Desc.Place`. It imports Mathlib. Nothing on completeness, soundness or hiding.

Terms: RunBySpec.lean.
-/
import Johnson.P5J.AtMg
import Johnson.Loose.H2K12.SitsRow
import Johnson.Loose.H2K12.AtFullPlain
import Johnson.Loose.H2K12.ChainAtLast
import Johnson.Loose.H2K12.OmegaIsSome
import Johnson.Desc.K12.Law.Sizes.PlacesAtScope
import Johnson.Desc.Laid.ProofAsksLaw
import Johnson.Desc.ProofFile.Honest.K12.RunBySpecAt
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Places

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (guardedProximityTestParts)
open H2K.Member (piUFull piOFull piWFull piLFull)
open H2K.JointK (descN pL pGu pGomega pOwn)
open ProofFile.Honest.K12.AtProof (four fourOf)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- Under the head each seated place has the numbers that it was made of, and Omega's place is
there. -/
theorem nums_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    (fourOf Np).L.nums = Np.L.nums ∧ (fourOf Np).U.nums = Np.U.nums ∧
      (∃ nO, Np.O = some nO ∧ (pGomega nO).nums = nO.nums) ∧ (fourOf Np).W.nums = Np.W.nums := by
  obtain ⟨Z', N', c', hZ', hN', e, R⟩ :=
    H2K.JointK.k12_sits_row o Z.pol Z.lay Z.KL _ h.laid.value
  have eZ : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  subst eZ
  have eN : N' = Np := Except.ok.inj (hN'.symm.trans h.laid.places)
  subst eN
  have hp : (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c').planOk = true := by
    rw [← e]
    exact h.laid.planOk
  have hpin : VerifiableInference.PlanWritten.seatPinnedProof Z.pol
      (descN o ProofFile.pureRoad.links guardedProximityTestParts Z' N' c') = true := by
    rw [← e]
    exact LPFD.asks_written h.laid.asks
  obtain ⟨nL, nU, nO', nW⟩ := R.nums hp
  obtain ⟨nO, hO⟩ := H2K.JointK.omega_some_in_scope h.scope Z' ProofFile.pureRoad.links N' c' hp hpin
  exact ⟨nL, nU, ⟨nO, hO, nO' nO hO⟩, nW⟩

/-- **Under the head the public part has its four places, Omega's among them, and the stages at the
numbers at which the description seats the tests are the written lists.** -/
theorem stages_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    four Zp = some (fourOf Np) ∧
    (fourOf Np).U.nums.stages = piUFull.nums.stages ∧
    (∃ p, (fourOf Np).O = some p ∧ p.nums.stages = piOFull.nums.stages) ∧
    (fourOf Np).W.nums.stages = piWFull.nums.stages ∧
    (H2K.Sizes.LayoutGroupsAre → (fourOf Np).L.nums.stages = piLFull.nums.stages) := by
  have A := H2K.Sizes.atFull_of_pubPlain h.scope h.laid.pub
  obtain ⟨nL, nU, ⟨nO, hO, nOm⟩, nW⟩ := nums_at_head h
  refine ⟨?_, ?_, ⟨pGomega nO, ?_, ?_⟩, ?_, fun hG => ?_⟩
  · unfold four
    rw [h.laid.places]
  · rw [nU]
    exact (H2K.Sizes.place_U_of_full A h.laid.places).1
  · show Np.O.map _ = _
    rw [hO]
    rfl
  · rw [nOm]
    exact (H2K.Sizes.place_O_of_full A h.laid.places nO hO).1
  · rw [nW]
    exact (H2K.Sizes.place_W_of_full A h.laid.places).1
  · rw [nL]
    exact (H2K.Sizes.place_L_of_full A h.laid.places
      (H2K.JointK.stages_of_pubPlain hG h.scope h.laid.pub)).1

/-- **`StagesOk` at the seated numbers, under the head.** -/
theorem stagesOk_at_head (h : P5J.AtMg o Z D r Zp Np cF) :
    StagesOk (fourOf Np).U.nums.stages = true ∧
    (∀ p, (fourOf Np).O = some p → StagesOk p.nums.stages = true) ∧
    StagesOk (fourOf Np).W.nums.stages = true ∧
    (H2K.Sizes.LayoutGroupsAre → StagesOk (fourOf Np).L.nums.stages = true) := by
  obtain ⟨_, eU, ⟨q, hq, eO⟩, eW, eL⟩ := stages_at_head h
  refine ⟨?_, fun p hp => ?_, ?_, fun hG => ?_⟩
  · rw [eU]
    exact SpecAt.stagesOk_piUFull
  · obtain rfl : q = p := Option.some.inj (hq.symm.trans hp)
    rw [eO]
    exact SpecAt.stagesOk_piOFull
  · rw [eW]
    exact SpecAt.stagesOk_piWFull
  · rw [eL hG]
    exact SpecAt.stagesOk_piLFull

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.nums_at_head
#print axioms ProofFile.Honest.K12.Light.stages_at_head
#print axioms ProofFile.Honest.K12.Light.stagesOk_at_head
