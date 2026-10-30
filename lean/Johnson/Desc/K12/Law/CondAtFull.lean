-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/CondAtFull.lean: the condition of the law of a proximity test (the kind K12),
and the two forms "every written round is below", at the four places of a proof file that are made
off ANY plan whose sized record is the full size's, by carrying the closed members over.

Why. CondMembersFull.lean and RoundsHoldPlaces.lean show them at four closed places.
Sizes/StageSizesAtScope.lean says of a planner's record `AtFull`: its setting, its stages and some
more numbers are the typed full-size ones; and shows it from `configure`'s yes at every set of
public files in the goals' scope. Sizes/PlacesAtScope.lean and Sizes/MoreAtScope.lean draw from
`AtFull` the made places' stages, bits of work, radii, rows and own mask. CondTransport.lean carries
a member over to a place that agrees with it in what is read.
Main names:
  `nums_of_pubOk`: a place at which `pubOk` says yes has the numbers that it was made of.
  `k12Condition_at_full_U`, `_O`, `_W`, `_L`: the condition at `proximityTestParametersAt place X.U` and its like, at
    the planner's radii (`radBy`) and 2^-128.
  `roundsHold_at_full_U`, `_O`, `_W`, `_L`: `RoundsHoldAt` (RoundsHold.lean) there.
    `roundsBelow_at_full_U` and its like: so `RoundsBelowAt`.
The premises of the condition's four, all: `AtFull m.p.chains.made`; `placesOfMade m = .ok X`;
`pubOk` at the place and the record's codes K (a yes of the block's step pays it); and ONE NAMED
PREMISE: the made place's written rounds are the closed member's: `writtenOf X.U.nums = writtenOf
piUFull.nums`. At the last test besides: the record's stages of that test are the typed list.
The premises of the eight on the rounds, all: `AtFull`; `placesOfMade`'s yes; the named premise;
and, in `pubOk`'s place, the test on the plan of the kind's block at the place: NO CODES AND NO
RECORD: sentences on public data alone. At the last test besides TWO: the record's stages of that
test are the typed list; the made place's rows are the closed member's.
No test on the plan's prices is asked: neither `planTestsB`, nor `planBatsB`, nor anything on the
plans' rounds "BASE" or "BAT".
Who can pay the named premise: `written_of_fields` (CondTransport.lean) gives it from eight
equations. Four follow from `AtFull` (the stages, the work, the rows, the own mask). Four hang on
the plans' rounds and sendings, not on sizes: the first free own number, the first tree's number,
and of the trees of the test's group whether there are any and the numbers of the chain's own among
them. `written_at_full_U` and its like take these four as premises.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: the closed members' limits stand (CondMembersFull.lean, RoundsHoldPlaces.lean): one round's
share, no sum; part of the 128 bits is work at "CS" and "BASE"; "BAT"'s number is priced and is no
law's count. `RoundsBelowAt` holds no clause on the radii: the weight lies in `RoundsHoldAt`.
`AtFull` has no member by theorem here. The full size only. Nothing on soundness of a verifier.
Nothing on hiding.

-/
import Johnson.Desc.K12.Law.Sizes.PlacesAtScope
import Johnson.Desc.K12.Law.Sizes.MoreAtScope
import Johnson.Desc.K12.Law.CondTransport
import Johnson.Desc.K12.Law.RoundsHoldPlaces

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2U (placesOfMade Places4 PlaceNums proximityTestParametersAt noP12)
open H2K.Made (nums_of_planOk)
open H2K.Member (piUFull piOFull piWFull piLFull rUFull rOFull rWFull rLFull szLFull)
open H2K.Sizes
open scoped ENNReal

/-- A place at which `pubOk` says yes has the numbers that it was made of. -/
theorem nums_of_pubOk (place : Place) (x : PlaceNums) (K : Codes)
    (hp : pubOk (proximityTestParametersAt place x) K = true) : (proximityTestParametersAt place x).nums = x.nums := by
  unfold proximityTestParametersAt at hp ⊢
  split
  · rename_i hc
    rw [if_pos hc] at hp
    exact absurd hp (by simp [pubOk, pubL, noP12, ok])
  · rename_i hc
    rw [if_neg hc] at hp
    split
    · rfl
    · rename_i ho
      rw [ho] at hp
      exact absurd hp (by simp [pubOk, pubL, noP12, ok])

section
variable {m : Made} (A : AtFull m.p.chains.made) {X : Places4} (h : placesOfMade m = .ok X)
  (place : Place) (K : Codes)
include A h

/-! ## U -/

theorem k12Condition_at_full_U (hW : writtenOf X.U.nums = writtenOf piUFull.nums)
    (hpub : pubOk (proximityTestParametersAt place X.U) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      (proximityTestParametersAt place X.U) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_pubOk place X.U K hpub
  obtain ⟨e1, _, e3⟩ := place_U_of_full A h
  exact k12Condition_of_member (r := rUFull) k12Condition_piUFull_r (by rw [hn]; exact e1)
    (by rw [hn]; exact hW) (by rw [hn]; exact e3) hpub

theorem roundsHold_at_full_U {Cl : Type}
    (hW : writtenOf X.U.nums = writtenOf piUFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.U) : Block T12 Cl).planOk = true) :
    RoundsHoldAt (proximityTestParametersAt place X.U)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_planOk place X.U hp
  obtain ⟨e1, _, e3⟩ := place_U_of_full A h
  exact roundsHoldAt_of_member (r := rUFull) roundsHold_piUFull (by rw [hn]; exact e1)
    (by rw [hn]; exact (more_U_of_full A h).1) (by rw [hn]; exact hW) (by rw [hn]; exact e3)

theorem roundsBelow_at_full_U {Cl : Type}
    (hW : writtenOf X.U.nums = writtenOf piUFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.U) : Block T12 Cl).planOk = true) :
    RoundsBelowAt (proximityTestParametersAt place X.U)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.folded.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_full_U A h place hW hp).below

/-- The named premise, from the four equations that hang on the plans' rounds. -/
theorem written_at_full_U (h5 : X.U.nums.free = piUFull.nums.free)
    (h6 : X.U.nums.firstTree = piUFull.nums.firstTree)
    (h7 : X.U.nums.first.isEmpty = piUFull.nums.first.isEmpty)
    (h8 : X.U.nums.first.filterMap ownOf = piUFull.nums.first.filterMap ownOf) :
    writtenOf X.U.nums = writtenOf piUFull.nums := by
  obtain ⟨e1, e2, _⟩ := place_U_of_full A h
  obtain ⟨r1, r2, _⟩ := more_U_of_full A h
  exact writtenOf_reads r1 e2 e1 r2 h5 h6 ⟨h7, h8⟩

/-! ## O -/

theorem k12Condition_at_full_O (o : PlaceNums) (ho : X.O = some o)
    (hW : writtenOf o.nums = writtenOf piOFull.nums)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      (proximityTestParametersAt place o) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_pubOk place o K hpub
  obtain ⟨e1, _, e3⟩ := place_O_of_full A h o ho
  exact k12Condition_of_member (r := rOFull) k12Condition_piOFull_r (by rw [hn]; exact e1)
    (by rw [hn]; exact hW) (by rw [hn]; exact e3) hpub

theorem roundsHold_at_full_O {Cl : Type} (o : PlaceNums) (ho : X.O = some o)
    (hW : writtenOf o.nums = writtenOf piOFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true) :
    RoundsHoldAt (proximityTestParametersAt place o)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_planOk place o hp
  obtain ⟨e1, _, e3⟩ := place_O_of_full A h o ho
  exact roundsHoldAt_of_member (r := rOFull) roundsHold_piOFull (by rw [hn]; exact e1)
    (by rw [hn]; exact (more_O_of_full A h o ho).1) (by rw [hn]; exact hW) (by rw [hn]; exact e3)

theorem roundsBelow_at_full_O {Cl : Type} (o : PlaceNums) (ho : X.O = some o)
    (hW : writtenOf o.nums = writtenOf piOFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true) :
    RoundsBelowAt (proximityTestParametersAt place o)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_full_O A h place o ho hW hp).below

/-- The named premise, from the four equations that hang on the plans' rounds. -/
theorem written_at_full_O (o : PlaceNums) (ho : X.O = some o) (h5 : o.nums.free = piOFull.nums.free)
    (h6 : o.nums.firstTree = piOFull.nums.firstTree)
    (h7 : o.nums.first.isEmpty = piOFull.nums.first.isEmpty)
    (h8 : o.nums.first.filterMap ownOf = piOFull.nums.first.filterMap ownOf) :
    writtenOf o.nums = writtenOf piOFull.nums := by
  obtain ⟨e1, e2, _⟩ := place_O_of_full A h o ho
  obtain ⟨r1, r2, _⟩ := more_O_of_full A h o ho
  exact writtenOf_reads r1 e2 e1 r2 h5 h6 ⟨h7, h8⟩

/-! ## W -/

theorem k12Condition_at_full_W (hW : writtenOf X.W.nums = writtenOf piWFull.nums)
    (hpub : pubOk (proximityTestParametersAt place X.W) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      (proximityTestParametersAt place X.W) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_pubOk place X.W K hpub
  obtain ⟨e1, _, e3⟩ := place_W_of_full A h
  exact k12Condition_of_member (r := rWFull) k12Condition_piWFull_r (by rw [hn]; exact e1)
    (by rw [hn]; exact hW) (by rw [hn]; exact e3) hpub

theorem roundsHold_at_full_W {Cl : Type}
    (hW : writtenOf X.W.nums = writtenOf piWFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.W) : Block T12 Cl).planOk = true) :
    RoundsHoldAt (proximityTestParametersAt place X.W)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_planOk place X.W hp
  obtain ⟨e1, _, e3⟩ := place_W_of_full A h
  exact roundsHoldAt_of_member (r := rWFull) roundsHold_piWFull (by rw [hn]; exact e1)
    (by rw [hn]; exact (more_W_of_full A h).1) (by rw [hn]; exact hW) (by rw [hn]; exact e3)

theorem roundsBelow_at_full_W {Cl : Type}
    (hW : writtenOf X.W.nums = writtenOf piWFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.W) : Block T12 Cl).planOk = true) :
    RoundsBelowAt (proximityTestParametersAt place X.W)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.own.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_full_W A h place hW hp).below

/-- The named premise, from the four equations that hang on the plans' rounds. -/
theorem written_at_full_W (h5 : X.W.nums.free = piWFull.nums.free)
    (h6 : X.W.nums.firstTree = piWFull.nums.firstTree)
    (h7 : X.W.nums.first.isEmpty = piWFull.nums.first.isEmpty)
    (h8 : X.W.nums.first.filterMap ownOf = piWFull.nums.first.filterMap ownOf) :
    writtenOf X.W.nums = writtenOf piWFull.nums := by
  obtain ⟨e1, e2, _⟩ := place_W_of_full A h
  obtain ⟨r1, r2, _⟩ := more_W_of_full A h
  exact writtenOf_reads r1 e2 e1 r2 h5 h6 ⟨h7, h8⟩

/-! ## L -/

theorem k12Condition_at_full_L
    (hL : m.p.chains.made.sized.proof.last.stages = szLFull)
        (hW : writtenOf X.L.nums = writtenOf piLFull.nums)
    (hpub : pubOk (proximityTestParametersAt place X.L) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      (proximityTestParametersAt place X.L) K ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_pubOk place X.L K hpub
  obtain ⟨e1, _, e3⟩ := place_L_of_full A h hL
  exact k12Condition_of_member (r := rLFull) k12Condition_piLFull_r (by rw [hn]; exact e1)
    (by rw [hn]; exact hW) (by rw [hn]; exact e3) hpub

theorem roundsHold_at_full_L {Cl : Type}
    (hL : m.p.chains.made.sized.proof.last.stages = szLFull)
    (hR : X.L.nums.rows = piLFull.nums.rows)
    (hW : writtenOf X.L.nums = writtenOf piLFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.L) : Block T12 Cl).planOk = true) :
    RoundsHoldAt (proximityTestParametersAt place X.L)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) := by
  have hn := nums_of_planOk place X.L hp
  obtain ⟨e1, _, e3⟩ := place_L_of_full A h hL
  exact roundsHoldAt_of_member (r := rLFull) roundsHold_piLFull (by rw [hn]; exact e1)
    (by rw [hn]; exact hR) (by rw [hn]; exact hW) (by rw [hn]; exact e3)

theorem roundsBelow_at_full_L {Cl : Type}
    (hL : m.p.chains.made.sized.proof.last.stages = szLFull)
    (hR : X.L.nums.rows = piLFull.nums.rows)
    (hW : writtenOf X.L.nums = writtenOf piLFull.nums)
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place X.L) : Block T12 Cl).planOk = true) :
    RoundsBelowAt (proximityTestParametersAt place X.L)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.last.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  (roundsHold_at_full_L A h place hL hR hW hp).below

end

end H2K.Pub

#print axioms H2K.Pub.nums_of_pubOk
#print axioms H2K.Pub.k12Condition_at_full_U
#print axioms H2K.Pub.roundsHold_at_full_U
#print axioms H2K.Pub.roundsBelow_at_full_U
#print axioms H2K.Pub.k12Condition_at_full_O
#print axioms H2K.Pub.roundsHold_at_full_O
#print axioms H2K.Pub.roundsBelow_at_full_O
#print axioms H2K.Pub.k12Condition_at_full_W
#print axioms H2K.Pub.roundsHold_at_full_W
#print axioms H2K.Pub.roundsBelow_at_full_W
#print axioms H2K.Pub.k12Condition_at_full_L
#print axioms H2K.Pub.roundsHold_at_full_L
#print axioms H2K.Pub.roundsBelow_at_full_L
#print axioms H2K.Pub.written_at_full_U
#print axioms H2K.Pub.written_at_full_O
#print axioms H2K.Pub.written_at_full_W
