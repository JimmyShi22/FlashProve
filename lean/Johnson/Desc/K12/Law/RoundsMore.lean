-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/RoundsMore.lean: two joints for RoundsAtMade.lean.

Main names:
  `batV0_eq`: the count `batV0` of BatPriceOk.lean is the count of `RoundsBelowAt` at "BAT": the
    Johnson bound's list at the first stage, times the rows less one.
  `later_split`, `places_split`: Omega's place is made only where the shape says that the shared
    chain splits.
  `k12Condition_at_madeOf_O'`, `roundsBelow_at_madeOf_O'`: the two statements at Omega's place
    without the premise on the split.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: as RoundsAtMade.lean's. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.RoundsAtMade
import Johnson.Desc.K12.Law.BatPriceLaw

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun Johnson.G.OfPlan
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Bridge (Rad baseWorks planTestsB planBats planBatsB)
open H2U (placesOfMade placesLater laterOfProof Places4 PlaceNums Later3 LaterArgs proximityTestParametersAt)
open H2K.Made (workShared written_bat_eq)
open scoped ENNReal

/-! ## One count -/

/-- "BAT"'s count of BatPriceOk.lean, written out at a place whose written rounds are there. -/
theorem batV0_eq (p : P12) (r : Fmt.M1.Stage → ℕ) (a : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hs : p.nums.stages = a :: rest) (w0 : WR) (l : List WR)
    (hw : writtenOf p.nums = some (w0 :: l)) :
    batV0 p r = (sgOf a).lstJ (r (sgOf a).st) * (p.nums.rows - 1) := by
  have hat : batAtB p = some (stN a, w0) := by
    unfold batAtB
    rw [hs, hw]
    rfl
  have hv : batV0 p r = v0On (stN a) (r (stN a)) w0.entry.rows := by
    unfold batV0
    rw [hat]
    rfl
  rw [hv, written_bat_eq p.nums w0 l hw]
  rfl

/-! ## At Omega's place -/

/-- Omega's place is made only where the shape says that the shared chain splits. -/
theorem later_split (A : LaterArgs) (X : Later3) (h : placesLater A = .ok X) :
    ∀ o, X.O = some o → A.batch.shape.sharedSplitNeeded = true := by
  unfold placesLater at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals
    first
    | (cases h
       intro o ho
       by_contra hs
       simp_all)
    | cases h

theorem places_split (m : Made) (X : Places4) (h : placesOfMade m = .ok X) :
    ∀ o, X.O = some o → m.p.chains.made.sized.proof.batch.shape.sharedSplitNeeded = true := by
  unfold placesOfMade at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i X3 hX3
        split at h
        · cases h
        · cases h
          exact later_split _ X3 hX3

section
variable {Cl : Type} {pol lay KL : ByteArray} (m : Made) (hm : madeOf pol lay KL = .ok m)
  (X : Places4) (h : placesOfMade m = .ok X) (place : Place) (K : Codes)
  (hM : planTestsB Rad.planner m.p.chains.made = true)
include hm h hM

/-- `k12Condition_at_madeOf_O` without its premise on the split. -/
theorem k12Condition_at_madeOf_O' (o : PlaceNums) (ho : X.O = some o)
    (hw : (baseWorks m.p.chains.made)[2]? = some (workShared (laterOfProof m 0)))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    K12Condition Sg.lstJ Sg.flC Sg.flZ Sg.flZ
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      (proximityTestParametersAt place o) K ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  k12Condition_at_madeOf_O m hm X h place K hM o ho (places_split m X h o ho) hw hp hpub

/-- `roundsBelow_at_madeOf_O` without its premise on the split. -/
theorem roundsBelow_at_madeOf_O' (hB : planBatsB Rad.planner m.p.chains.made = true)
    (o : PlaceNums) (ho : X.O = some o)
    (hw : (baseWorks m.p.chains.made)[2]? = some (workShared (laterOfProof m 0)))
    (hd : ∀ a rest, (proximityTestParametersAt place o).nums.stages = a :: rest →
      batPlaceOf (proximityTestParametersAt place o)
        (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages) a ∈
        (planBats Rad.planner m.p.chains.made).map (·.2))
    (hp : (proximityTestKind guardedProximityTestParts (proximityTestParametersAt place o) : Block T12 Cl).planOk = true)
    (hpub : pubOk (proximityTestParametersAt place o) K = true) :
    RoundsBelowAt (proximityTestParametersAt place o)
      (radBy m.p.chains.made.sized.proof.set m.p.chains.made.sized.proof.batch.omega.stages)
      ((2 : ℝ≥0∞)⁻¹ ^ 128) :=
  roundsBelow_at_madeOf_O m hm X h place K hM hB o ho (places_split m X h o ho) hw hd hp hpub

end

end H2K.Pub

#print axioms H2K.Pub.batV0_eq
#print axioms H2K.Pub.places_split
#print axioms H2K.Pub.k12Condition_at_madeOf_O'
#print axioms H2K.Pub.roundsBelow_at_madeOf_O'
