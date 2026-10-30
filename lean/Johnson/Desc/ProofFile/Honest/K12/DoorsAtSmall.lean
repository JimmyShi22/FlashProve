-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DoorsAtSmall.lean

What it proves. At the small made-up chain of SharedSmall.lean (P3) the premises on the two
fall-backs that DoorsByShape.lean's theorems ask are met, by the kernel's evaluation. So at P3, at
the states of doorUF and doorOmegaF, at every input and whatever precedes the test, whatever the
readers of the key and of the columns are: the three tests stTidyB, stPlainB and claimsB hold; the
shape is one term; and layFits is true at jobAtU and jobAtOmega with these state functions, at the
job's own state on entry.

Names.
  lengths_P3   the codes' lengths are in order at P3.
  three_fallOmega_small, near_fallU_small, near_fallOmega_small   the premises on the fall-backs.
  three_small_UF, three_small_OmegaF   the three tests.
  shape_small_UF, shape_small_OmegaF   the shapes.
  layFits_small_UF, layFits_small_OmegaF   layFits at the two jobs.
  The guards hold the term at G_omega against the honest state of PubAtSmallDoor.lean.

Limits. One small made-up plan. The theorems are also true of the fall-backs: they do not tell a
fold that failed from one that returned, and they are no statement that the state on entry is the
verifier's. At G_omega the guard hands doorOf columns that are made with the random values of the
test on G_u; a part is handed no opened column. It stands over files that are not in the library
yet, as MarksBehind.lean does. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorsByShape
import Johnson.Desc.ProofFile.Honest.K12.MarksAtSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (St blocks first)
open Desc.K14.Shape (doorO)
open ProofFile.Honest.Sh (testSh)

variable {W X : Type}

theorem lengths_P3 : P3.codes.lengthsOk = true := by decide +kernel

theorem three_fallOmega_small : Three (fallOmega P3 sentU3 p) :=
  (three_iff _).1 (by decide +kernel)

theorem near_fallU_small : pubNear (fallU P3 sentU3) = nearOf (pubBehind P3 sentU3) 0 := by
  decide +kernel

theorem near_fallOmega_small :
    pubNear (fallOmega P3 sentU3 p) = nearOf (pubBehind P3 sentU3) 1 := by
  decide +kernel

/-- **The three tests at doorUF's state, at P3.** -/
theorem three_small_UF (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) : Three (doorUF P3 sentU3 bs3 key cols w fr) :=
  three_doorUF P3 bs3 blocks_P3 planOk_bs3 splits_P3 sentU3 withU_P3 three_fallU_small key cols w
    fr

/-- **The three tests at doorOmegaF's state, at P3.** -/
theorem three_small_OmegaF (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) : Three (doorOmegaF P3 sentU3 bs3 p key cols w fr) :=
  three_doorOmegaF P3 bs3 blocks_P3 planOk_bs3 splits_P3 ahead_P3 sentU3 withU_P3 lengths_P3 p
    planOk_p three_fallOmega_small key cols w fr

theorem shape_small_UF (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    testSh (doorUF P3 sentU3 bs3 key cols w fr) = Desc.K14.Shape.doorU (endOf P3 sentU3) :=
  shape_doorUF P3 bs3 blocks_P3 splits_P3 sentU3 withU_P3 key cols w fr

theorem shape_small_OmegaF (key : W → TableKey) (cols : W → Front X → List OpenedColumn) (w : W)
    (fr : Front X) :
    testSh (doorOmegaF P3 sentU3 bs3 p key cols w fr) = doorO (endOmega P3 sentU3 p) :=
  shape_doorOmegaF P3 bs3 blocks_P3 splits_P3 sentU3 withU_P3 p planOk_p key cols w fr

/-- **layFits at jobAtU with doorUF, at the job's own state on entry.** -/
theorem layFits_small_UF (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E))
    (w : W) (fr : Front X) :
    (jobAtU ⟨P3, 0⟩ p (doorUF P3 sentU3 bs3 key cols) weights rand u?).layFits
      ((jobAtU ⟨P3, 0⟩ p (doorUF P3 sentU3 bs3 key cols) weights rand u?).rec₀ w fr) = true := by
  show (jobAtU ⟨P3, 0⟩ p (doorUF P3 sentU3 bs3 key cols) weights rand u?).layFits
    (doorUF P3 sentU3 bs3 key cols w fr) = true
  rw [layFits_near,
    near_doorUF P3 bs3 blocks_P3 splits_P3 ahead_P3 sentU3 withU_P3 near_fallU_small key cols w fr,
    layFitsNear_congr (jobAtU ⟨P3, 0⟩ p (doorUF P3 sentU3 bs3 key cols) weights rand u?)
      (pubJob p (shapesAtU ⟨P3, 0⟩ p)) rfl
      ((shapes_atU ⟨P3, 0⟩ p _ weights rand u?).trans (shapes_pubJob _ _).symm)]
  exact layFitsNear_U

/-- **The same at jobAtOmega with doorOmegaF.** -/
theorem layFits_small_OmegaF (key : W → TableKey) (cols : W → Front X → List OpenedColumn)
    (weights : W → Weights) (rand : W → TableRand)
    (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) :
    (jobAtOmega ⟨P3, 0⟩ pO (doorOmegaF P3 sentU3 bs3 p key cols) weights rand omega?).layFits
      ((jobAtOmega ⟨P3, 0⟩ pO (doorOmegaF P3 sentU3 bs3 p key cols) weights rand omega?).rec₀ w
        fr) = true := by
  show (jobAtOmega ⟨P3, 0⟩ pO (doorOmegaF P3 sentU3 bs3 p key cols) weights rand omega?).layFits
    (doorOmegaF P3 sentU3 bs3 p key cols w fr) = true
  rw [layFits_near,
    near_doorOmegaF P3 bs3 blocks_P3 splits_P3 ahead_P3 sentU3 withU_P3 p planOk_p
      near_fallOmega_small key cols w fr,
    layFitsNear_congr
      (jobAtOmega ⟨P3, 0⟩ pO (doorOmegaF P3 sentU3 bs3 p key cols) weights rand omega?)
      (pubJob pO (shapesAtOmega ⟨P3, 0⟩ pO)) rfl
      ((shapes_atOmega ⟨P3, 0⟩ pO _ weights rand omega?).trans (shapes_pubJob _ _).symm)]
  exact layFitsNear_Omega

/-! ## Guards -/

-- at the honest rounds and columns the fold over the nine returns: the state has the term's shape
#guard sameDoor (testSh (doorAtOmega colsO () frO)) (doorO (endOmega P3 sentU3 p))
#guard sameDoor (testSh (fallOmega P3 sentU3 p)) (doorO (endOmega P3 sentU3 p))
-- the term behind the test on G_u is another than the term in front of it
#guard !decide ((endOmega P3 sentU3 p).core = (endOf P3 sentU3).core)
-- the old fall-back at G_omega has another shape
#guard !sameDoor (testSh (stateOfPub (pubBehind P3 sentU3, 1))) (doorO (endOmega P3 sentU3 p))

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.SharedSmall.lengths_P3
#print axioms ProofFile.Honest.K12.Light.SharedSmall.three_fallOmega_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.near_fallU_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.near_fallOmega_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.three_small_UF
#print axioms ProofFile.Honest.K12.Light.SharedSmall.three_small_OmegaF
#print axioms ProofFile.Honest.K12.Light.SharedSmall.shape_small_UF
#print axioms ProofFile.Honest.K12.Light.SharedSmall.shape_small_OmegaF
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_small_UF
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_small_OmegaF
