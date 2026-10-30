-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Numbers/PlanWrittenMore.lean: small laws around "the description is made at the written
plan values" (Johnson/Goal/Numbers/PlanWrittenRow.lean): the statement taken apart by file, how it
hangs on its yes, what the test from the parameter file is in scope, and two facts for whoever lays
the test in a description's field `fileOk`.

Row or tool. Every declaration here is a tool: the makers and the yes are letters, and no
description is named.

What is here.
  `ProofWrittenAt FP yes`, `KeyWrittenAt FK yes`: the two halves of `PlanWrittenAt`, a file each,
    each with a yes of its own. `planWrittenAt_iff`: at one yes the statement is the two halves
    together. `planWrittenAt_of_halves`: halves under two yeses give the statement under both.
  `ProofSeatLaid FP yes`, `KeySeatLaid FK yes`, `seatLaid_iff`: the like for the named premise
    `SeatLaid`. `proofWrittenAt_of_seat`, `keyWrittenAt_of_seat`: each half follows from its own
    half of the premise. So whoever lays the test in one file's description can show that file's
    half alone.
  `PlanWrittenAt.mono`: a yes that asks more gives a statement that says less: from `yes' Z → yes Z`
    the statement at yes gives the statement at yes'.
  `seat_eq_in_scope_key`: in scope `seatPinnedKey Z.pol F` is `descPinnedKey fullKey F`: the key
    file's like of `seat_eq_in_scope`.
  `seat_iff_in_scope`, `seat_iff_in_scope_key`: in scope the test says yes if and only if, written
    out, the description's declared rounds are the full size's written lists and its depth is 32.
    The way back is what an honest maker needs.
  `lax_eq_full_in_scope`, `lax_eq_in_scope`, `lax_in_scope`: in scope the text with "yes" in the arm
    of the refusal (`laxSeat`, Johnson/Desc/Ok/PlanWritten/Seat.lean) is the test itself, and the
    rule in scope holds of it too. So no rule in scope leans on the arm of the refusal.
  `seat_fileOk`, `seat_fileOk_key`, `data_fileOk`: the tests and `FileDescription.data` do not read the
    field `fileOk`. By definition. So a description may hold the test on itself in that field
    without a circle.

Limits. No description and no yes is named. The halves are shown of no makers. All limits of
Johnson/Goal/Numbers/PlanWrittenRow.lean. Nothing on soundness.


-/
import Johnson.Goal.Numbers.PlanWrittenRow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Desc

variable {Xi XiP XiK : Type}

/-! ## The statement, a file at a time -/

/-- The proof file's half of `PlanWrittenAt`. -/
def ProofWrittenAt (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z →
    (FP Z).data "proof file" = .ok writtenPFull

/-- The key file's half. -/
def KeyWrittenAt (FK : VerifierAndGoals.PublicFiles → FileDescription XiK) (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z → (FK Z).data "key file" = .ok writtenKFull

/-- At one yes the statement is its two halves together. -/
theorem planWrittenAt_iff (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (yes : VerifierAndGoals.PublicFiles → Prop) :
    PlanWrittenAt FP FK yes ↔ ProofWrittenAt FP yes ∧ KeyWrittenAt FK yes :=
  ⟨fun H => ⟨fun Z hZ hy => (H Z hZ hy).1, fun Z hZ hy => (H Z hZ hy).2⟩,
    fun H Z hZ hy => ⟨H.1 Z hZ hy, H.2 Z hZ hy⟩⟩

/-- Halves under two yeses give the statement under both. -/
theorem planWrittenAt_of_halves {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yesP yesK : VerifierAndGoals.PublicFiles → Prop} (hP : ProofWrittenAt FP yesP) (hK : KeyWrittenAt FK yesK) :
    PlanWrittenAt FP FK fun Z => yesP Z ∧ yesK Z :=
  fun Z hZ hy => ⟨hP Z hZ hy.1, hK Z hZ hy.2⟩

/-- The proof file's half of the named premise `SeatLaid`. -/
def ProofSeatLaid (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z → seatPinnedProof Z.pol (FP Z) = true

/-- The key file's half. -/
def KeySeatLaid (FK : VerifierAndGoals.PublicFiles → FileDescription XiK) (yes : VerifierAndGoals.PublicFiles → Prop) : Prop :=
  ∀ Z : VerifierAndGoals.PublicFiles, VerifierAndGoals.InScope Z = true → yes Z → seatPinnedKey Z.pol (FK Z) = true

/-- At one yes the premise is its two halves together. -/
theorem seatLaid_iff (FP : VerifierAndGoals.PublicFiles → FileDescription XiP) (FK : VerifierAndGoals.PublicFiles → FileDescription XiK)
    (yes : VerifierAndGoals.PublicFiles → Prop) : SeatLaid FP FK yes ↔ ProofSeatLaid FP yes ∧ KeySeatLaid FK yes :=
  ⟨fun H => ⟨fun Z hZ hy => (H Z hZ hy).1, fun Z hZ hy => (H Z hZ hy).2⟩,
    fun H Z hZ hy => ⟨H.1 Z hZ hy, H.2 Z hZ hy⟩⟩

/-- **The proof file's half follows from its own half of the premise.** -/
theorem proofWrittenAt_of_seat {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {yes : VerifierAndGoals.PublicFiles → Prop}
    (h : ProofSeatLaid FP yes) : ProofWrittenAt FP yes :=
  fun Z hZ hy => (seat_in_scope XiP (FP Z) Z hZ (h Z hZ hy)).2.2

/-- **So does the key file's.** -/
theorem keyWrittenAt_of_seat {FK : VerifierAndGoals.PublicFiles → FileDescription XiK} {yes : VerifierAndGoals.PublicFiles → Prop}
    (h : KeySeatLaid FK yes) : KeyWrittenAt FK yes :=
  fun Z hZ hy => (seat_in_scope_key XiK (FK Z) Z hZ (h Z hZ hy)).2.2

/-- A yes that asks more gives a statement that says less. -/
theorem PlanWrittenAt.mono {FP : VerifierAndGoals.PublicFiles → FileDescription XiP} {FK : VerifierAndGoals.PublicFiles → FileDescription XiK}
    {yes yes' : VerifierAndGoals.PublicFiles → Prop} (h : ∀ Z, yes' Z → yes Z) (H : PlanWrittenAt FP FK yes) :
    PlanWrittenAt FP FK yes' := fun Z hZ hy => H Z hZ (h Z hy)

/-! ## What the test is in scope -/

/-- In scope the test on a key file's description is the test at the full size's key. -/
theorem seat_eq_in_scope_key {Z : VerifierAndGoals.PublicFiles} (F : FileDescription Xi) (hZ : VerifierAndGoals.InScope Z = true) :
    seatPinnedKey Z.pol F = descPinnedKey fullKey F := by
  obtain ⟨P, hP, hk⟩ := scan_returns_in_scope hZ
  unfold seatPinnedKey
  rw [hP]
  show descPinnedKey (keyOfScan P) F = descPinnedKey fullKey F
  rw [hk]

/-- **In scope the test says yes if and only if** the declared rounds, written out, are the written
lists and the depth is 32. -/
theorem seat_iff_in_scope {Z : VerifierAndGoals.PublicFiles} (F : FileDescription Xi) (hZ : VerifierAndGoals.InScope Z = true) :
    seatPinnedProof Z.pol F = true ↔
      writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 := by
  rw [seat_eq_in_scope F hZ]
  unfold descPinnedProof descPinned declPinned
  rw [if_pos rfl]
  exact declIs_iff _ _ _ _ _

/-- The like for a key file's description. -/
theorem seat_iff_in_scope_key {Z : VerifierAndGoals.PublicFiles} (F : FileDescription Xi) (hZ : VerifierAndGoals.InScope Z = true) :
    seatPinnedKey Z.pol F = true ↔
      writtenOf "key file" F.roundsDeclaredByBlocks = .ok dryKeyFull ∧ F.tableDepth = 32 := by
  rw [seat_eq_in_scope_key F hZ]
  unfold descPinnedKey descPinned declPinned
  rw [if_pos rfl]
  exact declIs_iff _ _ _ _ _

/-- In scope the text with "yes" in the arm of the refusal is the test at the full size's key. -/
theorem lax_eq_full_in_scope {Z : VerifierAndGoals.PublicFiles} (F : FileDescription Xi) (hZ : VerifierAndGoals.InScope Z = true) :
    laxSeat Z.pol F = descPinnedProof fullKey F := by
  obtain ⟨P, hP, hk⟩ := scan_returns_in_scope hZ
  unfold laxSeat
  rw [hP]
  show descPinnedProof (keyOfScan P) F = descPinnedProof fullKey F
  rw [hk]

/-- **So in scope it is the test itself.** -/
theorem lax_eq_in_scope {Z : VerifierAndGoals.PublicFiles} (F : FileDescription Xi) (hZ : VerifierAndGoals.InScope Z = true) :
    laxSeat Z.pol F = seatPinnedProof Z.pol F :=
  (lax_eq_full_in_scope F hZ).trans (seat_eq_in_scope F hZ).symm

/-- And the rule in scope holds of it too: no rule in scope leans on the arm of the refusal. -/
theorem lax_in_scope (F : FileDescription Xi) (Z : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.InScope Z = true)
    (h : laxSeat Z.pol F = true) :
    writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull ∧ F.tableDepth = 32 ∧
      F.data "proof file" = .ok writtenPFull :=
  seat_in_scope Xi F Z hZ ((lax_eq_in_scope F hZ).symm.trans h)

/-! ## The field `fileOk` is not read -/

/-- The test on a proof file's description does not read the field `fileOk`. By definition. -/
theorem seat_fileOk (pol : ByteArray) (F : FileDescription Xi) (b : Bool) :
    seatPinnedProof pol { F with fileOk := b } = seatPinnedProof pol F := rfl

/-- Nor does the test on a key file's description. By definition. -/
theorem seat_fileOk_key (pol : ByteArray) (F : FileDescription Xi) (b : Bool) :
    seatPinnedKey pol { F with fileOk := b } = seatPinnedKey pol F := rfl

/-- Nor do the data that a description hands on. By definition. -/
theorem data_fileOk (F : FileDescription Xi) (b : Bool) (file : String) :
    FileDescription.data { F with fileOk := b } file = F.data file := rfl

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.planWrittenAt_iff
#print axioms VerifiableInference.PlanWritten.planWrittenAt_of_halves
#print axioms VerifiableInference.PlanWritten.seatLaid_iff
#print axioms VerifiableInference.PlanWritten.proofWrittenAt_of_seat
#print axioms VerifiableInference.PlanWritten.keyWrittenAt_of_seat
#print axioms VerifiableInference.PlanWritten.PlanWrittenAt.mono
#print axioms VerifiableInference.PlanWritten.seat_eq_in_scope_key
#print axioms VerifiableInference.PlanWritten.seat_iff_in_scope
#print axioms VerifiableInference.PlanWritten.seat_iff_in_scope_key
#print axioms VerifiableInference.PlanWritten.lax_eq_full_in_scope
#print axioms VerifiableInference.PlanWritten.lax_eq_in_scope
#print axioms VerifiableInference.PlanWritten.lax_in_scope
#print axioms VerifiableInference.PlanWritten.seat_fileOk
#print axioms VerifiableInference.PlanWritten.seat_fileOk_key
#print axioms VerifiableInference.PlanWritten.data_fileOk
