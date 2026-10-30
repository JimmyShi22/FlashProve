-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
BUILT over Block.lean and State.lean, and over the seats that go
with them (HeadSeatAt.lean, ReplySeatAt.lean).
K6OnB: FOUR Bools on the record in front; pointsB stands in K6AfterB (RowPins.lean's head says why).
k6On_iff: six tests.
Johnson/Desc/Kinds/Law/K6OnB.lean: WHAT K6's LAW ASKS OF THE RECORD IN FRONT (Law/RowPins.lean: K6On) AND WHAT STANDS BEHIND ITS STEP (Law/RowPromise.lean: K6After) AS TESTS WITH CODE: Bools on the public files and the carried record: for the table's promise, which takes such tests alone (by report, not shown here): STATED AND PROVED EQUAL TO THE SENTENCES.
  planB W       TWO ON THE PLAN ALONE: the tests on the plan pass; there is at least one feature. No record is read: they stand beside the plan's tests, evaluated once.
  wellLaidB · startB · tokenB · cEndB · pointsB    FIVE ON THE RECORD: the ledger's three lists have the plan's count of numbers · the kind's part of the test on the request · the heard token, if one is heard, is below V · each number that the lookup's last claim names is filled in the ledger, if the lookup was heard · the two readers of the
                lookup's hearing agree in its points.
  K6OnB · K6AfterB · unmarkedB
  k6On_iff      K6On W s ↔ planB W = true ∧ K6OnB W s = true.     k6After_iff   K6After W s' ↔ unmarkedB s' = true ∧ wellLaidB … ∧ cEndB … ∧ pointsB ….
WHO MAKES EACH, AND FROM WHERE IT IS NEEDED: NOT IN LEAN HERE: BY READING (on a page that is not in this repository). WHAT IT DOES NOT SAY. That any block makes or keeps any of the five but K6's own (rowPromise: K6After behind K6On). NONE HAS RUN AT A RECORD OF A REAL RUN. tokenB and cEndB are free where nothing was heard: that a token and the lookup WERE heard in front of K6 is
asked by the block's own text (given refuses), not here. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.RowPromise

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Model (Fork)
open VerifiableInference.Desc.First (S)

/-- Two on the plan alone. -/
def planB (W : OnBytes.Model.Verify.Public) : Bool :=
  (parOf W.hS (workOf W)).ok &&
    (let _ := (parOf W.hS (workOf W)).sizes
     Decidable.decide (0 < Norm.d))

/-- The ledger's three lists have the plan's count of numbers. -/
def wellLaidB (F : Fork) : Bool :=
  F.gotF.size == F.ns && F.vp.size == F.ns && F.mf.size == F.ns

/-- The kind's part of the test on the request. -/
def startB (W : OnBytes.Model.Verify.Public) (s : S) : Bool :=
  (parOf W.hS (workOf W)).okStart ((seatAt W.hS (readsOf W)).request s)

/-- The heard token, if one is heard, is below V. -/
def tokenB (W : OnBytes.Model.Verify.Public) (s : S) : Bool :=
  match Reply.token (seatAt W.hS (readsOf W)).toSeat s with
  | some y => Decidable.decide (y < (parOf W.hS (workOf W)).sizes.V)
  | none => true

/-- Each number that the lookup's last claim names is filled in the ledger, if the lookup was heard. -/
def cEndB (W : OnBytes.Model.Verify.Public) (s : S) : Bool :=
  match s.lookHeard? with
  | some gk => gk.cEnd.slots.toList.all fun x =>
      ((seatAt W.hS (readsOf W)).ledger s).gotF.getD x.1 false
  | none => true

/-- The two readers of the lookup's hearing agree in its points. -/
def pointsB (s : S) : Bool := Decidable.decide (pointsOf s.look? = pointsOf s.lookHeard?)

/-- The record bears no mark. -/
def unmarkedB (s : S) : Bool := s.failed.isNone

/-- **The four on the record in front.** (pointsB has left: Law/RowPins.lean's head.) -/
def K6OnB (W : OnBytes.Model.Verify.Public) (s : S) : Bool :=
  wellLaidB ((seatAt W.hS (readsOf W)).ledger s) && startB W s && tokenB W s && cEndB W s

/-- **What stands behind.** -/
def K6AfterB (W : OnBytes.Model.Verify.Public) (s' : S) : Bool :=
  unmarkedB s' && wellLaidB ((seatAt W.hS (readsOf W)).ledger s') && cEndB W s' && pointsB s'

namespace Came

theorem wellLaidB_iff (F : Fork) : wellLaidB F = true ↔ WellLaid F := by
  unfold wellLaidB WellLaid
  simp only [Bool.and_eq_true, beq_iff_eq, and_assoc]

theorem tokenB_iff (W : OnBytes.Model.Verify.Public) (s : S) : tokenB W s = true ↔
    ∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V := by
  unfold tokenB
  cases h : Reply.token (seatAt W.hS (readsOf W)).toSeat s with
  | none => exact ⟨fun _ y e => (by cases e), fun _ => rfl⟩
  | some y =>
    exact ⟨fun h1 y' e => (by cases e; exact of_decide_eq_true h1),
      fun h1 => decide_eq_true (h1 y rfl)⟩

theorem cEndB_iff (W : OnBytes.Model.Verify.Public) (s : S) : cEndB W s = true ↔
    ∀ gk, s.lookHeard? = some gk → CEndFilled gk ((seatAt W.hS (readsOf W)).ledger s) := by
  unfold cEndB
  cases h : s.lookHeard? with
  | none => exact ⟨fun _ gk e => (by cases e), fun _ => rfl⟩
  | some gk =>
    constructor
    · intro h1 gk' e x hx
      cases e
      exact (List.all_eq_true.1 h1) x hx
    · intro h1
      exact List.all_eq_true.2 fun x hx => h1 gk rfl x hx

theorem pointsB_iff (s : S) : pointsB s = true ↔ pointsOf s.look? = pointsOf s.lookHeard? := by
  unfold pointsB
  exact decide_eq_true_iff

theorem unmarkedB_iff (s : S) : unmarkedB s = true ↔ s.failed = none := by
  unfold unmarkedB
  exact Option.isNone_iff_eq_none

/-- **K6On is the six tests.** -/
theorem k6On_iff (W : OnBytes.Model.Verify.Public) (s : S) :
    K6On W s ↔ planB W = true ∧ K6OnB W s = true := by
  unfold K6On planB K6OnB startB hasFeatures
  simp only [Bool.and_eq_true, decide_eq_true_eq, wellLaidB_iff, tokenB_iff, cEndB_iff]
  constructor
  · rintro ⟨a, b, c, d', e, f⟩
    exact ⟨⟨b, c⟩, ⟨⟨⟨a, d'⟩, e⟩, f⟩⟩
  · rintro ⟨⟨b, c⟩, ⟨⟨⟨a, d'⟩, e⟩, f⟩⟩
    exact ⟨a, b, c, d', e, f⟩

/-- **K6After is the four tests.** -/
theorem k6After_iff (W : OnBytes.Model.Verify.Public) (s' : S) :
    K6After W s' ↔ K6AfterB W s' = true := by
  unfold K6After K6AfterB
  simp only [Bool.and_eq_true, unmarkedB_iff, wellLaidB_iff, cEndB_iff, pointsB_iff, and_assoc]

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6On_iff
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.k6After_iff
