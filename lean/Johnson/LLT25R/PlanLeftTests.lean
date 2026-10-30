-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/PlanLeftTests.lean: NAMED TESTS WITH CODE FOR THE FIELDS OF `LLT25.PlanOk₃` (the premise
hP of the last table's law) THAT ARE TESTS ON FINITE PUBLIC DATA, EACH WITH ITS LAW "the test says true
→ the field's own text". Definitions and laws alone: NO CONTROL, NO EVALUATION, no value of a plan.
General in the letters: the caller lays ms₁ · ms₂ · N₁ · Ns · mine · V · the seat t := (D.t₁ + nΩ, 0).
  test                field(s) of PlanOk₃ | LastPlan8            law
  `someB`             someW · someI · someO                      `some_of`
  `apartB`            apartWO · apartIO · (indexNeW)             `apart_of`
  `oneSeatB`          oneSeat (by a stronger test)               `oneSeat_of`
  `omegaSeatB`        omegaSeat                                  `omegaSeat_of`
  `mineAtB`           mineI · mineW                              `mineAt_of`
  `seatsApartB`       seatsApart                                 `seatsApart_of`
  `allSeatsB`         allSeats                                   `allSeats_of`
  `elderBelowB`       elderBelow                                 `elderBelow_of`
  `oneTableAllB`      oneTable (over oneTableB)                  `oneTableAll_of`
  `nodupB`            nodup                                      `nodup_of`
  `omegaB`            omega                                      `omega_of`
  `fenceB`            fence                                      `fence_of`
NOT HERE: THEY LIE IN OTHER FILES: planAt (planAtAllB · planAtAll_law,
Johnson/P2LawR/PlanLeftAt.lean) · seats (seatsB · seatsB_law, Johnson/P2LawR/PlanLeftSeats.lean: THE
FIELD ASKS THE WHOLE SENDING OF EACH MEMBER) · fence's and placeB's base (fence_of_base ·
placeB_of_base, Johnson/P2LawR/PlanLeftBase.lean: `fence_of` here is the law that they want at the
base D.t₁ + D.t₂) · planShapes · oneOmega (planShapes_iff, Johnson/ToldDescR/BookAtW.lean ·
oneOmega_iff, Johnson/ToldDescR/OneOmegaB.lean) · stretch (hds_of_planOk,
Johnson/LLT25R/LastStretch.lean).
Limits. That a test says true at the release's plan is an evaluation's matter, not this file's.
Nothing on soundness.
-/
import Johnson.LLT25R.LastMine
import Johnson.ToldDescR.OneTableB
import Johnson.Desc.Last.OwnSits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LLT25.PlanB
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Shared
open VerifiableInference.Desc.Last (OwnSeats)

/-- Somebody of the list sits at w. -/
def someB (ms : List Mem) (w : ℕ × ℕ) : Bool := ms.any fun x => decide (x.1.seat x.2 = w)

theorem some_of {ms : List Mem} {w : ℕ × ℕ} (h : someB ms w = true) :
    ∃ x ∈ ms, SitsAt x w.1 w.2 := by
  obtain ⟨x, hx, hd⟩ := List.any_eq_true.1 h
  have e : x.1.seat x.2 = w := of_decide_eq_true hd
  exact ⟨x, hx, e⟩

/-- Two seats are apart. -/
def apartB (a b : ℕ × ℕ) : Bool := decide (a ≠ b)

theorem apart_of {a b : ℕ × ℕ} (h : apartB a b = true) : a ≠ b := of_decide_eq_true h

/-- The seats of mine are without a double. -/
def oneSeatB (mine : List Mem) : Bool := decide ((mine.map seatOf).Nodup)

theorem oneSeat_of {mine : List Mem} (h : oneSeatB mine = true) :
    ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y :=
  fun _ hx _ hy e => List.inj_on_of_nodup_map (of_decide_eq_true h) hx hy e

/-- One of mine sits at t and has the shape sh. -/
def omegaSeatB (mine : List Mem) (t : ℕ × ℕ) (sh : OracleShape) : Bool :=
  mine.any fun x => decide (seatOf x = t) && decide (sh = (x.1.l.get x.2).1)

theorem omegaSeat_of {mine : List Mem} {t : ℕ × ℕ} {sh : OracleShape}
    (h : omegaSeatB mine t sh = true) :
    ∃ x ∈ mine, seatOf x = t ∧ sh = (x.1.l.get x.2).1 := by
  obtain ⟨x, hx, hd⟩ := List.any_eq_true.1 h
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 hd
  exact ⟨x, hx, of_decide_eq_true a, of_decide_eq_true b⟩

/-- The same, the equation of shapes the other way round (as mineI and mineW have it). -/
def mineAtB (mine : List Mem) (t : ℕ × ℕ) (sh : OracleShape) : Bool :=
  mine.any fun x => decide (seatOf x = t) && decide ((x.1.l.get x.2).1 = sh)

theorem mineAt_of {mine : List Mem} {t : ℕ × ℕ} {sh : OracleShape}
    (h : mineAtB mine t sh = true) :
    ∃ x ∈ mine, seatOf x = t ∧ (x.1.l.get x.2).1 = sh := by
  obtain ⟨x, hx, hd⟩ := List.any_eq_true.1 h
  obtain ⟨a, b⟩ := Bool.and_eq_true_iff.1 hd
  exact ⟨x, hx, of_decide_eq_true a, of_decide_eq_true b⟩

/-- The three seats are apart. -/
def seatsApartB (V : OwnSeats) (t : ℕ × ℕ) : Bool :=
  decide (V.index ≠ V.w) && (decide (V.index ≠ t) && decide (V.w ≠ t))

theorem seatsApart_of {V : OwnSeats} {t : ℕ × ℕ} (h : seatsApartB V t = true) :
    V.index ≠ V.w ∧ V.index ≠ t ∧ V.w ≠ t := by
  obtain ⟨a, bc⟩ := Bool.and_eq_true_iff.1 h
  obtain ⟨b, c⟩ := Bool.and_eq_true_iff.1 bc
  exact ⟨of_decide_eq_true a, of_decide_eq_true b, of_decide_eq_true c⟩

/-- Every one of mine has one of the three seats. -/
def allSeatsB (mine : List Mem) (V : OwnSeats) (t : ℕ × ℕ) : Bool :=
  mine.all fun z => decide (seatOf z = V.index ∨ seatOf z = V.w ∨ seatOf z = t)

theorem allSeats_of {mine : List Mem} {V : OwnSeats} {t : ℕ × ℕ} (h : allSeatsB mine V t = true) :
    ∀ z ∈ mine, seatOf z = V.index ∨ seatOf z = V.w ∨ seatOf z = t :=
  fun z hz => of_decide_eq_true (List.all_eq_true.1 h z hz)

/-- The two elder seats lie in trees below t₁. -/
def elderBelowB (V : OwnSeats) (t₁ : ℕ) : Bool := decide (V.index.1 < t₁ ∧ V.w.1 < t₁)

theorem elderBelow_of {V : OwnSeats} {t₁ : ℕ} (h : elderBelowB V t₁ = true) :
    V.index.1 < t₁ ∧ V.w.1 < t₁ := of_decide_eq_true h

/-- Whoever of mine sits at t passes the test `oneTableB` (Johnson/ToldDescR/OneTableB.lean). -/
def oneTableAllB (cs : Codes) (mine : List Mem) (t : ℕ × ℕ) : Bool :=
  mine.all fun x => !decide (seatOf x = t) || ToldDesc.oneTableB cs (x.1.l.get x.2).1

theorem oneTableAll_of {cs : Codes} {mine : List Mem} {t : ℕ × ℕ}
    (h : oneTableAllB cs mine t = true) :
    ∀ x ∈ mine, seatOf x = t → ToldDesc.OneTable cs (x.1.l.get x.2).1 := by
  intro x hx e
  have hd := List.all_eq_true.1 h x hx
  rw [decide_eq_true e] at hd
  exact (ToldDesc.oneTable_iff _ _).1 (by simpa using hd)

/-- No two of mine have one number. -/
def nodupB (arr : ℕ → ℕ → ℕ) (mine : List Mem) : Bool := decide ((mine.map (numOf arr)).Nodup)

theorem nodup_of {arr : ℕ → ℕ → ℕ} {mine : List Mem} (h : nodupB arr mine = true) :
    (mine.map (numOf arr)).Nodup := of_decide_eq_true h

/-- Omega's tree lies below b. -/
def omegaB (Ns : NumbersS) (b : ℕ) : Bool := decide ((Ns.tenant .oOmega).1 < b)

theorem omega_of {Ns : NumbersS} {b : ℕ} (h : omegaB Ns b = true) : (Ns.tenant .oOmega).1 < b :=
  of_decide_eq_true h

/-- Every one of mine lies in a tree below the base. -/
def fenceB (base : ℕ) (mine : List Mem) : Bool :=
  mine.all fun x => decide ((x.1.seat x.2).1 < base)

theorem fence_of {base : ℕ} {mine : List Mem} (h : fenceB base mine = true) : Fenced base mine :=
  fun x hx => of_decide_eq_true (List.all_eq_true.1 h x hx)

end LLT25.PlanB

#print axioms LLT25.PlanB.some_of
#print axioms LLT25.PlanB.apart_of
#print axioms LLT25.PlanB.oneSeat_of
#print axioms LLT25.PlanB.omegaSeat_of
#print axioms LLT25.PlanB.mineAt_of
#print axioms LLT25.PlanB.seatsApart_of
#print axioms LLT25.PlanB.allSeats_of
#print axioms LLT25.PlanB.elderBelow_of
#print axioms LLT25.PlanB.oneTableAll_of
#print axioms LLT25.PlanB.nodup_of
#print axioms LLT25.PlanB.omega_of
#print axioms LLT25.PlanB.fence_of
