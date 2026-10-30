-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanTables.lean: the handed radius of the rounds «LOC» on the stored tables, BOUNDED
FROM ABOVE AT THE PLANNER's OWN RECORDS OF THE TABLES: one test whose yes gives that the plans
outside the first chain's hold two entries «LOC», that each draws its positions in the length of its
table's code, and that the radius passes `Cb.Bridge.foldTest` (Johnson/Bridge/PointAtPlan.lean) at
both tables: by `Cb.Bridge.foldTest_sound` it is then below the Johnson radius. And the three tests
on the records as one. No numeral of a plan is written here.

Arithmetic: no statement on codes is used in this file's own proofs. Through its imports the file
stands above Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from
ArkLib and Mathlib (lean/LIMITS.md,
L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions with code, and statements that unfold them.

Main names:
  `planTables Z`: the records of the two stored tables, in the plans' order: the proof file's, the
    key file's.
  `planTablesB rT M`: THE TEST: as many entries «LOC» outside the first chain's plan as tables; each
    entry's length is its table's code's; `foldTest T rT rT` at each table.
  `planTablesB_two`, `planTablesB_fits`, `planTablesB_radius`: what its yes gives.
  `planAllB ρ rT M`: `planTestsB` (Johnson/Bridge/PlanTests.lean), `planLocB`
    (Johnson/Bridge/PlanLoc.lean) and `planTablesB`, at one rule and one radius. `planAllB_parts`.

Limits: THE RADIUS IS WHATEVER THE CALLER SAYS: no statement here ties it to a protocol, and it is
one number for both tables and for both radii of `foldTest`. A yes of `foldTest` says nothing on the
size of a count (the Limits of Johnson/Bridge/PointAtPlan.lean). WHICH ENTRY BELONGS TO WHICH TABLE
IS BY ORDER ALONE; an entry's draws are held against nothing here. That the records and plans are
those of a file's public files is asked where they are made. That the rounds of a plan are rounds of
the description of the protocol that a verifier runs is not said here. `planAllB` is these three and
no more: what a radius costs at the tables' own fold (`linPointTest`), the batching, the rounds
«SEND seed», the entry file's «LINK» are in none of them: it says yes up to the last radius below
the Johnson radius. The limits of the three files named hold of it. The tests have been EVALUATED at
stored sets of public files by a sheet that is not in this repository; no theorem says that they say
yes at any plan. No sum over rounds. Nothing on a verifier or a file.

-/
import Johnson.Bridge.PlanLoc
import Johnson.Bridge.PointAtPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Params

/-- The records of the two stored tables, in the plans' order. -/
def planTables (Z : Params.Sized) : List TableSize := [Z.proof.batch.table, Z.key.once.table]

/-- **The test on the tables' records, at a radius.** -/
def planTablesB (rT : ℕ) (M : Configured) : Bool :=
  Nat.beq (tableLocs M).length (planTables M.sized).length &&
    (((tableLocs M).zip (planTables M.sized)).all fun p => Nat.beq p.1.logN p.2.code.logN) &&
    ((planTables M.sized).all fun T => Cb.Bridge.foldTest T rT rT)

/-- **A yes of the test: the plans outside the first chain's hold two entries «LOC».** -/
theorem planTablesB_two {rT : ℕ} {M : Configured} (h : planTablesB rT M = true) :
    (tableLocs M).length = 2 :=
  Nat.eq_of_beq_eq_true (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1

/-- **A yes of the test: each entry draws its positions in the length of its table's code.** -/
theorem planTablesB_fits {rT : ℕ} {M : Configured} (h : planTablesB rT M = true) :
    ∀ p ∈ (tableLocs M).zip (planTables M.sized), p.1.logN = p.2.code.logN := fun p hp =>
  Nat.eq_of_beq_eq_true
    (List.all_eq_true.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).2 p hp)

/-- **A yes of the test: the radius passes `foldTest` at both tables.** -/
theorem planTablesB_radius {rT : ℕ} {M : Configured} (h : planTablesB rT M = true) :
    ∀ T ∈ planTables M.sized, Cb.Bridge.foldTest T rT rT = true :=
  List.all_eq_true.1 (Bool.and_eq_true_iff.1 h).2

/-- **The three tests on the records as one**, at one rule and one radius. -/
def planAllB (ρ : Rad) (rT : ℕ) (M : Configured) : Bool :=
  planTestsB ρ M && planLocB ρ rT M && planTablesB rT M

theorem planAllB_parts {ρ : Rad} {rT : ℕ} {M : Configured} (h : planAllB ρ rT M = true) :
    planTestsB ρ M = true ∧ planLocB ρ rT M = true ∧ planTablesB rT M = true :=
  ⟨(Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).1,
    (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).2, (Bool.and_eq_true_iff.1 h).2⟩

end Johnson.Bridge

#print axioms Johnson.Bridge.planTablesB_two
#print axioms Johnson.Bridge.planTablesB_fits
#print axioms Johnson.Bridge.planTablesB_radius
#print axioms Johnson.Bridge.planAllB_parts
