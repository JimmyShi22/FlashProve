-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Bind/TwinBudget.lean: at the full size's shape the committer that runs, as a deterministic
algorithm, stays within the goals' budget of queries for an honest party.

`fullShape` is the shape (32, 402653184, 44040191, 11, 1, 40), meant as that of the full-size
example's first table. The six numbers are typed here; one test holds them against another typed
Lean term, not against the parameter file: the table of `OnBytes.Params.recordLink`
(OnBytes/Params/EntryStagesRecord.lean; "the one shape of the first table and of all copies",
OnBytes/Params/Items.lean), which is typed for the full-size parameter file. The same numbers are
public in Ladder/Stored.lean's spelling of the full-size example's parameter file: its lines
"table 11 32 402653184 44040191 0 18", "answers 1", "record 1" and "salt 40".
Main theorems: `calls_full_35`: 2 · `calls fullShape` ≤ 2^35. `queryBound_twinID_full`: at all
public files and every table `twinID fullShape` makes at most `VerifierAndGoals.honestBudget` queries.
Limits. A count of queries alone.

-/
import Johnson.Bind.TwinAlgorithm
import Johnson.Top.Seam.ReaderWith
import Ladder
import OnBytes.Params.EntryStagesRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bind.Twin

open VerifiableInference

/-- The full size's shape, meant as that of the full-size example's first table: the test below. -/
def fullShape : Shape := ⟨32, 402653184, 44040191, 11, 1, 40⟩

#guard
  let t := OnBytes.Params.recordLink.table
  fullShape == ⟨t.code.logN, t.code.ell, t.code.r, t.v, t.answers, t.saltBytes⟩

theorem cube_full_le : fullShape.cube ≤ 29 := by
  have h : Nat.log2 (402653184 - 1) < 29 := (Nat.log2_lt (by decide)).2 (by decide)
  show (if (402653184 : Nat) ≤ 1 then 0 else Nat.log2 (402653184 - 1) + 1) ≤ 29
  rw [if_neg (by decide)]
  omega

theorem seedCalls_eq (S : Shape) :
    seedCalls S = 1 + (1 + (S.s * (S.cube * 18 + 36) + 3) / 4 + 1) / 2 := rfl

/-- A bound on the calls at every shape with at most 2^32 leaves, points of at most 29 coordinates
and one answer a row. -/
theorem calls_le_of (S : Shape) (ha : S.a ≤ 32) (hc : S.cube ≤ 29) (hs : S.s = 1) :
    calls S * 2 ≤ 2 ^ 35 := by
  have h1 := calls_le S
  have h2 : 2 ^ (S.a + 1) ≤ 2 ^ 33 := Nat.pow_le_pow_right (by decide) (by omega)
  have h3 := seedCalls_eq S
  rw [hs] at h3
  generalize seedCalls S = q at h1 h3
  generalize calls S = n at h1 ⊢
  generalize 2 ^ (S.a + 1) = w at h1 h2
  generalize S.cube = c at hc h3
  omega

theorem a_full : fullShape.a ≤ 32 := Nat.le_refl 32

theorem s_full : fullShape.s = 1 := rfl

/- From here on Lean does not open the shape's numbers: a term at 2^32 leaves is not to be unfolded.
-/
attribute [local irreducible] fullShape

theorem calls_full_35 : calls fullShape * 2 ≤ 2 ^ 35 :=
  calls_le_of fullShape a_full cube_full_le s_full

theorem calls_full : calls fullShape * 2 ≤ 2 ^ 48 :=
  Nat.le_trans calls_full_35 (Nat.pow_le_pow_right (by decide) (by decide))

theorem calls_full_budget : calls fullShape * 2 ≤ VerifierAndGoals.honestBudget := by
  unfold VerifierAndGoals.honestBudget
  exact calls_full

/-- Where 2 · `calls S` is at most B, the committer makes at most B queries. -/
theorem queryBound_twinID_of (S : Shape) (B : Nat) (hB : calls S * 2 ≤ B) (pol lay KL : ByteArray)
    (T : Table) : (twinID S pol lay KL T).toRandomized.QueryBound B :=
  queryBound_mono_det _ _ _ hB (queryBound_twinID S pol lay KL T)

/-- **At the full size's shape the committer stays within the honest budget.** -/
theorem queryBound_twinID_full (pol lay KL : ByteArray) (T : Table) :
    (twinID fullShape pol lay KL T).toRandomized.QueryBound VerifierAndGoals.honestBudget :=
  queryBound_twinID_of fullShape VerifierAndGoals.honestBudget calls_full_budget pol lay KL T

end Bind.Twin

#print axioms Bind.Twin.cube_full_le
#print axioms Bind.Twin.calls_le_of
#print axioms Bind.Twin.a_full
#print axioms Bind.Twin.s_full
#print axioms Bind.Twin.calls_full_35
#print axioms Bind.Twin.seedCalls_eq
#print axioms Bind.Twin.calls_full
#print axioms Bind.Twin.calls_full_budget
#print axioms Bind.Twin.queryBound_twinID_of
#print axioms Bind.Twin.queryBound_twinID_full
