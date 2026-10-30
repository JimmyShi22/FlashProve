-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5T/RowsFitAt.lean: THE LETTER rw OF THE TABLE OF JOINTS' COMPOSED FILLING
(Johnson/Desc/Sound/MgAll.lean: rw : ℕ → First.S → Bool) AS A TERM WITH NO LETTER BUT Z, the proof
file's public part. Two definitions with code, two lemmas.

  `k9RowsAt Z m`: the rows of the batching round's entry at segment m, off the plan:
    `k9Where` at `k9Stretches Z` (Johnson/Desc/ProofFile/Lot/K9.lean).
  `rwAt Z m s`: **rw**: the test `K9.rowsFit` (Johnson/Desc/First/Batch/OwedLaid.lean:
    the plan's claims and the ties' and reads' indices are
    at most the round's rows) at that number.
  `rwAt_of_rows`, `rwAt_none`: what it is where the plan has such a round at m, and where not.
THE TERM THAT HAS RUN, BY READING: evaluations in DoorK9b.lean (not in this repository) :52-53, :57,
:62: rowsOf l := (k9Where (k9Stretches I.Z) l).map (·.rows); (rowsOf m).any fun r => rowsFit r s.

Limits. WHERE THE PLAN HAS NO BATCHING ROUND AT m, `rwAt` IS false. `K9.rowsFit` ITSELF SAYS YES
WHERE WHAT IT READS IS NOT IN THE VERIFIER's STATE (nothing of the smallness test, no list of
tables, no ledger): by Batch/OwedLaid.lean's own head: an idle yes there.
Nothing on soundness.

-/
import Johnson.Desc.ProofFile.Lot.K9
import Johnson.K9R.OwedLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open VerifiableInference.Desc.First (S)

/-- The rows of the batching round's entry at segment m, off the plan. -/
def k9RowsAt (Z : ProofFile.Pub) (m : Nat) : Option Nat :=
  (ProofFile.k9Where (ProofFile.k9Stretches Z) m).map (·.rows)

/-- **rw.** -/
def rwAt (Z : ProofFile.Pub) (m : Nat) (s : S) : Bool :=
  (k9RowsAt Z m).any fun r => VerifiableInference.Desc.K9.rowsFit r s

theorem rwAt_of_rows (Z : ProofFile.Pub) (m r : Nat) (h : k9RowsAt Z m = some r) (s : S) :
    rwAt Z m s = VerifiableInference.Desc.K9.rowsFit r s := by
  unfold rwAt
  rw [h]
  rfl

theorem rwAt_none (Z : ProofFile.Pub) (m : Nat) (h : k9RowsAt Z m = none) (s : S) :
    rwAt Z m s = false := by
  unfold rwAt
  rw [h]
  rfl

end P5T

#print axioms P5T.rwAt_of_rows
#print axioms P5T.rwAt_none
