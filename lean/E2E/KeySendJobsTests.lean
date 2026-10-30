-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/KeySendJobsTests.lean: tests of the three jobs of E2E/KeySendJobs.lean at the written sizes of
the key (`keyFull`, Johnson/Goal/PlanValues/KeySizedReturns.lean). Each is run by Lean's evaluator
when the file compiles (`#guard`). No theorem.

What is tested. The part's own public test `sendFits` accepts each job, with a fold's fresh table of
4 rounds and 2^4 rows beside the multiplicities and one of 5 rounds and 2^1 rows beside W; with
another number of rows both are rejected. The counts of coins (`dueR`) at these numbers. THE NUMBERS
OF ROUNDS 4 AND 5 ARE LAID BY THE TEST ITSELF, and `dueR` is reckoned from them: the counts do not
hold them against the plan (that is done in E2E/KeyBookHeldK1Jobs.lean, in the kernel). The three
counts 305, 38098 and 512 elements of the extension field were reckoned from the book of coins,
apart from this file, and were laid in here before the evaluation. The index-mask message has no
main row.

Limits. `sendFits` and `dueR` read the codes, the shapes and the fresh tables' numbers alone. THE
PLACES' NUMBERS (N), THE FIRST MESSAGES' NUMBERS AND THE THREE ROUNDS OF `BattAt` ARE SYNTHETIC
HERE: no test reads them. Nothing is played at this size. Nothing on hiding follows from this file.


-/
import E2E.KeySendJobs
import Johnson.Goal.PlanValues.KeySizedReturns

set_option autoImplicit false

namespace AtPublicFiles.Key
open OnBytes OnBytes.Params
open ProofFile.Honest.K1 (SendJob Ride sendFits dueR)
open VerifiableInference.Desc.Key (Pieces)

namespace Tests
open Lk6.AtPlan (keyFull)

/-- The one-time chain's public values at the written sizes. Of the parameter bytes' own fields the
jobs read the plan's number of answers to an OOD sample alone: the written settings'; all else of
them is empty here. -/
def one : OneTime :=
  { given := { bytes := ByteArray.empty, cfg := ByteArray.empty, items := []
               plan := { field := Fmt.Fld.two, salt := 0, nonce := 0, posB := 0
                         samples := keyFull.set.samples, saved := 1, entries := [] } }
    indexMasks := keyFull.once.input, ranges := keyFull.ranges.x
    binding := default, codes := keyFull.codes, lin := keyFull.once.shape }

def N : Pieces := ⟨0, 1, 5, 6, 7⟩
def rideMsg (k h : Nat) : Nat → Option Ride := fun i => if i == 1 then some ⟨k, h⟩ else none

#guard sendFits (idxJob (W := Unit) (X := Unit) one N [[]] 0).P fun _ => none
#guard sendFits (msgJob (W := Unit) (X := Unit) (fun _ _ _ => 0) one N [[], []] 1 (rideMsg 4 4)).P
  (rideMsg 4 4)
#guard ((wJob (W := Unit) (X := Unit) (fun _ _ _ => 0) one N [[], []] 9 (rideMsg 5 1)
  (fun _ _ _ => []) ⟨0, 1, 2⟩).map fun J => sendFits J.P (rideMsg 5 1)) == some true
-- a fresh table of other numbers is rejected
#guard !sendFits (msgJob (W := Unit) (X := Unit) (fun _ _ _ => 0) one N [[], []] 1 (rideMsg 4 3)).P
  (rideMsg 4 3)
#guard ((wJob (W := Unit) (X := Unit) (fun _ _ _ => 0) one N [[], []] 9 (rideMsg 5 2)
  (fun _ _ _ => []) ⟨0, 1, 2⟩).map fun J => sendFits J.P (rideMsg 5 2)) == some false

/-- The three jobs with the fresh tables' numbers (k, h) beside the multiplicities and beside W. -/
def jobs (a b : Nat × Nat) : List (SendJob Unit Unit) :=
  [idxJob one N [[]] 0, msgJob (fun _ _ _ => 0) one N [[], []] 1 (rideMsg a.1 a.2)] ++
    (wJob (fun _ _ _ => 0) one N [[], []] 9 (rideMsg b.1 b.2) (fun _ _ _ => []) ⟨0, 1, 2⟩).toList

-- the counts of coins, by field
#guard (jobs (4, 4) (5, 1)).map (fun J => dueR J.P J.ride) == [⟨0, 305⟩, ⟨98, 38098⟩, ⟨0, 512⟩]
-- one round more in a fresh table: two coins more, though the public test still accepts
#guard (jobs (5, 4) (6, 1)).map (fun J => dueR J.P J.ride) == [⟨0, 305⟩, ⟨98, 38100⟩, ⟨0, 514⟩]
#guard (jobs (5, 4) (6, 1)).all fun J => sendFits J.P J.ride
-- the index-mask message has no main row
#guard one.indexMasks.shape.mainRows == 0

end Tests

end AtPublicFiles.Key
