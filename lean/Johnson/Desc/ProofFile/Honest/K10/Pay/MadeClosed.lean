-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeClosed.lean: closed facts at the written plan of the full size on the rows of the
closing of a segment (K10), by Lean's kernel: no state, no prover.

  `duesW`           the counts of the runs that the part at segment l carries, at the written shape and codes
  `rowsTest`, `rows_written`   at each of the 25 segments the test `groupS` on shapes and counts says yes, and its members
                    are the written list's members, with their shapes and marks "kept", in that order
  `segs_written`    at each of the 25 segments two public tests of the job say yes: the codes, and the count of runs
  `last_written`    each of the 25 segments is there, with the written codes and the written code numbers, whose message
                    lengths are powers of two
  `rising_written`  at each of the 25 links the numbers of the written list's members rise

Limits. Nothing here speaks of a run. The full size alone.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeShape
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.ProofFile.Honest.K10.BorneAt
import Johnson.Desc.ProofFile.Honest.K10.SegmentClosing
import Johnson.Desc.First.Close.Law.MaskAtFull
import Johnson.Desc.First.Close.Law.ReqKept
import Johnson.Desc.First.Close.Law.NoOfLink
import Johnson.Desc.ReqLit.Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open ProofFile.Honest.K2.Law (segsW)
open VerifiableInference.Desc.First.Close (kbAt noK10 seatsPlanW)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2 linksFullLit)

/-- The written counts of the runs that the part at segment l carries. -/
def duesW (l : Nat) : List Due := (borneOf shapeFull codesFull2 (fun _ _ => default) l).map (·.count)

/-- The written list's members at segment l, with their shapes and marks. -/
def membersW (l : Nat) : List (OnBytes.OracleShape × Bool) :=
  (VerifiableInference.Desc.First.Close.membersOf (linksFullLit.getD l [])).map fun i =>
    (((linksFullLit.getD l []).get i).1, kbAt shapeFull l (linksFullLit.getD l []) i)

/-- The test on the group's rows names the written members. -/
def rowsTest (l : Nat) : Bool :=
  match groupS (segsW.take (l + 1)) (duesW l) with
  | some ms => ms.map (fun m => (m.shape, m.kept)) == membersW l
  | none => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- So it is at each of the 25 segments. -/
theorem rows_written : ((List.range 25).all rowsTest) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- At each of the 25 segments the job's two public tests on numbers say yes. -/
theorem segs_written : ((List.range 25).all fun l =>
    segsKnown (segsW.take (l + 1)) && (duesW l).length == runsAsked (segsW.take (l + 1))) = true := by decide +kernel

/-- One segment's public numbers. -/
def lastTest (S : ProofFile.Honest.K2.SegmentPub) : Bool :=
  S.sizes.codes == codesFull2 && S.sizes.code == shapeFull.code && S.sizes.maskCode == shapeFull.maskCode &&
    OnBytes.powerOfTwo (codesFull2.base.getD shapeFull.code default).ell &&
    OnBytes.powerOfTwo (codesFull2.mask.getD shapeFull.maskCode default).ell

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- Each of the 25 segments is there, with the written numbers. -/
theorem last_written : ((List.range 25).all fun l => ((segsW.take (l + 1)).getLast?).any lastTest) = true := by
  decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- At each of the 25 links the numbers of the written list's members rise. -/
theorem rising_written : ((List.range 25).all fun l =>
    rising ((VerifiableInference.Desc.First.Close.membersOf (linksFullLit.getD l [])).map
      (noK10 seatsPlanW (linksFullLit.getD l []) P5T.psFull l))) = true := by decide +kernel

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.duesW
#print axioms ProofFile.Honest.K10.membersW
#print axioms ProofFile.Honest.K10.rowsTest
#print axioms ProofFile.Honest.K10.rows_written
#print axioms ProofFile.Honest.K10.segs_written
#print axioms ProofFile.Honest.K10.lastTest
#print axioms ProofFile.Honest.K10.last_written
#print axioms ProofFile.Honest.K10.rising_written
