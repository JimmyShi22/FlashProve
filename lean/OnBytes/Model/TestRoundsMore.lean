-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestRoundsMore.lean: further tests of OnBytes/Model/Frame.lean and
OnBytes/Model/Rounds.lean, which run when this file is compiled.

They check constants, try bounds from both sides, and break conditions that
OnBytes/Model/TestFrame.lean leaves unbroken. The last part checks under which name a faulty block
fails in the dry run.

What this file does not claim. The expected values are constants and conditions of the C++ source
(verifier/src/vf_common.h: LBZ, LBZW, LIDB_SEALED, LIDB_MAX, NMINH_MAX, WORK_BITS_MOST, tauServed,
eqOne; vf_transcript_channel.h; vf_sumcheck_receive.h; blocks/chain/rounds.h, by which a round's
numbers of elements, positions and matrix entries are those of the plan). No C++ program was run. In
the last part the name internal-batching-bare is the C++ verifier's. The words refused and plan are
this library's own (OnBytes/Iop/Ground.lean): refused stands for a condition without a name, here
one of Rounds.lean, and plan for a condition of the channel. Which of the two a fault must meet was
read off closeAs, Blk.close and Blk.dryRunNamed. No program imports this file.
-/
import OnBytes.Model.TestFrame

namespace OnBytes.Model.TestRoundsMore

open OnBytes.Model.TestFrame

/-! ## Frame -/

#guard lbz == 17 && lbzw == 20 && lidbSealed == 22 && lidbMost == 30 && nminHMost == 28
#guard workMost == 32
-- eqOne: the point has at most 63 coordinates, and the index is below 2 to the number of them
#guard eqIndexOK (Array.replicate 63 oneE) 0 && !eqIndexOK (Array.replicate 64 oneE) 0
#guard eqIndexOK #[oneE, oneE] 3 && !eqIndexOK #[oneE, oneE] 4
-- the values that the parameter file's line tau may have
#guard (List.range 600).filter tauServed == [32, 64, 96, 128, 160, 192, 256]
-- the largest 32 * 2^i that is at most tau
#guard tauFirst 8 63 32 == 32 && tauFirst 8 64 32 == 64 && tauFirst 8 96 32 == 64
#guard tauFirst 8 127 32 == 64 && tauFirst 8 128 32 == 128 && tauFirst 8 256 32 == 256
-- integers as elements of the base field: p - 1 for -1, 0 for 0, p and -p
#guard fOfInt 0 == 0 && fOfInt 1 == 1 && fOfInt (-1) == 18446744069414584320
#guard fOfInt 18446744069414584321 == 0 && fOfInt (-18446744069414584321) == 0

/-! ## Rounds -/

-- a matrix with no combination
#guard fails (trTrits 5 0) [{ name := "RNG", trits := 0 }]
-- a round of the plan that also draws positions
#guard fails (trAnswer .line) [{ name := "LINE", drawE := 1, poss := 1, logN := 4 }]
-- trAnswerNotZero does not take the round that combines rows
#guard fails (trAnswerNotZero .batSigma)
  [{ name := "BAT-sigma", drawE := 1, drawNZ := 1, rows := 0 }]
-- the degree of a round of the forms nodes and eq is 1 to 64
#guard [RoundForm.nodes, .eq].all fun f =>
  !f.degreeOK 0 && f.degreeOK 1 && f.degreeOK 64 && !f.degreeOK 65
#guard [RoundForm.eq2, .sum2, .sum3].all fun f => f.degreeOK 0 && f.degreeOK 65

/-! ## Under which name a faulty block fails -/

/-- The name under which the block fails in the dry run on the given entries; none if the dry run
goes through. -/
def failsAs {α : Type} (b : Blk α) (entries : List Fmt.Entry) : Option String :=
  match b.dryRunNamed { entries := entries, st := {} } with
  | .error e => some e.name
  | .ok _ => none

/-- The plan of a chain with the one round that combines rows, which counts none. -/
def noRows : List Fmt.Entry := [{ name := "BAT-sigma", drawE := 1, rows := 0 }]

#guard failsAs (trBatch 3) threeRows == none
#guard failsAs (trAnswer .line) [{ name := "LINE", drawE := 1 }] == none
-- the round that combines rows: no row; a plain draw
#guard failsAs (trBatch 0) noRows == some "internal-batching-bare"
#guard failsAs (trAnswer .batSigma) noRows == some "internal-batching-bare"
#guard failsAs (trPoint .batSigma 1) noRows == some "internal-batching-bare"
#guard failsAs (trAnswerNotZero .batSigma)
  [{ name := "BAT-sigma", drawE := 1, drawNZ := 1, rows := 0 }] == some "internal-batching-bare"
-- conditions of closeAs and trTrits: the kind, the numbers of elements, entries and positions
#guard failsAs (trEmpty .line) [{ name := "LINE" }] == some "refused"
#guard failsAs (trAnswer .line) [{ name := "LINE", drawE := 2 }] == some "refused"
#guard failsAs (trPoint .zero 3) [{ name := "ZERO", drawE := 2 }] == some "refused"
#guard failsAs (trTrits 2 3) [{ name := "RNG", trits := 5 }] == some "refused"
#guard failsAs (trTrits 5 0) [{ name := "RNG", trits := 0 }] == some "refused"
#guard failsAs (trAnswer .line) [{ name := "LINE", drawE := 1, poss := 1, logN := 4 }] ==
  some "refused"
-- conditions of the channel: the name, the rule on 0, rows that were never stated, what is left
#guard failsAs (trAnswer .line) [{ name := "ZERO", drawE := 1 }] == some "plan"
#guard failsAs (trAnswer .pscY) [{ name := "PSC Y", drawE := 1, drawNZ := 1 }] == some "plan"
#guard failsAs (trAnswerNotZero .pscY) [{ name := "PSC Y", drawE := 1 }] == some "plan"
#guard failsAs trBatchOpen threeRows == some "plan"
#guard failsAs (do let _ ← trBatchOpen; trAnswer .line)
  (threeRows ++ [{ name := "LINE", drawE := 1 }]) == some "plan"
#guard failsAs (trRead 1) [] == some "plan"
#guard failsAs (trAnswer .line) [{ name := "LINE", drawE := 1 }, { name := "LINE", drawE := 1 }] ==
  some "plan"

end OnBytes.Model.TestRoundsMore
