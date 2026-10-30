-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/VerifyHiding.lean: the range checks of one request.

Every sub-proof has a smallness test (OnBytes/Model/Tail.lean). For each of its matrices of
whole numbers the prover commits to random combinations of the cells of every row, and a lookup
tests that each combination lies in a fixed range. An honest prover fails such a range check with a
small chance. The programs admit public files only if a bound on that chance lies below a target
(OnBytes/Params/Gate.lean; in the C++, blocks/frame/hiding_conditions.h). The bound needs the sizes
of all range checks of a request. This file lists them from the sub-proofs' plans, as the C++
verifier does near the end of its routine buildLinksH (verifier/src/vf_segments.inc).

Main definitions: `cellBound`, `rangeCheckOf`, `rangeChecksH`.
What is not claimed: no theorem is stated here. The list says nothing by itself about what a proof
shows or hides. It is one input of the conditions in OnBytes/Params/Gate.lean.
-/
import OnBytes.Model.Tail
import OnBytes.Params.Gate

namespace OnBytes.Model

/-- The bound on a cell that the C++ verifier puts into each range check. In the C++ a cell of a
matrix of a smallness test is a signed byte, -128 to 127, so its absolute value is below this
number. Nothing in this file tests that. -/
def cellBound : Nat := 129

/-- The range check of one matrix. tau: the number of random combinations of each row. A
combination must lie from -2^lbz to 2^lbz - 1. The prover adds 2^lbz to it and commits to the sum
as a low digit of t2D0 bits and a high digit of t2D1 bits. -/
def rangeCheckOf (tau : Nat) (M : TMat) : Params.RangeCheck where
  rows := M.m
  columns := M.k
  combinations := tau
  bound := cellBound
  range := 2 ^ lbz
  digitBits := (t2D0, t2D1)

/-- The range checks of one request. Each sub-proof is one link of the proof's first chain. There
is one range check for each matrix of each link's smallness test, in the order of the links. The
matrices that a link reads from an earlier link are among them. tails: the closing part of each
link's sub-proof. Each check takes its number of combinations from its own link's closing part,
which draws and folds with the same number. The C++ uses one number, TAU, for all links of a
run. -/
def rangeChecksH (tails : List HTailF2) : List Params.RangeCheck :=
  tails.flatMap fun tl => tl.mats.toList.map (rangeCheckOf tl.tau)

end OnBytes.Model
