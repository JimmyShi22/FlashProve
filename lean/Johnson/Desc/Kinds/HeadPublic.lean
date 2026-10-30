-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/HeadPublic.lean: THE OUTPUT HEAD'S OWN ROUNDS (Head.lean): what is public, and
what the prover has committed to before these rounds. To be read first. Definitions only.
In Lean what is given stands in classes (Sizes, Policy, Request here), so that a formula names d, C
or r without arguments.
-/
import Johnson.Desc.Kinds.HeadNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open Norm (T S2)

/-! ## PUBLIC -/

/-- Beside the normalization's sizes (T = 2^lt positions; d features, 2^lPd with padding, in blocks
of S2): V vocabulary entries. 2^sh: the least cost; sh is 7 or 8. 2^F: the table's row 0; F = 24. -/
class Sizes extends FinalNorm.Sizes where (V sh F : Nat)
/-- The clip on a cost; the bound on the mean of the clipped costs; how many costs may exceed C. -/
class Policy where (C theta cap : Nat)
/-- The request: T tokens, and two positions: the stretch r <= t < e of it is under test. All that
is said of positions is a function of these and of the next token y. -/
class Request where (tok : Nat → Nat) (r e : Nat)
export Sizes (V sh F)
export Policy (C theta cap)
export Request (tok r e)
variable [Sizes] [Policy] [Request]

/-- V with padding to whole blocks. -/
def JV : Nat := (V + S2 - 1) / S2 * S2
/-- The table's keys are cut in two at this entry: half the least power of two that is >= JV. -/
def JVa : Nat := 2 ^ (clog2 JV - 1)
/-- Position t is checked. -/
def checked (t : Nat) : Bool := r ≤ t && t < e
/-- Position t has a cost. -/
def costed (t : Nat) : Bool := checked t && t + 1 < T
/-- The number of positions with a cost. -/
def RC : Nat := min e (T - 1) - r

/-! ## COMMITTED before these rounds. None of it is sent in the clear -/

/-- The matrices of cells that the head's own claims read. A matrix has a column of T cells for each
of its features. A cell is meant to be a signed byte, and a number takes several limbs at the radix
256; what the range check shows is only that a cell is below 2^18.
wide: 4 d features of the normalization's; then for each vocabulary entry the margin's middle digit
(two limbs), its low digit, and the middle digit's table value (three limbs).
act: the normalization's output, two limbs a feature.
row: for each position the normalization's 99 digits, then the 21 digits of six numbers. -/
inductive Matrix | wide | act | row

/-- The six hidden numbers of a position with a cost. All are at least 0, because each digit is a
byte: that is meant to be shown by the normalization's key digits (HeadNorm.lean), which runs over
these 21 too.
paid: what the prover sets against the cost, where that is at most C.
over: ONE DIGIT, 0 .. 255, not a bit: it lifts every margin by BIG over, and is charged C over.
slackMean fills the sum (a) up to theta RC. slackClip is C - paid. slackCap fills the count (b) up
to cap. slackTable is 2^F less the sum of the position's V table values.
The claims enforce inequalities alone: any paid from the cost up to C passes, and so does over > 0
at a cheap position; each only costs the prover more. -/
inductive Number | paid | over | slackMean | slackClip | slackCap | slackTable
/-- A number's first digit behind the normalization's 99, and how many digits it has. -/
def Number.digits : Number → Nat × Nat
  | .paid => (0, 5) | .over => (5, 1) | .slackMean => (6, 5) | .slackClip => (11, 5)
  | .slackCap => (16, 2) | .slackTable => (18, 3)

end VerifiableInference.Desc.Kinds.Head
