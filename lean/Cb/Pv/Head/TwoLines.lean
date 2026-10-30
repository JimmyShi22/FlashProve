-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Head/TwoLines.lean: the two clauses of the acceptance policy on a position's cost, as a family
of two vectors over the positions, with the statement before and the statement after the point at
which the verifier tests them.

The output head's verifier tests two clauses on the hidden numbers of each counted position, dB4
(c + k = C) and dZ (zs and the looked-up values add up to 2^24; Inst/Model/Head/Trace.lean), at one
point only: the last coordinates of the point that its lookup has drawn. No round of its own is run
for them.

linesFam t y: the two vectors. t: the cells. y: what the head reads of the request; the public mark
of the counted positions lies inside both clauses. LinesAll t y lt: both vectors are 0 at every
position below 2^lt: what stands before the lookup. LinesAtPt t y lt u: the extensions of both over
lt coordinates are 0 at the point u: what the verifier's two claims say; coordinate 0 of u belongs
to the top bit of a position. TwoLinesAt t y lt u: the second gives the first, at this point.

Limits. These are statements, not theorems. TwoLinesAt is a statement at one point and no law for
all points: it is false for some cells and points. What makes that rare is that the cells are fixed
before the point is drawn: that order is not said here, and no count of the bad points is.


-/
import Inst.Model.Head.Trace
import Blocks.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Head
open Inst.Model.Head

variable {K : Type} [Field K]

/-- The two clauses on a position's cost, as vectors over the positions. -/
def linesFam (t : Cells K) (y : Req) (i : Fin 2) (a : ℕ) : K :=
  if i = 0 then dB4 t y a else dZ t y a

/-- Both are 0 at every position below 2^lt. -/
def LinesAll (t : Cells K) (y : Req) (lt : ℕ) : Prop :=
  ∀ i, ∀ a < 2 ^ lt, linesFam t y i a = 0

/-- The extensions of both are 0 at the point u. -/
def LinesAtPt (t : Cells K) (y : Req) (lt : ℕ) (u : ℕ → K) : Prop :=
  ∀ i, Blocks.ext lt (linesFam t y i) u = 0

/-- From one point to all positions, at this point. -/
def TwoLinesAt (t : Cells K) (y : Req) (lt : ℕ) (u : ℕ → K) : Prop :=
  LinesAtPt t y lt u → LinesAll t y lt

end Cb.Pv.Head
