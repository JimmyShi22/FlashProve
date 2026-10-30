-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/RoundSizes.lean: the sizes that the planner needs of a lookup and of a smallness
test.

The plan of a request's chain is made in OnBytes/Params/. For the rounds of a sub-proof it needs a
few numbers of the sub-proof's lookups and of its smallness test. This file reads them off the
records of OnBytes/Model/Forest.lean and OnBytes/Model/Tail.lean. It is a separate file so that
Forest.lean and Tail.lean need not import the planner. Lookup and smallness test are explained at
the head of OnBytes/Model/Frame.lean.

What this file does not claim. No theorem is stated here.
-/
import OnBytes.Model.Forest
import OnBytes.Model.Tail
import OnBytes.Params.SubRounds

namespace OnBytes.Model

/-- What the planner needs of a lookup (Forest.Shape): v, the bits of a key's index (2^v keys); d,
the bits of a table row's index (2^d rows); shifted, true if the lookup serves more than one
call. -/
def forestSize (h : Forest.Shape) : Params.ForestSize :=
  { v := h.v, d := h.d, shifted := decide (1 < h.NC) }

/-- What the planner needs of a smallness test (HTailF2): the columns of all its matrices together,
the number tau of random combinations, and the sizes of the lookup that checks the digits. -/
def smallSize (tl : HTailF2) : Params.SmallSize :=
  { columns := tl.foldColumns, tau := tl.tau, digits := forestSize tl.f9 }

end OnBytes.Model
