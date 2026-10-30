-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4RowTestBends.lean: THE TOOLS OF THE NEGATIVE TESTS OF THE PROPOSED ROW k4RowB
(Johnson/Road/K4/K4RowTest.lean): FOUR BENDS OF THE PUBLIC PARAMETERS, one thing turned each.
DEFINITIONS ALONE: four. ON THE LAWS' SIDE: NOTHING THAT THE VERIFIER RUNS IMPORTS THIS FILE.

  `bendShort`: the last group's entry is taken away · `bendClaims`: the first group's number of
  claims on the weights is one more · `bendReads`: the first group's list of the vectors' arrays is
  empty · `bendLimb`: the tensor of the stream has one limb more.
WHO HOLDS WHAT: bendClaims, bendReads: laws (Johnson/Road/K4/K4RowTestLaws.lean) · bendShort,
bendLimb: the evaluator alone.
Limits. Nothing on soundness.


-/
import Johnson.Road.K4.K4RowTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model

/-- A bend: the last group's entry is taken away. -/
def bendShort (X : Verify.Public) : Verify.Public := { X with G := X.G.pop }

/-- A bend: the first group's number of claims on the weights is one more. -/
def bendClaims (X : Verify.Public) : Verify.Public :=
  { X with G := X.G.modify 0 fun hp => { hp with NCL := hp.NCL + 1 } }

/-- A bend: the first group's list of the vectors' arrays is empty. -/
def bendReads (X : Verify.Public) : Verify.Public :=
  { X with G := X.G.modify 0 fun hp =>
      { hp with tl := { hp.tl with ix := { hp.tl.ix with U := #[] } } } }

/-- A bend: the tensor of the stream has one limb more. -/
def bendLimb (X : Verify.Public) : Verify.Public :=
  { X with layers := { X.layers with
      y := { X.layers.y with xb := { X.layers.y.xb with nl := X.layers.y.xb.nl + 1 } } } }

end OnBytes.Road.K4
