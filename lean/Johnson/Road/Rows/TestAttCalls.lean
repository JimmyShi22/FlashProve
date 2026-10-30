-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/TestAttCalls.lean: the numbers of the lookup of an attention sub-proof, tried at
two configurations.

The tests run when this file is compiled. The program does not import this file.

What is tried. At the verifier's small configuration (64 tokens) and at its configuration of full
size (1,024 tokens; OnBytes/Model/TestAttentionShape.lean), with the shapes that shapeHid returns:
the record callsOf is the expected one (at full size the library's Calls.ref); the test callsFitB
says yes, so CallsFit holds (callsFit_of in Johnson/Road/Rows/AttCalls.lean); the verifier's first
trees are the library's.

The teeth. With a tree of half the depth the test says no at the small configuration.

What is not tested. Two configurations, one cap on the depth of a tree each.


-/
import Johnson.Road.Rows.AttCalls
import OnBytes.Model.TestAttentionShape
import OnBytes.Model.TestAttentionPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows.TestCalls

open OnBytes.Attention (shapeHid smallCfg)
open Inst.Model.AttSeg (Calls)

/-- The numbers of a record. -/
def nums (C : Calls) : List Nat × Nat × Nat := ((List.finRange 4).map C.a, C.Dk, C.sg)

-- the small configuration
#guard ((shapeHid 24 smallCfg).toOption.map fun x => nums (callsOf x.2)) ==
  some ([20, 20, 20, 20], 20, 2)
#guard ((shapeHid 24 smallCfg).toOption.map fun x => callsFitB x.1 x.2) == some true
#guard ((shapeHid 24 smallCfg).toOption.map fun x => decide (SameOrder x.2)) == some true
-- full size: the library's reference numbers
#guard ((shapeHid 25 Attention.Test.full).toOption.map fun x => nums (callsOf x.2)) ==
  some (nums Calls.ref)
#guard ((shapeHid 25 Attention.Test.full).toOption.map fun x => callsFitB x.1 x.2) == some true
#guard ((shapeHid 25 Attention.Test.full).toOption.map fun x => decide (SameOrder x.2)) ==
  some true
-- a tooth: a tree of half the depth
#guard ((shapeHid 24 smallCfg).toOption.map fun x => callsFitB x.1 { x.2 with dT := 10 }) ==
  some false

end OnBytes.Road.Rows.TestCalls
