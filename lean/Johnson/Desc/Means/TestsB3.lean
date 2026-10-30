-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/TestsB3.lean: three invariants more on a statement, and the test for the end, as
tests that can be run.

Definitions with code alone; this file stands over OnBytes/Iop/Ground.lean alone, so that a run can
call it at any statement that a chain passes through. That each test gives its invariant is shown in
Johnson/Desc/Means/TestsLaw3.lean.

Main definitions: sampledMembersB, linkedB, markedEmptyB, allTestedB.

What is not claimed. Nothing is proved here.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- Every member of a group is an oracle message that is there and is marked as sampled. -/
def sampledMembersB (S : Statement) : Bool :=
  S.groups.toList.all fun G => G.members.toList.all fun o =>
    match S.oracles[o]? with
    | some x => x.sampled
    | none => false

/-- An oracle message that notes a group is a member of it. -/
def linkedB (S : Statement) : Bool :=
  (List.range S.oracles.size).all fun o =>
    match S.oracles[o]? with
    | some x => x.groups.all fun g =>
        match S.groups[g]? with
        | some G => G.members.contains o
        | none => false
    | none => true

/-- A group whose test has begun holds no open row. -/
def markedEmptyB (S : Statement) : Bool :=
  S.groups.toList.all fun G => !G.inRun || G.rows.isEmpty

/-- The test for the end of a protocol, in its own words. -/
def allTestedB (S : Statement) : Bool :=
  S.groups.all (·.inRun) && S.oracles.all fun x => !x.sampled || !x.groups.isEmpty

end OnBytes.Means
