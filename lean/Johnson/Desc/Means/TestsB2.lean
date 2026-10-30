-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/TestsB2.lean: the three invariants on a statement, as tests that can be run.

Definitions with code alone; this file stands over Johnson/Desc/Means/TestsB.lean and
OnBytes/Iop/Ground.lean, so that a run can call it at any statement that a chain passes through.
That each test gives its invariant is shown in Johnson/Desc/Means/TestsLaw2.lean.

Main definitions: inOrderB, openKindsB, noneYetB, tidyB.

What is not claimed. Nothing is proved here.

-/
import Johnson.Desc.Means.TestsB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

/-- Every group is in order, every open row passes the tests of the adding at its group, and every
sample row is on its own oracle message. -/
def inOrderB (S : Statement) : Bool :=
  (S.groups.toList.all fun G => groupOkB S G && G.rows.toList.all (rowInB S G)) &&
  ((List.range S.oracles.size).all fun o =>
    match S.oracles[o]? with
    | some x => x.sampleRows.toList.all (rowInB S { code := 0, members := #[o] })
    | none => true)

/-- No open row is marked as a sample row. -/
def openKindsB (S : Statement) : Bool :=
  S.groups.toList.all fun G => G.rows.toList.all fun r => r.kind != .sample

/-- An oracle message that is not marked as sampled has no sample row. -/
def noneYetB (S : Statement) : Bool :=
  S.oracles.toList.all fun x => x.sampled || x.sampleRows.isEmpty

/-- All three. -/
def tidyB (S : Statement) : Bool := inOrderB S && openKindsB S && noneYetB S

end OnBytes.Means
