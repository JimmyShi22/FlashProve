-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsBelowWritten.lean: the test `sampledBelow`
(Johnson/Desc/Sound/ReadsBelowAt.lean: every sampled tenant whose pin is open at the first table's
last border sits in a tree below lo) at the written values of the full size: it accepts at 83, it
rejects at 82, and it is not idle there. A definition and statements with their proofs.

Who asks the test. It is the premise h of `ocEnd_readsBelow_sig`
(Johnson/Desc/Sound/ReadsBelowAt.lean), and the first of the three named tests `testsO`, there under
the name "hbelow" (Johnson/Desc/K14/Law/SharedConstTests.lean): whence the names here.

The arguments, each with its written term and what ties it:
  lo · 83, the number of the first chain's trees (`roots_all`, Johnson/P5T/PlanSeatsFull.lean) · no
    tie: lo is a parameter of the law that asks the test; whoever calls that law says at which
    number.
  N₁ · `N0Full`, the core of the numbers · the tie is named here, not made: `seats_in_scope`
    (Johnson/P5T/PlanSeatsTie.lean: in the goals' scope, under its premises, the numbers of the
    plan's seats are `N0Full`) and `atBlocks_seats` (Johnson/Desc/First/NumbersAtBlocks.lean:
    `N.atBlocks` keeps the four fields) would give the four premises of `hbelow_at`; neither file is
    among this file's three imports, and no statement here brings them together · the test reads
    four fields alone, all the core's: `sampledBelow_core`.
  the segments and the places · `linksFull` (Johnson/Desc/Sound/AtDriver.lean) and `flatPlaces` of
    it: closed constants; whether the law's own list of segments is that constant is for whoever
    calls the law.

  `openLastFull`: what is open at the last border. `sampledBelow_core`.
  `hbelow_open`: it is not idle: there are 358 places, and the sampled tenants that are open at the
    last border are (1, 0), the index masks' message's, and (82, 0), W's. That this list is not
    empty also shows that the border is there: beyond the end `openLastFull` would be empty.
  `hbelow_written`: the test accepts at 83. `hbelow_rejects`: the negative test: at 82 it rejects.
  `hbelow_at`: at any numbers whose four fields are the core's.
By evaluations in Lean's kernel (`decide +kernel`): `hbelow_open`, `hbelow_written`,
`hbelow_rejects`. The counts that make these say something: `psFull_whole`, `psFull_roles`
(Johnson/P5T/PlanSeatsFull.lean).

Limits. Nothing here ties lo to 83, N₁ to `N0Full` or a law's list of segments to `linksFull`: these
are facts at written values, and no law is called. The accept by itself is no news: `hbelow_of`
(Johnson/Desc/AtSeats/TestsOAtPlan.lean) proves it at every lawful list of segments from two
comparisons, and `linksFull` is such a list (`linksOk_full`, same file). Nor is it news that the
test is not idle: `endTests_all` (Johnson/Desc/K13/Law/EndTestsAll.lean) has W's and the index
masks' tenants among the sampled at every such list. What is added here is the evaluation: the
sampled list whole, and the reject. The full size alone. Nothing on soundness.
-/
import Johnson.Desc.Sound.ReadsBelowAt
import Johnson.Desc.Sound.AtDriver
import Johnson.P5T.PlanSeatsFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (Item Numbers start openSets sampledIn flatPlaces)
open P5T (N0Full)

/-- What is open at the first table's last border, at the full size's list of segments. -/
def openLastFull : List Item :=
  (openSets linksFull (flatPlaces true linksFull true) (start linksFull))[
    (flatPlaces true linksFull true).length]?.getD []

/-- The test reads four fields of the numbers alone. -/
theorem sampledBelow_core {N N' : Numbers} (h1 : N.sent = N'.sent) (h2 : N.keptOf = N'.keptOf)
    (h3 : N.index = N'.index) (h4 : N.w = N'.w) (lo : ℕ) (O : List Item) :
    sampledBelow lo N O = sampledBelow lo N' O := by
  unfold sampledBelow sampledIn
  rw [h1, h2, h3, h4]

/-- **It is not idle**: the border is there, and the sampled tenants whose pin is open at it are
the index masks' message's and W's. -/
theorem hbelow_open :
    ((flatPlaces true linksFull true).length, sampledIn N0Full openLastFull) =
      (358, [(1, 0), (82, 0)]) := by decide +kernel

/-- At the written values the test accepts, at the number of the first chain's trees. -/
theorem hbelow_written : sampledBelow 83 N0Full openLastFull = true := by decide +kernel

/-- The negative test: one lower it rejects: W sits in tree 82. -/
theorem hbelow_rejects : sampledBelow 82 N0Full openLastFull = false := by decide +kernel

/-- At any numbers whose four fields are the core's. -/
theorem hbelow_at {N : Numbers} (h1 : N.sent = N0Full.sent) (h2 : N.keptOf = N0Full.keptOf)
    (h3 : N.index = N0Full.index) (h4 : N.w = N0Full.w) :
    sampledBelow 83 N openLastFull = true :=
  (sampledBelow_core h1 h2 h3 h4 83 openLastFull).trans hbelow_written

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.sampledBelow_core
#print axioms VerifiableInference.Desc.Sound.hbelow_open
#print axioms VerifiableInference.Desc.Sound.hbelow_written
#print axioms VerifiableInference.Desc.Sound.hbelow_rejects
#print axioms VerifiableInference.Desc.Sound.hbelow_at
