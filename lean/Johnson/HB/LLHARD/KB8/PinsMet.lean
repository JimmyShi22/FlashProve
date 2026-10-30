-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB8/PinsMet.lean: An X made for the purpose: it comes of no public files. The
premises of `decl_full` and `r8'_of_lin` (Johnson/HB/LLHARD/KB8/Row.lean) can be met together: they
do not contradict each other. Definitions, statements and proofs by unfolding.

What `xMade` is. A value of the type `Key.Source` whose fields that the premises name hold the typed
sizes of a key of full size (`keyFull`), and whose sizes and plans are the written parts joined
(`writtenMade`, Johnson/Goal/Written/Made.lean). Every other field is empty or a default: the
parameter bytes, the plans as read back, the declared rounds and the tenants that X holds, the
units of rows, the proof file's and the entry file's chains. It comes of no public files. The
description's tests on the plan are not asked of it here.

Main names.
  `xMade`; `pins_met : Pins xMade rangesNumsFull laterPlacesFull`; `lin_met`.
  `r8_at_made`, `r8'_at_made`: so the statements of r8 and r8' (see Row.lean's head) hold at it.

Limits. This guards against premises that cannot be met at all, and against nothing else. That the
X, N and P which `Key.sourceOf`, `Key.rangesNumbers` and `Key.laterPlaces` return at the release's
public files meet the premises is shown by no theorem in this file or in the files that it imports.
The pieces lie in other files, under three premises: the public files are in scope of the goals
(`VerifierAndGoals.InScope`), `publicOfO` returns on them, and m is what `Key.madeAt` then returns at the
constant digest `Key.fixedDigest`. N and P: `rangesNumbers_in_scope` and `laterPlaces_in_scope`
(both in the namespace `Johnson.AtFull.KeyBack`; Johnson/AtFull/KeyBack/InScope.lean) say what
`Key.rangesNumbers` and `Key.laterPlaces` return at m, and `pinsNP_full` (PinsOfEnds.lean in this
folder) that these values meet the premises on N and P. X:
`Johnson.AtFull.KeyBack.sourceOf_named_in_scope` (Johnson/AtFull/KeyBack/InScopeNamed.lean) says
that `Key.sourceOf m` returns, and `pinsX_at_fixed` (PinsOfReturns.lean in this folder) that what it
returns meets the premises on X. `pins_of_parts` (PinsOfEnds.lean) makes `Pins` of the two parts.
The three premises are met at the library's written copy of the full-size public files
(`VerifierAndGoals.storedPublicFiles`: three terms written in Lean; no theorem ties them
to the shipped files): the first by `VerifierAndGoals.inScope_full` (Johnson/Goal/Files/ScopeExample.lean),
the other two by `AtFullSide.Planner.theKeyLaid_zFull_returns`
(AtFullSide/Planner/KeyLaidReturns.lean), at the format's second hash function (`OnBytes.secondHashFunction`)
and the same constant digest (`Key.fixedDigest`), not the files' own, in a side library outside the
main library (one constant beneath it passes Lean's kernel only at a larger thread stack; Lean's
re-checker, leanchecker, was run on it and fails there at each shell stack limit that was tried; the
toolchain's own replay passes it at a larger thread stack; so that constant has been checked by the
kernel in the build and by that replay, and by no independent program); no independent checker has
replayed any of the closed facts beneath it, and the full-size example's weights are synthetic.
These last two theorems speak of `VerifierAndGoals.storedPublicFiles` alone, not of other files in scope. The pieces are
used together at `VerifierAndGoals.storedPublicFiles` inside the proof of `AtFullSide.Planner.theKeyLaid_zFull_returns`,
which reaches `Johnson.AtFull.KeyBack.keyBack_at_fixed_of_rest`
(Johnson/AtFull/KeyBack/KeyBackAtFixed.lean), whose proof calls them all; no theorem is known
that states the conjunction by itself.

Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB8.Row
import Johnson.Goal.Written.Made

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB8

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.G Johnson.G.OfPlan
open OnBytes OnBytes.Params
open Lk6.AtPlan (keyFull)

/-- Parameter bytes that hold nothing. -/
def givenNone : Given := ⟨.empty, ⟨.two, 0, 0, 0, 0, 0, []⟩, .empty, []⟩

/-- A key's three chains: the fields that the premises name at the typed sizes. -/
def keyMade : KeyChains :=
  ⟨⟨givenNone, keyFull.once.input, keyFull.ranges.x, default, keyFull.codes, keyFull.once.shape⟩,
    ⟨givenNone, keyFull.codes, keyFull.once.shape⟩, ⟨givenNone⟩⟩

/-- The seven chains: the written parts joined, at empty bytes. -/
def chainsMade : Model.Verify.Chains :=
  ⟨VerifiableInference.PlanWritten.Joined.writtenMade.at MadeFree.Hung.none, keyMade,
    ⟨givenNone, default, default⟩,
    ⟨⟨givenNone, default, default, default, default, [], 0, default, []⟩,
      ⟨givenNone, default, default⟩, ⟨givenNone⟩⟩⟩

/-- **An X made for the purpose: it comes of no public files.** -/
def xMade : Source :=
  ⟨⟨keyMade, keyFull.once.shape, (default, default, default), keyFull.once.input, keyFull.ranges.x,
      0, ([], [], []), ([], [], []), []⟩, chainsMade, keyFull.set⟩

/-- **The premises can be met together.** -/
theorem pins_met : Pins xMade rangesNumsFull laterPlacesFull :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ⟨_, rfl, rfl, rfl⟩, rfl, rfl⟩

/-- The premise of `r8'_of_lin` is met at it too. -/
theorem lin_met : xMade.Y.k.shared.lin = keyFull.once.shape := rfl

/-- The statement of r8 at it. -/
theorem r8_at_made :
    writtenOf "key file" (descriptionFromSource xMade rangesNumsFull laterPlacesFull).roundsDeclaredByBlocks = .ok dryKeyFull :=
  r8_of_pins pins_met

/-- The statement of r8' at it. -/
theorem r8'_at_made : (descriptionFromSource xMade rangesNumsFull laterPlacesFull).tableDepth = 32 :=
  r8'_of_lin _ _ lin_met

end Johnson.KB8

#print axioms Johnson.KB8.pins_met
#print axioms Johnson.KB8.lin_met
#print axioms Johnson.KB8.r8_at_made
#print axioms Johnson.KB8.r8'_at_made
