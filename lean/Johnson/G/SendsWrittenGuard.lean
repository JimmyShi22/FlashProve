-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/G/SendsWrittenGuard.lean: one test at the build: Lean's evaluator makes the seven chains'
lists of sendings of oracle messages at the full size's three shipped public files (`sendsOf`,
Johnson/G/Sends.lean, at Johnson/G/KitFull.lean) and holds six of them, whole, against the written
lists (`keySendsFull`, `proofSendsFull`, Johnson/G/SendsWritten.lean). In the pattern of
Johnson/G/SendsLitGuard.lean.

  `writtenOk K`: the made lists are seven, and the key file's three and the proof file's three are
    the written ones, by `sameThree` (Johnson/Desc/Ok/PlanWritten/SendsTest.lean): all four fields
    of a chain, all five of every sending.
  One «#guard»: `writtenOk` at these files. A pure value: nothing is read or printed.

What it adds. The written lists were laid off one print, made on another road (the public part of
the IOP as written in Lean). Here the evaluator makes the lists anew, by `sendsOf`, in every build:
so the labels and the two entries of each sending stand on a second evaluation too. The two roads
are not independent: that road's planner is a copy of the library's text, changed in a few lines
(Johnson/Desc/ProofFile/PlanPlain.lean, whose head also tells how far equations between copy and
library are proved). So a yes shows that the program that laid the written value did not slip, and
that copy and library agree in these six lists at these files; an error in the shared text stands on
both roads.

Can it say no. By its make: `writtenOk` says no at an error and at any number of lists but seven.
That a yes of `sameThree` leaves no field and no sending out is a theorem (`sameThree_eq`,
Johnson/Desc/Ok/PlanWritten/SendsTestLaws.lean), and the same file shows its parts (`sameSending`,
`sameSends`, `sameChain`) saying no at one changed field after another (`reject_entry` to
`reject_codes`). No value at which this guard says no is shown in this file.

Limits. An evaluator's answer, no theorem. At these three files alone, as Johnson/G/KitFull.lean
holds them: that the typed values are files of the repository is not tested here. The fourth list
(the copy's file's) is not held. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.SendsTest
import Johnson.G.KitFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.G
open VerifiableInference.PlanWritten (sameThree)

/-- The made lists are seven, and six of them are the written ones. -/
def writtenOk (K : Except String (List ChainSends)) : Bool :=
  match K with
  | .ok [k0, k1, k2, _, p0, p1, p2] =>
    sameThree (k0, k1, k2) keySendsFull && sameThree (p0, p1, p2) proofSendsFull
  | _ => false

#guard writtenOk (sendsOf KitFull.policy.toUTF8 KitFull.layout.toUTF8 KitFull.scales)

end Johnson.G
