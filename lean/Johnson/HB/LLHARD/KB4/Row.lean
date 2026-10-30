-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/Row.lean: (Key.descriptionFromSource X N P).planOk = true, in the form of the premise r4 of
IM.keyBack_of_rows (Johnson/IMR/KeyBackOfRows.lean), under Pins and four premises on parts of X.

  key_planOk (h : Pins X N P) (hread) (hcfg) (hmade) (hunits) : (Key.descriptionFromSource X N P).planOk = true.
From fileOk_of (FileOk.lean) and planOk_of_fileOk (PlanW.lean).

Beside the theorem. Pins.told asks that the tenants as told are toldKeyFull (Told.lean), a value
typed by reading. In the theorem's own proof only its groups are weighed, up to their order. Its
other words are held by one fact that neither this file nor a file beneath it imports: oracles_told
(COracles.lean). The field start of the four places' numbers, which Pins.N and Pins.P ask with the
rest, is read by no test on the plan and held by nothing here; firstGroup is held only against a
clash.
What is not shown in this file or in the files that it imports. That the premises can be met
together at any X, N, P. Pins alone is met by a closed source (PinsMet.lean); hread asks that the
three chains' values are read back from bytes: that is had only where the planner returns
(Key.madeAt), which no theorem in this file or in the files that it imports shows at the full size.
In another file, AtFullSide.Planner.theKeyLaid_zFull_returns
(AtFullSide/Planner/KeyLaidReturns.lean) shows that Key.madeAt returns at the library's written copy
of the full-size public files (VerifierAndGoals.storedPublicFiles: three terms written in Lean; no theorem
ties them to the repository's files), at the format's second hash function
(OnBytes.secondHashFunction) and a constant digest (Key.fixedDigest), not the files' own, in a side library
outside the main library (one constant beneath it passes Lean's kernel only at a larger
thread stack; Lean's re-checker, leanchecker, was run on it and fails there at each shell stack
limit that was tried; the toolchain's own replay passes it at a larger thread stack; so that
constant has been checked by the kernel in the build and by that replay, and by no independent
program); no independent checker has replayed any of the closed facts beneath it, and the
full-size example's weights are synthetic. AtFullSide.Planner.theKeyLaid_zFull_returns speaks of
VerifierAndGoals.storedPublicFiles alone, not of other files in scope. The premises of key_planOk are used together at
VerifierAndGoals.storedPublicFiles inside the proof of that theorem, which reaches key_planOk through key_planOk_in_scope
(RowInScope.lean); no theorem is known that states the conjunction by itself.
hmade and hunits are
two of the test on the file's own clauses, taken in their own words: laws that end in them, from
what Key.sourceOf and other routines return, lie in KB9/FileMade.lean and KB9/FileWeights.lean.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.FileOk
import Johnson.HB.LLHARD.KB4.PlanW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open OnBytes OnBytes.Params

/-- **The premise r4 of IM.keyBack_of_rows**, under Pins and four premises on parts of X. -/
theorem key_planOk {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces} (h : Pins X N P)
    {b₁ b₂ b₃ : ByteArray} (hread : KeyChains.read b₁ b₂ b₃ = some X.Y.k)
    (hcfg : (X.Y.k.oneTime.given.cfg != Fmt.zero32) = true) (hmade : madeAgainOk X.Y = true)
    (hunits : weightsCovered X.Y.units X.Y.k.oneTime.ranges = true) :
    (descriptionFromSource X N P).planOk = true :=
  planOk_of_fileOk (chainPins_of h) h.D h.lin₂ (fileOk_of h hread hcfg hmade hunits)

end Johnson.KB4

#print axioms Johnson.KB4.key_planOk
