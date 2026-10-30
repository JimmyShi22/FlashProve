-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/Top.lean: what an accepted entry file gives at the library's run function.



The file is about `runEntry`: the library's run function on bytes (Run/PlanQXRun.lean), at any
description D and at any decision dec on what was read.




Main theorem.
 `runEntry_accepted`: if `runEntry D dec r0 file` accepts, its head gives the copy's root and the
   chain's bytes, reader and typing give a proof string, and `VX` says yes on that string.








Not claimed, in short.
 No bound on the probability that a false file is accepted.

 That the written link is sound for a language of interest.


 `runEntry D dec` is not the program's function.
 That the first table's root belongs to a checked key: of the key nothing is read but the root.
OnBytes/Slice/README.md: "The vocabulary", "What no theorem here says", "Not claimed" (TopAny.lean).
-/
import OnBytes.Slice.Experiment
import Run.PlanQXFastR
import Fmt.M3Items
import Fmt.M3Dec
import Fmt.ParamsRead
import Fmt.Rules5Fast
import Fmt.M3Entry
import Run.PlanQXDoorProofs

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch Run Run.PQ
open scoped ENNReal

/-- An entry file that the run function accepts: its head gives the copy's root and the chain's
bytes; the strict reader and the typing give a proof string; the verifier says yes on it. -/
theorem runEntry_accepted (D : XD) (dec : View → Bool) (r0 file : ByteArray)
    (h : runEntry D dec r0 file = .accepted) :
    ∃ r1 rest π, readHead file = some (r1, rest) ∧
      (_root_.Fmt.wholeChainX (m := Id) _root_.Fmt.formatHash (D.atR r0 r1) rest).bind
        (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) = some π ∧
      VX D dec r0 r1 π = true := by
  unfold runEntry at h
  split at h
  · split at h
    · cases h
    · next r1 rest hr =>
      split at h
      · cases h
      · next π hπ =>
        split at h
        · next hv => exact ⟨r1, rest, π, hr, hπ, hv⟩
        · cases h
  · cases h

end OnBytes.Slice

