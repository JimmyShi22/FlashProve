-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/BookAtIdleWants.lean: the shared "sending" (the kind K1): the test lendsOk on an entry of the book, and ONE PASS: it accepts the stretches' entries. Cut out of BookAtIdle.lean, statements unturned, so
that Lean's kernel walks one long written list in one process (with both walks in one file a build under a cap of 32 GiB
died on another house's lane). Public data alone. No property of the protocol is claimed.
-/
import AtFullSide.K14.BookWholeWritten
import AtFullSide.K14.RawEntriesKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K1
open VerifiableInference.Desc
open ProofFile.Honest
open AtFullSide.K14

/-- **The test on an entry.** -/
def lendsOk (e : Ahead) : Bool :=
  !e.once || e.owner.place.kind != .K1 || e.owner.place.link.isNone ||
    e.owner == (⟨⟨1, some 0, 1, .K1⟩, 0⟩ : Addr)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- The test accepts the stretches' entries. -/
theorem wants_lend : ((rawWantsW.map (·.entry)).all lendsOk) = true := by
  decide +kernel

end AtFullSide.K1

#print axioms AtFullSide.K1.wants_lend
