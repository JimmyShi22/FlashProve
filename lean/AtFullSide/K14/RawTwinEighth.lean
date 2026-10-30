-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawTwinEighth.lean: THE EIGHTH TEST's TWIN clause8Q (Honest/BookLinear/Eighth.lean)
ACCEPTS THE RAW BOOK's 13,116 ENTRIES rawAheadW AT orderOf WP AND posW, AT 20 ROUNDS OF THE SORT
(raw8_test). BY ONE EVALUATION IN LEAN's KERNEL (decide +kernel). A WORKING FILE. One statement with
its proof; no definition.

  raw8_test       **clause8Q posW 20 (orderOf WP) rawAheadW = true**: at the whole list at once: the
                  twin sorts all entries by their owners

What it is for: with orderW_nodup (AtFullSide/K14/RawTwinKit.lean), raw7_test
(AtFullSide/K14/RawTwinSeventh.lean) through spent_apart, and clause8Q_of it is the eighth test's
Bool at rawAheadW. That step is not drawn here. That the twin can reject at this size:
AtFullSide/K14/RawTwinEighthBent.lean.

maxRecDepth and maxHeartbeats are lifted in front of the fact. The proof first unfolds rawAheadW,
rawSegW, segmentCarries and linkOf and rewrites by Johnson.Unfolds.splitOn_eq and slice_toNat?_eq:
the kernel cannot run linkOf's text as it stands. IF THE FRAME's segmentCarries TURNS, THE PROOF
RIDES ANEW; that its text can stay is a forecast.

Limits. A FACT ON WRITTEN VALUES: at the proof file's IOP as written in Lean at the full size
(P2Law.ProofPlan.WP), the written sendings (Johnson.G.proofSendsFull) and the merges that
mergesByName lays ("a guess", in the frame's own word): rawAheadW
(AtFullSide/K14/RawAheadWritten.lean) is made at these. rawSegW STANDS OVER THE FRAME's
segmentCarries AS IT IS TODAY. The twin's yes, not the test's. Nothing on what an evaluation costs.
Nothing on any property.
-/
import AtFullSide.K14.RawTwinKit
import Johnson.Desc.ProofFile.Honest.BookLinear.Eighth
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest ProofFile.Honest.K14
open VerifiableInference.Desc (Place)
open P2Law.ProofPlan (WP)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **THE EIGHTH TEST's TWIN ACCEPTS THE RAW BOOK's ENTRIES.** -/
theorem raw8_test : clause8Q posW 20 (orderOf WP) rawAheadW = true := by
  unfold rawAheadW rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.raw8_test
