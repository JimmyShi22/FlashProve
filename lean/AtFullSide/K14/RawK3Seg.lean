-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawK3Seg.lean: AT THE WRITTEN DESCRIPTION WP: OF THE 5,130 CARRYING ENTRIES OF THE
CHAIN OF SEGMENTS (rawSegW, AtFullSide/K14/RawAheadWritten.lean) NONE NAMES ONE OF THE FIFTY PLACES
OF THE KIND K3 (k3SitesW, AtFullSide/K14/RawK3Sites.lean) AS ITS SPENDER's. One statement: one
evaluation in Lean's kernel.

Limits. rawSegW HOLDS A DEFAULT ON A MAKER's RETURN: AT AN ERROR IT WOULD BE EMPTY AND THIS "all"
TRUE FOR NOTHING: THAT IS BARRED BY rawSeg_returns AND rawSeg_ok (RawAheadWritten.lean) AND BY
rawSegW_length (AtFullSide/K14/RawLengthsWritten.lean: 5,130): QUOTE THIS STATEMENT BESIDE THESE
ALONE. The negative test for this form of test stands at the written pieces: k3None_bent
(AtFullSide/K14/RawK3Rest.lean); at rawSegW itself there is none. WP's own limit stands. Addresses
on public data: nothing on soundness, completeness or hiding.

How. The maker reads each message's link through String.splitOn and String.toNat?, past which the
kernel is led by the library's Johnson.Unfolds.splitOn_eq and slice_toNat?_eq.
AN OPTION IS RAISED: maxRecDepth to 1000000 (no lower number was tried).
What is assumed. Nothing.
-/
import AtFullSide.K14.RawK3Sites
import AtFullSide.K14.RawAheadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest

set_option maxRecDepth 1000000 in
/-- **No carrying entry of the chain of segments names one of the fifty places as its spender's.**
-/
theorem k3Seg_none :
    rawSegW.all (fun e => !k3SitesW.any fun s => s.at_.place == e.spender.place) = true := by
  unfold rawSegW segmentCarries linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.k3Seg_none
