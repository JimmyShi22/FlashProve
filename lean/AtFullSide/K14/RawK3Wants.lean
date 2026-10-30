-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K14/RawK3Wants.lean: AT THE WRITTEN DESCRIPTION WP (Johnson/AtFull/ProofPlan/WP.lean),
THE WRITTEN SENDINGS AND THE MERGES THAT mergesByName GUESSES: OF THE FRAME's 7,940 STRETCHES
(rawWantsW, AtFullSide/K14/RawAheadWritten.lean) THOSE WHOSE SPENDER STANDS AT ONE OF THE FIFTY
PLACES OF THE KIND K3 (k3SitesW, AtFullSide/K14/RawK3Sites.lean) HAVE, IN THE MAKER's ORDER, THE
KEYS OF THE RUNS THAT THE LOOKUPS' PARTS STATE (k3Keys, AtFullSide/K14/K3KeysOfStated.lean). One
statement: one evaluation in Lean's kernel.

Limits. rawWantsW holds a default on a maker's return (rawLinksW): at an error it would be short,
and this equation false: it says of itself that the maker's list is there; rawLinks_returns
(RawAheadWritten.lean) says so outright. THAT THE FIFTY ARE THE LOOKUPS' OWN SITES AT ANY PUBLIC
PART IS NO THEOREM (RawK3Sites.lean's head). The merges are a guess; WP's own limit stands; the full
size alone. A key is public data: addresses, names and counts: nothing on soundness, completeness or
hiding. The negative test stands in AtFullSide/K14/RawK3WantsBent.lean.

AN OPTION IS RAISED: maxRecDepth to 1000000 (no lower number was tried).
What is assumed. Nothing.
-/
import AtFullSide.K14.K3KeysOfStated
import AtFullSide.K14.RawK3Sites
import AtFullSide.K14.RawAheadWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K14
open ProofFile.Honest

set_option maxRecDepth 1000000 in
/-- **The stretches at the fifty places have the stated keys, in the maker's order.** -/
theorem k3Wants_written :
    (rawWantsW.filter fun w => k3SitesW.any fun s => s.at_.place == w.spender.place).map wantKey =
      k3Keys k3SitesW := by decide +kernel

end AtFullSide.K14

#print axioms AtFullSide.K14.k3Wants_written
