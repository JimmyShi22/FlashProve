-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/EndTestsAll.lean: THE LAST CHAIN's LEDGER's THREE TESTS ON THE FIRST TABLE's
LAST BORDER (sampled · wIn · iIn) AT EVERY LAWFUL LIST OF SEGMENTS, BY CALLS. One theorem. A LIGHT
FILE: it stands on the first table's text, Johnson/Desc/K13/Law/EndTests.lean and
Johnson/Desc/K13/Law/OpenSetAtEnd.lean alone, so that it can be imported
without the shared chain's ledger.

  endTests_all   the three, at every links with linksOk links = true, from N.index.1 < lo and
                 N.w.1 < lo.
What is not claimed. The two comparisons: facts on the public parameters' numbers. Nothing on
soundness.

-/
import Johnson.Desc.K13.Law.EndTests
import Johnson.Desc.K13.Law.OpenSetAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open VerifiableInference.Desc.First (ModelPart Numbers openSets start linksOk sampledIn)
open VerifiableInference.Desc.Sound (sampledBelow)

/-- **The three tests at every lawful list of segments.** -/
theorem endTests_all (links : List ModelPart) (hl : linksOk links = true) (lo : ℕ) (N : Numbers)
    (hI : N.index.1 < lo) (hV : N.w.1 < lo) :
    sampledBelow lo N ((openSets links (First.flatPlaces true links true)
        (start links))[(First.flatPlaces true links true).length]?.getD []) = true ∧
      N.w ∈ sampledIn N ((openSets links (First.flatPlaces true links true)
        (start links))[(First.flatPlaces true links true).length]?.getD []) ∧
      N.index ∈ sampledIn N ((openSets links (First.flatPlaces true links true)
        (start links))[(First.flatPlaces true links true).length]?.getD []) :=
  ⟨sampledBelow_of_open lo N _ (endOpenOnly links hl) hI hV, w_sampled N (endOpenPins links hl).1,
    index_sampled N (endOpenPins links hl).2⟩

end VerifiableInference.Desc.K13.Law
