-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Second/Seam/LinksOne.lean: THE WRITTEN LISTS OF THE FIRST CHAIN's SEGMENTS AT THE FULL SIZE ARE ONE LIST: four closed terms in three folders, each a List Sub of 25: P5J.fullLinks (Johnson/P5J/MeansQ.lean) · Sound.linksFull (Johnson/Desc/Sound/AtDriver.lean) · the lookups' fullSubs (Johnson/Desc/First/Look/K3RowIndex.lean) and liveFull (K3LiveIs.lean). By Lean's kernel.
  links_one      fullLinks = linksFull ∧ linksFull = fullSubs ∧ fullSubs = liveFull ∧ the length is 25 ∧ linksOk accepts at it.
  links_one_small  the like for the small lists that lie: Sound.linksSmall = smallSubs = liveSmall; five segments.
  links_not        a negative twin: the full list is not the small one; nor is it itself without its head.
Limits. That the list at a seat IS this list is not said here (LinksOk.lean's linksOk_of_chainC needs no closed list). No soundness is claimed.

-/
import Johnson.Second.Seam.LinksOk
import Johnson.Desc.Sound.AtDriver
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Second.Seam
open VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.OnPublicFiles (fullSubs smallSubs)


theorem links_one : P5J.fullLinks = Sound.linksFull ∧ Sound.linksFull = fullSubs ∧
    fullSubs = Look.liveFull ∧ P5J.fullLinks.length = 25 ∧ linksOk P5J.fullLinks = true := by
  decide +kernel

theorem links_one_small : Sound.linksSmall = smallSubs ∧ smallSubs = Look.liveSmall ∧
    Sound.linksSmall.length = 5 ∧ linksOk Sound.linksSmall = true := by decide +kernel

theorem links_not : P5J.fullLinks ≠ Sound.linksSmall ∧ P5J.fullLinks ≠ P5J.fullLinks.dropLast := by
  decide +kernel

end Second.Seam

#print axioms Second.Seam.links_one
#print axioms Second.Seam.links_one_small
#print axioms Second.Seam.links_not
