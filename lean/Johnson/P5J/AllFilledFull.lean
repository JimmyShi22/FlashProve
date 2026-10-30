-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/AllFilledFull.lean: THE CLOSED FACTS, BY LEAN's KERNEL, FOR
Johnson/P5J/AllFilledAt.lean (whose head says what they are for and what they do not say): every
public item that the first chain's promise asks at any of its 359 borders at the full size is
claimed by a layer of the composed meaning. ALONE IN ITS FILE: twelve decisions of the kernel,
some five minutes together. Twelve theorems: four of them negative tests.
  `allFilledBy_full`, `unfilledBy_full`; `asked_lists`, `sets_lengths`, `asked_items`,
    `asked_none_empty` (so that "every" is not over nothing: 359 lists, none dropped by the zip,
    3,298 items, no list empty); `bend_hd`, `bend_mH`, `bend_links5`, `bend_linksD` (one bend for
    each letter of the test: each says false); `worthFilledBy_full`, `allSaid_full`.
Limits. Closed facts at written letters: 24 24 fullLinks fullLinks stand where the constant's own
data are meant: the tie is `allFilled_at`. A claim is no yes: see that file's head. No soundness
is claimed.

-/
import Johnson.Desc.Sound.MgBase
import Johnson.Desc.First.AllFilledBy
import Johnson.P5J.K09Len

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace P5J
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (allFilledBy unfilledBy worthFilledBy allSaid askedAt pubSets
  openSets start)

/-- **EVERY ASKED PUBLIC ITEM IS CLAIMED BY A LAYER.** -/
theorem allFilledBy_full : allFilledBy 24 24 fullLinks fullLinks mgMore fullLinks At.ps = true := by
  decide +kernel

theorem unfilledBy_full :
    (unfilledBy 24 24 fullLinks fullLinks mgMore fullLinks At.ps).length = 0 := by
  decide +kernel

/-- One list a border. -/
theorem asked_lists : (askedAt mgMore fullLinks At.ps).length = 359 := by decide +kernel

/-- The two lists that are zipped have as many members: the zip drops none. -/
theorem sets_lengths : (pubSets mgMore fullLinks At.ps).length = 359 ∧
    (openSets fullLinks At.ps (start fullLinks)).length = 359 := by decide +kernel

theorem asked_items : ((askedAt mgMore fullLinks At.ps).map List.length).sum = 3298 := by
  decide +kernel

theorem asked_none_empty : ((askedAt mgMore fullLinks At.ps).all fun Q => !Q.isEmpty) = true := by
  decide +kernel

/-- **A negative test**: the lookups' number of the head's segment bent. -/
theorem bend_hd : allFilledBy 23 24 fullLinks fullLinks mgMore fullLinks At.ps = false := by
  decide +kernel

/-- **A negative test**: the head's layer's number bent. -/
theorem bend_mH : allFilledBy 24 23 fullLinks fullLinks mgMore fullLinks At.ps = false := by
  decide +kernel

/-- **A negative test**: the attention caller's list of sorts empty. -/
theorem bend_links5 : allFilledBy 24 24 fullLinks [] mgMore fullLinks At.ps = false := by
  decide +kernel

/-- **A negative test**: the feed-forward caller's list of sorts empty. -/
theorem bend_linksD : allFilledBy 24 24 [] fullLinks mgMore fullLinks At.ps = false := by
  decide +kernel

theorem worthFilledBy_full : worthFilledBy 24 fullLinks At.ps = true := by decide +kernel

theorem allSaid_full : allSaid mgMore fullLinks At.ps = true := by decide +kernel

end P5J

#print axioms P5J.allFilledBy_full
#print axioms P5J.unfilledBy_full
#print axioms P5J.asked_lists
#print axioms P5J.sets_lengths
#print axioms P5J.asked_items
#print axioms P5J.asked_none_empty
#print axioms P5J.bend_hd
#print axioms P5J.bend_mH
#print axioms P5J.bend_links5
#print axioms P5J.bend_linksD
#print axioms P5J.worthFilledBy_full
#print axioms P5J.allSaid_full
