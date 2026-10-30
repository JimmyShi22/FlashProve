-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Law/Rule/LedgerOpen.lean: ON THE WRITTEN LISTS: WHICH OF THE TABLE's
PUBLIC ITEMS THAT SAY THE LEDGER's NEXT FREE SLOT ARE OPEN AT WHICH BORDER. At the full size's list
of segments and places (`P5J.At.links`, `P5J.At.ps`, Johnson/P5J/LettersAt.lean) and the closed
list of extra public tests (`(moreOver9 {}).strike leavesName`): the open public sets are the
library's own function of these lists (`pubSets`, Johnson/Desc/First/Borders.lean). Each sentence
is decided by Lean's kernel, as the library's own decisions on these lists are
(Johnson/Desc/First/Att/Door/Law/K5ListsFull.lean).

`open_callerIn` "callerIn l" is open at 14 l + 4, at each of the 24 segments in front of the
head's: in front of the feed-forward caller's and the attention caller's members
`open_lookIn_calls` "lookIn l 2" at 14 l + 3, and "lookIn 24 3" at 340: in front of the lookups on
the calls `open_lookIn_digits` "lookIn l 7" at 14 l + 8, and "lookIn 24 8" at 345: in front of the
lookups on the digits `not_open_head` THREE NON-MEMBERSHIPS, NO MORE: at 341 (in front of the
head's caller) neither "callerIn 24" nor "lookIn 24 3" is open; at 346 (in front of the merge)
"lookIn 24 8" is not. What the other items that are open there say is not read here

Before this file these stood in a replica of the sets alone, made outside Lean by another author of
this project (at 74 of 76 borders).

BY `decide +kernel` (Lean's kernel evaluates a closed, true sentence on the library's own written
lists): all four theorems. THE CONTROL THAT SAYS NO: `not_open_head`.

Limits. DECIDED AT ONE VERSION OF THE TABLE AND OF THE LISTS: at another the file compiles again or
it does not. What an item's test says is not here. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.P5J.LettersAt
import Johnson.Desc.First.Att.Door.Plus

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (Pub pubSets leavesName)
open H2K5.Door (moreOver9)

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem open_callerIn : ∀ l, l < 24 →
    Pub.callerIn l ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[14 * l +
        4]?.getD [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem open_lookIn_calls : (∀ l, l < 24 →
    Pub.lookIn l 2 ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[14 * l +
        3]?.getD []) ∧
    Pub.lookIn 24 3 ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[340]?.getD
        [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem open_lookIn_digits : (∀ l, l < 24 →
    Pub.lookIn l 7 ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[14 * l +
        8]?.getD []) ∧
    Pub.lookIn 24 8 ∈ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[345]?.getD
        [] := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option synthInstance.maxSize 100000 in
set_option synthInstance.maxHeartbeats 2000000 in
theorem not_open_head :
    Pub.callerIn 24 ∉ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[341]?.getD
        [] ∧
    Pub.lookIn 24 3 ∉ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[341]?.getD
        [] ∧
    Pub.lookIn 24 8 ∉ (pubSets ((moreOver9 {}).strike leavesName) P5J.At.links P5J.At.ps)[346]?.getD
        [] := by
  decide +kernel

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.open_callerIn
#print axioms ProofFile.Honest.FirstThread.open_lookIn_calls
#print axioms ProofFile.Honest.FirstThread.open_lookIn_digits
#print axioms ProofFile.Honest.FirstThread.not_open_head
