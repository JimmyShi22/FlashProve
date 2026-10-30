-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/OkAskedFull.lean: AT THE BORDER IN FRONT OF THE BATCHING OF EVERY ATTENTION LINK OF
THE WRITTEN LIST THE PUBLIC ITEM "more (some m) K5.okAt" IS OPEN, AT THE COMPOSED MEANING's CLOSED
LIST OF EXTRA PUBLIC TESTS (`mgMore`, Johnson/Desc/Sound/MgAllAt.lean). Closed facts, by the
kernel: the premise hq of okAtt_k5_at (Johnson/Desc/First/Link/Law/OkK5Paid.lean).

What is said.
  `okAskedB m`: the test at link m: the item stands in the open public set at the number of m's
    batching.
  `okAsked_full`: **yes at every attention link.** `okAsked_count`: there are twelve of them: the
    sentence is not idle.
  `okAsked_off`: THE NEGATIVE LINE: at no link of another sort is the item (at that link's number)
    open there.
  `okAsked_at`: the fact at a link, as a membership: hq's form at mgMore.

Limits. Closed facts on the written list and the closed list of tests. That the item's Bool accepts
an honest state is not said here. Nothing on soundness.

-/
import Johnson.LPFK9R.SitsAtConstant
import Johnson.Desc.Sound.MgAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFK9
open VerifiableInference.Desc.First (ModelPart Pub pubSets)
open VerifiableInference.Desc.Sound (mgMore)
open VerifiableInference.Desc.LinkJoin (batchAt)
open P5J (fullLinks)

/-- The item is open in front of link m's batching. -/
def okAskedB (m : ℕ) : Bool :=
  ((pubSets mgMore fullLinks P5J.At.ps)[batchAt fullLinks P5J.At.ps m]?.getD []).contains
    (Pub.more (some m) "K5.okAt")

set_option maxRecDepth 1000000 in
/-- **BY THE KERNEL: at every attention link.** -/
theorem okAsked_full : (List.range 25).all (fun m =>
    !(fullLinks[m]? == some ModelPart.attention) || okAskedB m) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- There are twelve. -/
theorem okAsked_count : ((List.range 25).filter fun m =>
    fullLinks[m]? == some ModelPart.attention).length = 12 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The negative line: at no link of another sort. -/
theorem okAsked_off : (List.range 25).any (fun m =>
    !(fullLinks[m]? == some ModelPart.attention) && okAskedB m) = false := by decide +kernel

/-- The fact at a link, as a membership. -/
theorem okAsked_at (m : ℕ) (hm : m < 25) (ha : fullLinks[m]? = some ModelPart.attention) :
    Pub.more (some m) "K5.okAt" ∈
      (pubSets mgMore fullLinks P5J.At.ps)[batchAt fullLinks P5J.At.ps m]?.getD [] := by
  have h := List.all_eq_true.1 okAsked_full m (List.mem_range.2 hm)
  rw [ha] at h
  have h' : okAskedB m = true := by simpa using h
  exact List.contains_iff_mem.1 h'

end LPFK9

#print axioms LPFK9.okAsked_full
#print axioms LPFK9.okAsked_count
#print axioms LPFK9.okAsked_off
#print axioms LPFK9.okAsked_at
