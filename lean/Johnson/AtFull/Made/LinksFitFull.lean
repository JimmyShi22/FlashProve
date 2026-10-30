-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Made/LinksFitFull.lean: `linksFit` (OnBytes/Model/StagesLinks.lean) RETURNS AT THE 25
WRITTEN VIEWS, THE WRITTEN CODES, THE WRITTEN SHAPE OF THE REQUEST AND THE WRITTEN LAYOUT OF THE
FULL SIZE. Closed facts by Lean's kernel, and two joinings. A law file; no running text imports it.
Nothing on codes as such: the codes enter as a written list of sizes.

What it is for. `built_at_full` and `fit_at` (Johnson/AtFull/Made/BuiltAtFull.lean) take this closed
fact as their premise hF, to the letter. The premise c₃ of `chainsOf_of_parts`
(Johnson/AtFull/Made/Ledger.lean) is NOT this fact: it speaks in the letters of the sizes and the
shapes, and wants four equations more: Johnson/AtFull/Made/FitAtSized.lean.

  `ok_of_isOk`: a tool. `entriesFull`: the written views' entries (`viewFull`, `ofView`:
    LinksFull.lean, LinksView.lean).
  `layoutOk_full`, `room_full`, `laid_full`: the three tests of `linksFit`, each alone.
  `linksFit_isOk`, `linksFit_full`: **the whole; hF to the letter.** `linksFit_at`: at every array
    of entries whose views are the written ones (by `linksFit_narrow`).
  `layoutOk_bend`, `room_bend`, `laid_bend`: each of the three says no at a bent value: the first at
    its clause on the lists' lengths, the second at its last arm (no message at the start), not at
    the count of free entries. `laid_bend_life`: the life of the array that the last bend reads is
    some 0; that the refusal comes from there is a reading, no theorem.

Limits. CLOSED FACTS AT WRITTEN VALUES. THAT THE VIEWS, THE CODES, THE SHAPE AND THE LAYOUT ARE THE
PLANNER's AT ANY FILES IS SHOWN NOWHERE HERE: each is a run's print (the heads of LinksFull.lean,
Johnson/G/SendsWritten.lean, Johnson/Desc/ReqLit/Full.lean, Johnson/G/LayoutLit.lean). The three
tests alone are not joined to the whole by a theorem: the whole is evaluated once more. Nothing on
soundness.

-/
import Johnson.AtFull.Made.LinksFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Made
open OnBytes OnBytes.Model OnBytes.Model.Stages OnBytes.Params
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (layoutFull proofCodesWritten)

/-- A test without a value that says yes has returned. -/
theorem ok_of_isOk {x : Except String Unit} (h : x.isOk = true) : x = .ok () := by
  cases x with
  | ok u => rfl
  | error e => cases h

/-- The 25 written views' entries. -/
def entriesFull : Array LinkH := (viewFull.map ofView).toArray

/-! ## 1 The three tests of `linksFit`, each alone -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The layout fits the shape. -/
theorem layoutOk_full : reqLayoutOk proofCodesWritten shapeFull layoutFull = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The index-mask message has room. -/
theorem room_full : (indexMaskRoom entriesFull proofCodesWritten shapeFull 18).isOk = true := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- Every entry fits shape and layout. -/
theorem laid_full : (linksLaid entriesFull proofCodesWritten shapeFull layoutFull).isOk = true := by
  decide +kernel

/-! ## 2 The whole -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem linksFit_isOk :
    (linksFit entriesFull proofCodesWritten shapeFull layoutFull 18).isOk = true := by
  decide +kernel

/-- **`linksFit` returns at the written views**: the premise hF of `built_at_full` and of `fit_at`
(Johnson/AtFull/Made/BuiltAtFull.lean), to the letter. -/
theorem linksFit_full :
    linksFit (viewFull.map ofView).toArray proofCodesWritten shapeFull layoutFull 18 = .ok () :=
  ok_of_isOk linksFit_isOk

/-- **At entries with the written views.** -/
theorem linksFit_at {links : Array LinkH}
    (hv : links.toList.map Johnson.AtFull.Made.viewOf = viewFull) :
    linksFit links proofCodesWritten shapeFull layoutFull 18 = .ok () :=
  (linksFit_narrow links proofCodesWritten shapeFull layoutFull 18).symm.trans
    ((congrArg (fun a => linksFit a proofCodesWritten shapeFull layoutFull 18)
      (narrow_of_views hv)).trans linksFit_full)

/-! ## 3 Each of the three can say no -/

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- The last segment's arrays struck from the layout: the first test says no. -/
theorem layoutOk_bend :
    reqLayoutOk proofCodesWritten shapeFull ⟨layoutFull.link.dropLast⟩ = false := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- No message at the start of the chain: the second test says no. -/
theorem room_bend :
    (indexMaskRoom entriesFull proofCodesWritten { shapeFull with atStart := [] } 18).isOk =
      false := by
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
/-- One entry sends 2 ^ 20 scalars more; one reads an array that is laid nowhere; one reads an array
of segment 0 that is laid there and kept for no later segment: the third test says no at each. -/
theorem laid_bend :
    (linksLaid (entriesFull.modify 3 fun X => { X with ns := X.ns + 2 ^ 20 }) proofCodesWritten
      shapeFull layoutFull).isOk = false ∧
    (linksLaid (entriesFull.modify 3 fun X => { X with arrayOf := X.arrayOf.push (3, "none") })
      proofCodesWritten shapeFull layoutFull).isOk = false ∧
    (linksLaid (entriesFull.modify 3 fun X => { X with arrayOf := X.arrayOf.push (0, "M0") })
      proofCodesWritten shapeFull layoutFull).isOk = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- `linkLaid`'s own term for the life of the array "M0" of segment 0 is some 0: the array is laid,
and 0 + 0 < 3. THAT THE LAST BEND OF `laid_bend` IS REFUSED AT THIS TEST IS NOT SAID BY THIS
THEOREM: it is a reading of `linkLaid`'s text with `laid_full` (all that stands before the pushed
array passes); both refusals of that routine bear one name. `reqArray` is `OnBytes.reqArray`, the
one that `linkLaid` calls; `OnBytes.Params.reqArray` is another. -/
theorem laid_bend_life :
    (do
      let A ← reqArray layoutFull 0 "M0"
      let L ← shapeFull.link[0]?
      let m ← L.messages[A.message]?
      pure m.life : Option Nat) = some 0 := by
  decide +kernel

end Johnson.AtFull.Made

#print axioms Johnson.AtFull.Made.ok_of_isOk
#print axioms Johnson.AtFull.Made.layoutOk_full
#print axioms Johnson.AtFull.Made.room_full
#print axioms Johnson.AtFull.Made.laid_full
#print axioms Johnson.AtFull.Made.linksFit_isOk
#print axioms Johnson.AtFull.Made.linksFit_full
#print axioms Johnson.AtFull.Made.linksFit_at
#print axioms Johnson.AtFull.Made.layoutOk_bend
#print axioms Johnson.AtFull.Made.room_bend
#print axioms Johnson.AtFull.Made.laid_bend
#print axioms Johnson.AtFull.Made.laid_bend_life
