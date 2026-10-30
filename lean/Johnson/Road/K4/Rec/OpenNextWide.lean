-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Rec/OpenNextWide.lean: TWO TESTS ON THE LIST OF EXTRA PUBLIC TESTS, `openNextB`
(Johnson/Road/K4/Rec/NextEntryStatement.lean) AND `openMaskB`
(Johnson/Road/K4/Rec/MaskEntryStatement.lean), EVALUATED BY LEAN's KERNEL behind K4's sub-protocol
at each of its twelve places of the written list of 25 segments, AT THE WIDER MEANING's OWN LIST
`moreWideAll` (Johnson/Desc/Sound/MgWide.lean), with negative tests; and the two as theorems at the
term `mgWide Dm E mgBase`.

  **`k4_openNext_wide`**: BY THE KERNEL: `k4OpenNextFit moreWideAll` accepts; the places are twelve.
  `k4_openNext_small`: A NEGATIVE TEST: at the composed meaning's own small list `moreAll`
    (Johnson/Desc/Sound/MoreAll.lean) `openNextB` rejects at each of the twelve.
  `k4_openNext_other`: A NEGATIVE TEST: asked for the segment after next, `openNextB` rejects at
    each of the twelve, at the wider list.
  `k4OpenMaskFit`, `openMask_of_fit`: `openMaskB` behind K4's sub-protocol at every place of K4's,
    as one test with its law, general in the list.
  **`k4_openMask_wide`**: BY THE KERNEL: it accepts at `moreWideAll`. `k4_openMask_small`: A
    NEGATIVE TEST: at `moreAll` `openMaskB` rejects at each of the twelve.
  **`openNext_mgWide`**, `openMask_mgWide`: at a place of K4's (H: in the caller's hand) the two
    tests accept at the field more of `mgWide Dm E mgBase`, at every Dm and E: the first is the
    field openNext of the structure K4NameAt (Johnson/Road/K4/K04LawOf.lean), to the letter, at
    that meaning.
Limits. THE WIDER MEANING IS NOT THE MEANING THAT COUNTS: it is one side of a bridge to the
composed meaning (Johnson/Desc/Sound/PlusDoorA.lean), whose premises are for the most part unpaid.
At the composed meaning's own list both tests reject: the two negative tests say so. THE LIST OF
SEGMENTS IS WRITTEN (`linksFull`), not read off the public parameters. The base is `mgBase`.
K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.


-/
import Johnson.Road.K4.Rec.OpenNextAt
import Johnson.Road.K4.Rec.MaskEntryStatement
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Rec
open OnBytes.Road.K4.Riders (atK4s atK4s_at)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart More flatPlacesOf)
open VerifiableInference.Desc.First.FillK4 (isK4At)
open VerifiableInference.Desc.Sound (linksFull moreAll moreWideAll MgData WideData mgWide mgBase
  moreW moreW_base)

set_option maxRecDepth 1000000 in
theorem k4_openNext_wide :
    (k4OpenNextFit moreWideAll linksFull (flatPlacesOf linksFull true) &&
      ((flatPlacesOf linksFull true).countP (isK4At linksFull) == 12)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the small list the test rejects at every place of K4's. -/
theorem k4_openNext_small :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k m =>
      !openNextB moreAll linksFull (flatPlacesOf linksFull true) (k + 1) m) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: asked for the segment after next the test rejects. -/
theorem k4_openNext_other :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k m =>
      !openNextB moreWideAll linksFull (flatPlacesOf linksFull true) (k + 1) (m + 2)) = true := by
  decide +kernel

/-- The three items of `openMaskB` are open behind K4's sub-protocol, at every place of K4's. -/
def k4OpenMaskFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  atK4s links ps fun k _ => openMaskB M links ps (k + 1)

/-- What an accept gives at a place of K4's. -/
theorem openMask_of_fit {M : More} {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
    (H : AtK4 links ps k m pl) (h : k4OpenMaskFit M links ps = true) :
    openMaskB M links ps (k + 1) = true :=
  atK4s_at (t := fun k _ => openMaskB M links ps (k + 1)) H h

set_option maxRecDepth 1000000 in
theorem k4_openMask_wide :
    k4OpenMaskFit moreWideAll linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the small list the test rejects at every place of K4's. -/
theorem k4_openMask_small :
    (atK4s linksFull (flatPlacesOf linksFull true) fun k _ =>
      !openMaskB moreAll linksFull (flatPlacesOf linksFull true) (k + 1)) = true := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (E : WideData P) {k m : ℕ} {pl : Place}

/-- **The field openNext at the wider meaning.** -/
theorem openNext_mgWide (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) :
    openNextB (mgWide Dm E mgBase).more linksFull (flatPlacesOf linksFull true) (k + 1) m =
      true := by
  show openNextB (moreW Dm mgBase) linksFull (flatPlacesOf linksFull true) (k + 1) m = true
  rw [moreW_base]
  have h := k4_openNext_wide
  rw [Bool.and_eq_true] at h
  exact openNext_of_fit H h.1

/-- The test `openMaskB` at the wider meaning. -/
theorem openMask_mgWide (H : AtK4 linksFull (flatPlacesOf linksFull true) k m pl) :
    openMaskB (mgWide Dm E mgBase).more linksFull (flatPlacesOf linksFull true) (k + 1) = true := by
  show openMaskB (moreW Dm mgBase) linksFull (flatPlacesOf linksFull true) (k + 1) = true
  rw [moreW_base]
  exact openMask_of_fit H k4_openMask_wide

end

end OnBytes.Road.K4.Rec

#print axioms OnBytes.Road.K4.Rec.k4_openNext_wide
#print axioms OnBytes.Road.K4.Rec.k4_openNext_small
#print axioms OnBytes.Road.K4.Rec.k4_openNext_other
#print axioms OnBytes.Road.K4.Rec.openMask_of_fit
#print axioms OnBytes.Road.K4.Rec.k4_openMask_wide
#print axioms OnBytes.Road.K4.Rec.k4_openMask_small
#print axioms OnBytes.Road.K4.Rec.openNext_mgWide
#print axioms OnBytes.Road.K4.Rec.openMask_mgWide
