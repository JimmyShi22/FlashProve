-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/MgAt/K3Tests.lean: the kind "lookup" (K3): THE TESTS ON THE TABLE OF JOINTS THAT
THE LOOKUPS' ROWS ASK AT THE MEANING's OWN LIST OF EXTRA PUBLIC TESTS, EVALUATED BY THE KERNEL AT
THE COMPOSED MEANING's CLOSED LIST mgMore (Johnson/Desc/Sound/MgAllAt.lean)
AND THE FULL SIZE's WRITTEN LISTS; and so at mgAll Dm Mg wherever the base's list is
empty. Evaluations, with negative tests. NO SOUNDNESS IS CLAIMED.

Main names.
  pubFit_mgMore: pubFit mgMore linksFull PS = true. hfit_mgAll: so the rows' premise hfit (pubs) at
    mgAll Dm Mg, where Mg.more = {}. FOR BOTH LOOKUPS.
  pubFit_cut: A NEGATIVE TEST: at the list of places cut in front of segment 0's digits the test
    says false (by reading: the first row asks lookIn 0 7, made by nobody).


  digTab_mgMore: digTableB (K3DigitsBehind.lean) at mgMore, at the digits' place of all 25 segments.
    hTab_mgAll: so DigRestR's field hTab. digTab_control: A NEGATIVE TEST: read at segment 0's
    calls' place it says false.
  digFree_mgMore: freeAbove l is open at the border behind the digits' place, at all 25.
    askFree_mgAll: so digMaskR_of_facts' premise askFree (K3DigitsMaskAt.lean).
OBJECT. Functions with code of the table of joints (Johnson/Desc/First/Borders.lean) at closed
lists.
Used by K03BareAt.lean and K03LeftAt.lean (Johnson/P5J/), K3DigitsOwed.lean
(Johnson/Desc/Sound/MgAt/) and others.
LETTERS. Dm, Mg; l, sub.
IS IT EMPTY? The evaluations have no premise. Mg.more = {} holds at the closed base (mgBase,
MgBase.lean).



Compiled with the whole library.
Limits. The full size's lists alone. pubFit is a test of well-formedness: its own head says what it
cannot see.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MoreAll
import Johnson.Desc.First.Look.K3DigitsBehind
import Johnson.Desc.First.Look.K3Base

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Pub Meaning shift pubFit pubSets)

local notation "PS" => Desc.First.flatPlacesOf linksFull true

set_option maxRecDepth 1000000 in
theorem pubFit_mgMore : pubFit mgMore linksFull PS = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test**: at the list of places cut in front of segment 0's digits. By reading: the
first row asks lookIn 0 7, which nobody has made. -/
theorem pubFit_cut : pubFit mgMore linksFull (List.drop (k3K 0 true) PS) = false := by
  decide +kernel

/-- digTableB at the digits' place of segment l. -/
def digTabB (l : ℕ) : Bool :=
  digTableB mgMore linksFull PS (k3K l true) (IM.k3Place l true) l
    (shift (linksFull.getD l .layers))

set_option maxRecDepth 1000000 in
theorem digTab_mgMore : (List.range 25).all digTabB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- **A negative test.** -/
theorem digTab_control :
    digTableB mgMore linksFull PS (k3K 0 false) (IM.k3Place 0 false) 0 0 = false := by
  decide +kernel

/-- freeAbove l is open behind the digits' place of segment l. -/
def digFreeB (l : ℕ) : Bool :=
  ((pubSets mgMore linksFull PS)[k3K l true + 1]?.getD []).contains (.freeAbove l)

set_option maxRecDepth 1000000 in
theorem digFree_mgMore : (List.range 25).all digFreeB = true := by decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))

/-- **hfit | pubs.** -/
theorem hfit_mgAll (h : Mg.more = {}) : pubFit (mgAll Dm Mg).more linksFull PS = true := by
  rw [mgAll_more_closed Dm Mg h]
  exact pubFit_mgMore

/-- **hTab.** -/
theorem hTab_mgAll (h : Mg.more = {}) (l : ℕ) (hl : l < 25) (sub : ModelPart)
    (hsub : linksFull[l]? = some sub) :
    digTableB (mgAll Dm Mg).more linksFull PS (k3K l true) (IM.k3Place l true) l (shift sub) =
      true := by
  rw [mgAll_more_closed Dm Mg h]
  have h0 := List.all_eq_true.1 digTab_mgMore l (List.mem_range.2 hl)
  unfold digTabB at h0
  rw [List.getD_eq_getElem?_getD, hsub] at h0
  exact h0

/-- **askFree.** -/
theorem askFree_mgAll (h : Mg.more = {}) (l : ℕ) (hl : l < 25) :
    Pub.freeAbove l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[k3K l true + 1]?.getD [] := by
  rw [mgAll_more_closed Dm Mg h]
  have h0 := List.all_eq_true.1 digFree_mgMore l (List.mem_range.2 hl)
  unfold digFreeB at h0
  simpa using h0

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.pubFit_mgMore
#print axioms VerifiableInference.OnPublicFiles.pubFit_cut
#print axioms VerifiableInference.OnPublicFiles.digTab_mgMore
#print axioms VerifiableInference.OnPublicFiles.digTab_control
#print axioms VerifiableInference.OnPublicFiles.digFree_mgMore
#print axioms VerifiableInference.OnPublicFiles.hfit_mgAll
#print axioms VerifiableInference.OnPublicFiles.hTab_mgAll
#print axioms VerifiableInference.OnPublicFiles.askFree_mgAll
