-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/Sound/MgAt/K3CallsAsks.lean: THE LOOKUP ON A LINK's CALLS AT THE COMPOSED MEANING
mgAll: THREE SMALL PREMISES OF K3's FILES' PAYMENTS, PAID: onIn (of objIn_mgAll,
Johnson/Desc/Sound/MgAt/K3CallsObjIn.lean): under the table's promise in front the kind's own test
in front holds of an unmarked state (the item lookIn is asked by the row, so it is open; at mgAll
its test is the kind's); askSent, askFree (of objects_att_mgAll_facts, objects_lay_mgAll_facts,
Johnson/Desc/Sound/MgAt/K3CallsObjFacts.lean): "frame.sentIs" l and freeAbove l are open at the
border behind: a test on the table by the kernel at all 25 segments, with a negative test. NO
SOUNDNESS IS CLAIMED.

OBJECT: the table of joints; the composed public test at lookIn.
Used by K3CallsPaid.lean (Johnson/Desc/Sound/MgAt/).
LETTERS: those of MgAt/K3CallsOthers.lean; sub: the segment's sort.

WHAT IS LEFT, BOOKED: test: hfit (the ledger's pubs), the place's facts · term: hmore (for the two
  on the border behind).

Main names: `calls_onIn_mgAll` · `asksBehindB`, `asksBehindB_mgMore` (by the kernel),
  `asksBehindB_wrong` (A NEGATIVE TEST) · `asks_behind_mgAll`.

Limits. The full size's written list and mgMore.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.MgAt.K3CallsOthers

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Inst.Model Inst.Model.All
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look.Stored (oWc wOfC msgWc smpWc strWc)
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn pubFit shift sameStand bookFit pubStep pubRowM stepOpen pubOfItems)
open VerifiableInference.Desc.First (More moreItem)
open VerifiableInference.Desc.First.FillSent (sentName)
open _root_.Meaning (linkTieB BaseSegF seatBy fLay hidAtF ReadsOne sizesFit)

/-- At the border behind the lookup on the calls of each segment the two items are open. ask: which
items, as a letter. -/
def asksBehindB (M : More) (ask : ℕ → List Pub) : Bool :=
  (List.range 25).all fun l => (ask l).all
    ((pubSets M linksFull
      (Desc.First.flatPlacesOf linksFull true))[kOfCalls l + 1]?.getD []).contains

set_option maxRecDepth 1000000 in
theorem asksBehindB_mgMore :
    asksBehindB mgMore (fun l => [moreItem (sentName l), .freeAbove l]) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the item lookIn, which the row closes, is open there no more. -/
theorem asksBehindB_wrong : asksBehindB mgMore (fun l => [.lookIn l 2]) = false := by
  decide +kernel

section
variable {Xi P Tok Cl : Type} {rows cols nR : ℕ} {X : Verify.Public} {Fr : Frame}
  (Dm : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Desc.Wit (CellsQ rows cols) Tok MsgT))
  {k l : ℕ} {x : Desc.First.Look.Place} {a : Desc.Place} {sub : ModelPart}

local notation "PS" => Desc.First.flatPlacesOf linksFull true
local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **askSent, askFree.** -/
theorem asks_behind_mgAll (hmore : Mg.more = {}) (hl : l < 25) :
    moreItem (sentName l) ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[kOfCalls l + 1]?.getD [] ∧
      Pub.freeAbove l ∈ (pubSets (mgAll Dm Mg).more linksFull PS)[kOfCalls l + 1]?.getD [] := by
  rw [mgAll_more_closed Dm Mg hmore]
  have h := List.all_eq_true.1 (List.all_eq_true.1 asksBehindB_mgMore l (List.mem_range.2 hl))
  exact ⟨List.contains_iff_mem.1 (h _ (by simp)), List.contains_iff_mem.1 (h _ (by simp))⟩

/-- **onIn.** -/
theorem calls_onIn_mgAll (hfit : pubFit (mgAll Dm Mg).more linksFull PS = true)
    (here : PS[k]? = some a) (hla : a.link = some l) (hsub : linksFull[l]? = some sub)
    (hpc : a.piece = 2 + shift sub) (hpcX : a.piece = Desc.K3.pieceAt X l false)
    (hlook : lookAt X l false = some x) (z : P) (u : Desc.First.S × Fr.E.Str)
    (hu : onQ Dm.N (mgAll Dm Mg) linksFull PS (fun s => (z, s)) k u) (hf : u.1.failed = none) :
    Desc.K3.k3OnIn theP u.1 = true :=
  k3LookIn_onIn (fLook_at (k3At_mgAll Dm Mg) l false hlook z u.1 (by
    rw [← hpcX, hpc]
    exact onQ_front hu hf _ (List.mem_append_left _
      (calls_asks_open (mgAll Dm Mg).more linksFull PS k a l sub hfit here hla hsub hpc _
        (by simp)))))

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.asksBehindB_mgMore
#print axioms VerifiableInference.OnPublicFiles.asksBehindB_wrong
#print axioms VerifiableInference.OnPublicFiles.asks_behind_mgAll
#print axioms VerifiableInference.OnPublicFiles.calls_onIn_mgAll
