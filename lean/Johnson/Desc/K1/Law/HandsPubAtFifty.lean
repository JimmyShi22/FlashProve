-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/HandsPubAtFifty.lean:
IM.Hands (what one sub-protocol owes) WHOLE, ALL SIX FIELDS, AT KIND K1's FIFTY
LATER SENDINGS, AT E := HashBuild.EPub z Mg (the two tests of the table of joints' promise that
IM.BK leaves out): as at 355, 356 and 2 (Johnson/Desc/AtSeats/HandsMore.lean). One
theorem: calls alone: five fields by hands_later; the sixth by more_block
(Johnson/Desc/K1/Law/HandsMoreAtLater.lean), the table's row by rowL_digits_full | rowL_reads_full
(by the kernel at the written list) at the meaning's own door Mg.more.
GENERAL IN THE MEANING Mg.
PREMISES THAT STAY, BY NAME. hinj, trees, msgs, hP: on the list of rounds' numbers (binders of
k01_later_tied too, Johnson/Desc/K1/Law/LaterOne.lean; PlanK1 pays them). hg: the open link's frame
has the plan's group of l (a binder of k01_later_tied too, here in the form of the promise's half
with code). hOrd, hRide, hNew: the three
arms of more_block, in InB's form; inAt_bare turns an arm that is shown generally in Mg into that
form.
What is not claimed. These. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.AtSeats.HandsAtLater
import Johnson.Desc.K1.Law.HandsMoreAtLater

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.K13.Law (openAt)
open OnBytes.Model.Stages (LinkH)
open HashBuild (EPub)
open IM (k1Ix k1Reads)

variable {Pp W : Type}

/-- **WHAT ONE SUB-PROTOCOL OWES, WHOLE, AT THE FIFTY.** -/
theorem hands_later_pub (N : Numbers) (Mg : Meaning Pp W) (z : Pp) (ft : ℕ) (Z : ProofFile.Pub)
    (G : ProofFile.Ground) (l : ℕ) (hl : l < 25) (d : Bool) (X : LinkH) (arrs : Option (List ℕ))
    (c : Block S ProofFile.Cl) (hu : c.UnderR ((blkL Z G l d X arrs).retype : Block S ProofFile.Cl))
    (hinj : ∀ m' ∈ First.rowSegs (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)),
      N.groupAt m' = N.groupAt l → m' = l)
    (trees : N.treesAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[noL l d]? + (layOf (parL Z G l d)).shapes.size)
    (msgs : N.msgsAt (flatPlacesOf linksFull true)[noL l d + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[noL l d]? + (parL Z G l d).sent.size)
    (hP : laterSeatsB N (parL Z G l d) l (momL d)
      (N.treesAt (flatPlacesOf linksFull true)[noL l d]?) = true)
    (hg : ∀ s : S, s.failed = none →
      IM.XK N linksFull (flatPlacesOf linksFull true)
        (EPub z Mg linksFull (flatPlacesOf linksFull true)) (noL l d) s = true →
      ∀ L, s.link? = some L → L.check.frame.group = N.groupAt l)
    (hOrd : ∀ x x', YesOf (blkL Z G l d X arrs) x x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x → Mg.inOrder x' = true)
    (hRide : ∀ x x' q, YesOf (blkL Z G l d X arrs) x x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) →
      q ∈ (First.pubSets Mg.more linksFull (flatPlacesOf linksFull true))[noL l d + 1]?.getD [] ++
        First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d + 1)) →
      Mg.pub q x' = true)
    (hNew : ∀ x x' q, YesOf (blkL Z G l d X arrs) x x' →
      InB N Mg linksFull (flatPlacesOf linksFull true) (noL l d) x → q ∈ tiedL Mg.more l d →
      Mg.pub q x' = true) :
    IM.Hands N linksFull (flatPlacesOf linksFull true)
      (EPub z Mg linksFull (flatPlacesOf linksFull true)) ft (noL l d) c := by
  refine hands_later N _ ft Z G l hl d X arrs c hu hinj trees msgs hP hg
    (more_block N Mg linksFull (flatPlacesOf linksFull true) z ft (noL l d) (blkL Z G l d X arrs) c
      hu (tiedL Mg.more l d) ?_ hOrd hRide hNew)
  cases d with
  | true => exact (rowL_digits_full N Mg.more l hl _ _ hinj trees msgs).pubs
  | false => exact (rowL_reads_full N Mg.more l hl _ _ hinj trees msgs).pubs

end VerifiableInference.Desc.K1
