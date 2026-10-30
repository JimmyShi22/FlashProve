-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/AtTableSealMgAll.lean: WHAT THE LAW OF THE FIRST CHAIN's LAST SUB-PROTOCOL (THE
SEAL) ASKS OF THE TABLE AND OF THE MEANING (RowSeal · FillSeal, AtTableSeal.lean), AT THE FIRST
TABLE's COMPOSED MEANING mgAll 𝔇 Mg (Johnson/Desc/Sound/MgAll.lean),
AT THE FULL LIST OF SEGMENTS. Four theorems.

OBJECT   the seal's row of the first table (number 357 at the full list), at mgAll's own list of
         extra public tests; mgAll's fields decodes · shown · noColl · pinW · pin · pileOne.
USER     firstEnd_tied_seat | seal_tied357's two premises hT | hF at the reference form; the kind
         "frame"'s join. fillSeal_mgAll is called in Johnson/Desc/AtSeats/Seal357AtAll.lean.

  fillSeal_mgAll   **FillSeal N (mgAll 𝔇 Mg) B O Op**, general in 𝔇 and Mg: fillSeal_sig's
                   premises WITHOUT hP: mgAll's pileOne reads no oracle's string (it is "all
                   pending rows are true" at a reader of the state and the witness): it goes back
                   by the make. The other fields by the composed meaning's own equations (rfl) and
                   the four lemmas that fillSeal_sig calls.
  seal_makes_mgAll where Mg's own list of extra public tests is empty, mgAll's list makes nothing
                   at the seal's place: the composed meaning's closed term mgMore, by the kernel.
  rowSeal_mgAll    **RowSeal N (mgAll 𝔇 Mg).more … 357 placeSeal** at the full list, in K13's
                   files' spelling (K13.Law.linksFull · First.flatPlaces true … true), from
                   Mg.more = {} and the two counts that stay (hT · hMs).
  rowSeal_mgAll'   the same in the table's files' spelling (Sound.linksFull · flatPlacesOf … true).
THE QUESTION (does a clause name one of the names that have left the table's list?):
RowSeal's one clause on public tests, pubs, says "what is open behind the seal was open in front":
it names no test; FillSeal names none. At mgAll the list is read AS STRUCK (mgMore ends in
".strike leavesName").
What is not claimed. hT | hMs at the numbers meant; hO | hOp (what is open at 357: by the kernel
at the two lists in AtTableSealRow.lean; at every lawful list in OpenSetAtEnd.lean); hI | hV. That
Mg.more = {} at the base meant. Nothing on soundness.

-/
import Johnson.Desc.K13.Law.AtTableSealDoor
import Johnson.Desc.K13.Law.AtTableSealFill
import Johnson.Desc.Sound.MgAllAt
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.K13.Law (SameBelow RowSeal FillSeal sampled_of_open placeSeal
  rowSeal_full_door)

variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
variable (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **FillSeal at the composed meaning.** -/
theorem fillSeal_mgAll (N : Numbers) (B : ℕ) (O : List Item) (Op : Item → Prop)
    (hO : ∀ i ∈ O, i = .unmarked ∨ i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne)
    (hI : N.index.1 < B) (hV : N.w.1 < B)
    (hOp : ∀ i, Op i → i = .pinW ∨ i = .pinI ∨ i = .pinV ∨ i = .pileOne) :
    FillSeal N (mgAll 𝔇 Mg) B O Op :=
  have hS : ∀ t ∈ First.sampledIn N O, t.1 < B := fun t ht => by
    rcases sampled_of_open N O hO t ht with rfl | rfl
    · exact hI
    · exact hV
  { decodes := fun x y y' h hd => decodesOf_cell 𝔇.decT x y y' (fun z => by rw [h.1]) hd
    shown := fun t ht y y' h hs => shownJT_col 𝔇.cs 𝔇.G 𝔇.ms t.1 t.2 y y' (h.2 t.1 (hS t ht)) hs
    noColl := fun t ht x y y' h hn =>
      noCollJT_col 𝔇.cs 𝔇.G 𝔇.smp 𝔇.ms t.1 t.2 x y y' (h.2 t.1 (hS t ht)) hn
    back := fun i hi x y y' w h hw => by
      rcases hOp i hi with rfl | rfl | rfl | rfl
      · exact pinWOf_cell 𝔇.decT x y' y w (fun z => by rw [h.1]) hw
      · exact pinJT_col 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms N.index.1 N.index.2 x y' y w
          (fun z => (h.2 _ hI z).symm) hw
      · exact pinJT_col 𝔇.cs 𝔇.G 𝔇.arr 𝔇.smp 𝔇.ms N.w.1 N.w.2 x y' y w
          (fun z => (h.2 _ hV z).symm) hw
      · exact hw }

/-- The composed meaning's closed list (mgMore) makes nothing at the seal's place. -/
theorem seal_makes_mgMore : (mgMore.rows K13.Law.linksFull placeSeal).makes = [] := by
  decide +kernel

/-- So does mgAll's, where Mg's own list is empty. -/
theorem seal_makes_mgAll (h : Mg.more = {}) :
    ((mgAll 𝔇 Mg).more.rows K13.Law.linksFull placeSeal).makes = [] := by
  rw [mgAll_more_closed 𝔇 Mg h]
  exact seal_makes_mgMore

/-- **RowSeal at the composed meaning, at the full list.** -/
theorem rowSeal_mgAll (h : Mg.more = {}) (N : Numbers)
    (hT : N.treesAt (First.flatPlaces true K13.Law.linksFull true)[357 + 1]? =
      N.treesAt (First.flatPlaces true K13.Law.linksFull true)[357]?)
    (hMs : N.msgsAt (First.flatPlaces true K13.Law.linksFull true)[357 + 1]? =
      N.msgsAt (First.flatPlaces true K13.Law.linksFull true)[357]?) :
    RowSeal N (mgAll 𝔇 Mg).more K13.Law.linksFull
      (First.flatPlaces true K13.Law.linksFull true) 357 placeSeal :=
  rowSeal_full_door N _ (seal_makes_mgAll 𝔇 Mg h) hT hMs

/-- The same in the table's files' spelling (Sound.linksFull · flatPlacesOf … true). -/
theorem rowSeal_mgAll' (h : Mg.more = {}) (N : Numbers)
    (hT : N.treesAt (flatPlacesOf linksFull true)[357 + 1]? =
      N.treesAt (flatPlacesOf linksFull true)[357]?)
    (hMs : N.msgsAt (flatPlacesOf linksFull true)[357 + 1]? =
      N.msgsAt (flatPlacesOf linksFull true)[357]?) :
    RowSeal N (mgAll 𝔇 Mg).more linksFull (flatPlacesOf linksFull true) 357 placeSeal :=
  rowSeal_mgAll 𝔇 Mg h N hT hMs

end VerifiableInference.Desc.Sound
