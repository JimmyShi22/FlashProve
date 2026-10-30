-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Riders/PlanFull.lean: LEAN's KERNEL's WORD, AT THE FULL SIZE's LISTS OF SEGMENTS AND
PLACES, ON THE TESTS ON THE PUBLIC PARAMETERS UNDER WHICH K4's ROW's LINES ON THE PUBLIC ITEMS
STAND, as far as these tests are closed terms, AT THE WIDER MEANING's OWN CLOSED DOOR (`door8`).
Definitions, statements and proofs: evaluation by the kernel.

  `door8`: THE WIDER MEANING's OWN CLOSED DOOR (`moreWideAll`, Johnson/Desc/Sound/MgWide.lean: the
    composed meaning's rows before the names that leave are struck, merged with these names'
    authors' own rows; `moreW_base`: it is the field more of the wider meaning over the closed base,
    by rfl). `doorOthers`: the same without K4's own second layer's two: for the negative tests.
  `k4DoorFit`: a test on a door's filling: at every place of K4's the door makes "K8.funsThird" of
    its segment and no other name, and lets the row ask "pile.room", "K4.rowsBare" and "K4.lookLeft"
    of its segment. `door_of_fit`: what a yes gives at a place of K4's.
  BY THE KERNEL, TRUE. FOUR READ NO DOOR (the table's written lists alone): `k4_next_full` ·
    `k4_tied_full` · `k4_obj_full` · `k4_places_full`. FIVE READ `door8` AND PAY SEVEN FIELDS OF
    `K4RowPlan` (fit · pub · askRoom · askLeft · askBare · only · openAll): `pub_fit_full` (the
    table's own test: what a row asks is open in front of it, nothing is made twice …) ·
    `k4_pub_full` (whatever is open across K4's sub-protocol is dropped by the row, or of a sort
    that our laws carry) · `k4_door_full` · `k4_only_full` · `k4_openAll_full`. (`k4_places_full`:
    twelve of the list's places are K4's: so no test above is true for want of a place.) AT ANOTHER
    TERM: `pub_fit_order`: pubFit with K4's second layer's door merged last (the positive twin of
    `pub_fit_noMaker`: that negative test turns the makers' rows alone).
  NEGATIVE TESTS, BY THE KERNEL, FALSE: `pub_fit_noMaker`: with the makers' rows of K4's second
    layer's four names struck, pubFit rejects · `k4_openAll_others`: without K4's second layer's
    door the six items are not all open · `k4_door_others`: nor does the row ask our names ·
    `k4_door_noMaker`: with every row's makes struck at `door8` the test on the door rejects (no
    control: the outcome is fixed by the texts: the test asks for one make at a place of K4's, and
    none is left): its clause on what the door makes can fail by itself (`noMaker` turns a row's
    makes alone; the three clauses on the row's asks read the row as at `door8`, where they pass:
    `k4_door_full`) ·
    `k4_door_small`, `k4_openAll_small`: AT THE COMPOSED MEANING's OWN SMALL DOOR (`moreAll`) the
    test on the door and the test on the six items REJECT (each says "not at all twelve places"; the
    first rejects already at its clause on what the door makes, which is no premise of K4's row) ·
    `k4_askRoom_small`, `k4_openAll_small_each`: SHARPER: AT THAT SMALL DOOR, AT EACH OF K4's TWELVE
    PLACES, the row does not ask "pile.room", and the six items are not all open: there the fields
    askRoom and openAll of `K4RowPlan` are false at every place: K4's row's premises have no member
    · `k4_next_reversed`, `k4_obj_reversed`: at the list of places read backward two tests on the
    table reject · `k4_pub_stranger`: with one strange name laid open at the chain's start, k4PubFit
    rejects.

Limits. WHAT THESE ROWS PAY IS THE TABLE's BOOK-KEEPING AT TWO WRITTEN LISTS: that another author's
sub-protocol MAKES or KEEPS a name which K4's row asks is a law of that author's, not shown here.
The names that only carry a fact on every reached
state across many authors' sub-protocols HAVE LEFT the composed meaning's door: THIRTEEN (the
weights' one · the proximity test's door's four · the pile's three · "pile.room" · "frame.liveIs" ·
"K8.lay7" · "K8.onThird" · "K8.funsThird"), and four conjuncts of "in order": a theorem here that
spends, keeps or makes one of them stands at a WIDER meaning than the composed one (a bridge's
side), and is carried to it by a bridge under facts on reached states that are owed. AT THE TABLE's
ROWS AND THE LAYERS' DOORS AS IMPORTED: a later layer with a door turns `door8`: the five rows that
read it, and the negative tests at a door, are owed anew. k4TiedFit and k4OnlyFit have no negative
test. The tests that read the public parameters' numbers or the list of what each
sub-protocol tells (k4ToldFit · bookFit · fenceFit) stand elsewhere. The full size alone. K04_law,
the law of K4's sub-protocol itself, IS NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Riders.KeepsOfMeans
import Johnson.Road.K4.Riders.PlanTests
import Johnson.Road.K4.Riders.KeptNames
import Johnson.Road.K4.Riders.MoreFront
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.Att.Door.Door
import Johnson.Desc.Sound.MgWide

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Riders

open OnBytes.Road.K4.Rec (openAllB)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (ModelPart More MoreName pubFit flatPlacesOf rowMore weightsMore)
open VerifiableInference.Desc.First.Look (liveMore)
open VerifiableInference.Desc.First.FillK4 (k4NextFit isK4At)
open VerifiableInference.Desc.First.FillSent (sentMore sent1More)
open VerifiableInference.Desc.First.FillBare (leftMore bareName leftName)
open VerifiableInference.Desc.K12.Door (k12More shapesMore)
open VerifiableInference.Desc.K13.Law (wSitsMore)
open VerifiableInference.Desc.Sound (linksFull moreExtra)

/-- The wider door without K4's own second layer's two: for the negative tests. -/
def doorOthers : More :=
  ((((({} : More).merge rowMore).merge sent1More).merge H2K5.Door.more).merge wSitsMore).merge
    moreExtra

/-- The wider meaning's own closed door (Johnson/Desc/Sound/MgWide.lean: moreW_base: it is the wider
meaning's field more over the closed base, by rfl). -/
abbrev door8 : More := VerifiableInference.Desc.Sound.moreWideAll

/-- A filling with its makers' rows struck. -/
def noMaker (M : More) : More where
  rows links p := { M.rows links p with makes := [] }
  start := M.start

/-- A test on a door's filling, at every place of K4's. -/
def k4DoorFit (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  ps.all fun pl =>
    !isK4At links pl ||
      ((M.rows links pl).makes == [(some (pl.link.getD 0), "K8.funsThird")] &&
        (M.rows links pl).asks.contains (roomName (pl.link.getD 0)) &&
        (M.rows links pl).asks.contains (bareName (pl.link.getD 0)) &&
        (M.rows links pl).asks.contains (leftName (pl.link.getD 0)))

/-- What an accept gives at a place of K4's. -/
theorem door_of_fit {M : More} {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}
    (H : AtK4 links ps k m pl) (h : k4DoorFit M links ps = true) :
    (M.rows links pl).makes = [(some m, "K8.funsThird")] ∧ roomName m ∈ (M.rows links pl).asks ∧
      bareName m ∈ (M.rows links pl).asks ∧ leftName m ∈ (M.rows links pl).asks := by
  have hm : pl ∈ ps := List.mem_of_getElem? H.here
  have h1 := List.all_eq_true.1 h pl hm
  simp only [isK4At_of H, Bool.not_true, Bool.false_or, H.link, Option.getD_some,
    Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

set_option maxRecDepth 1000000 in
theorem k4_next_full : k4NextFit linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_tied_full : k4TiedFit linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pub_fit_full : pubFit door8 linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_pub_full : k4PubFit restNames door8 linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_door_full : k4DoorFit door8 linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_only_full : k4OnlyFit door8 linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_obj_full : k4ObjFit linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_openAll_full : k4OpenAllFit door8 linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_openAll_others :
    k4OpenAllFit doorOthers linksFull (flatPlacesOf linksFull true) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The tests above begin "at every place of K4's": there are twelve such places. -/
theorem k4_places_full :
    ((flatPlacesOf linksFull true).filter (isK4At linksFull)).length = 12 := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pub_fit_order :
    pubFit (doorOthers.merge (sentMore.merge leftMore)) linksFull
      (flatPlacesOf linksFull true) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_door_others : k4DoorFit doorOthers linksFull (flatPlacesOf linksFull true) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_next_reversed : k4NextFit linksFull (flatPlacesOf linksFull true).reverse = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_obj_reversed : k4ObjFit linksFull (flatPlacesOf linksFull true).reverse = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_door_noMaker :
    k4DoorFit (noMaker door8) linksFull (flatPlacesOf linksFull true) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_door_small :
    k4DoorFit VerifiableInference.Desc.Sound.moreAll linksFull (flatPlacesOf linksFull true) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_openAll_small :
    k4OpenAllFit VerifiableInference.Desc.Sound.moreAll linksFull (flatPlacesOf linksFull true) =
      false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_askRoom_small :
    ((flatPlacesOf linksFull true).all fun pl => !isK4At linksFull pl ||
      !((VerifiableInference.Desc.Sound.moreAll.rows linksFull pl).asks.contains
        (roomName (pl.link.getD 0)))) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_openAll_small_each :
    atK4s linksFull (flatPlacesOf linksFull true) (fun k m =>
      !openAllB VerifiableInference.Desc.Sound.moreAll linksFull (flatPlacesOf linksFull true) k
        m) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem pub_fit_noMaker :
    pubFit (doorOthers.merge (noMaker (sentMore.merge leftMore))) linksFull
      (flatPlacesOf linksFull true) = false := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem k4_pub_stranger :
    k4PubFit restNames (door8.merge { start := [(none, "a.stranger")] }) linksFull
      (flatPlacesOf linksFull true) = false := by
  decide +kernel

end OnBytes.Road.K4.Riders

#print axioms OnBytes.Road.K4.Riders.door_of_fit
#print axioms OnBytes.Road.K4.Riders.k4_next_full
#print axioms OnBytes.Road.K4.Riders.k4_tied_full
#print axioms OnBytes.Road.K4.Riders.pub_fit_full
#print axioms OnBytes.Road.K4.Riders.k4_pub_full
#print axioms OnBytes.Road.K4.Riders.k4_door_full
#print axioms OnBytes.Road.K4.Riders.k4_only_full
#print axioms OnBytes.Road.K4.Riders.k4_obj_full
#print axioms OnBytes.Road.K4.Riders.k4_openAll_full
#print axioms OnBytes.Road.K4.Riders.k4_openAll_others
#print axioms OnBytes.Road.K4.Riders.k4_places_full
#print axioms OnBytes.Road.K4.Riders.pub_fit_order
#print axioms OnBytes.Road.K4.Riders.k4_door_others
#print axioms OnBytes.Road.K4.Riders.k4_next_reversed
#print axioms OnBytes.Road.K4.Riders.k4_obj_reversed
#print axioms OnBytes.Road.K4.Riders.k4_door_noMaker
#print axioms OnBytes.Road.K4.Riders.k4_door_small
#print axioms OnBytes.Road.K4.Riders.k4_openAll_small
#print axioms OnBytes.Road.K4.Riders.k4_askRoom_small
#print axioms OnBytes.Road.K4.Riders.k4_openAll_small_each
#print axioms OnBytes.Road.K4.Riders.pub_fit_noMaker
#print axioms OnBytes.Road.K4.Riders.k4_pub_stranger
