-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/DoorAtPlus13.lean: the list of extra
public tests of the wider meaning `plus13 (d13 Dm) dk (mgAll Dm Mg₀)`, as a closed term, and facts
on it at K1's fifty later places of the full size, by evaluation in Lean's kernel.
  `mwMore`, `plus13_more_closed`   the closed term; it is the wider meaning's `more` where
                    `Mg₀.more` is the empty one
  `noForms_mw`, `noForms_plus13`   [kernel] that list makes no `formsIn`: the field `noForms` of
                    `BoolsK1` (Johnson/Desc/K1/Law/CallsG.lean), to the letter
  `openB`, `fitsOpen_mw`, `fitsOpen_plus13`   [kernel] the name "K12.bookFits" is open in front of
                    each of the fifty: the field `fitsOpen`, to the letter, at fI := that name
  `doorTests_fail`  [kernel] the two tests can fail
NOT HERE: a fact on the name "K9.groupIs" of a segment. That name is in none of the lists that are
merged into `mwMore`, so no item of that name is open there. `BoolsK1` has no field on it: the
sentence on the open link's group comes by "in order".
The recursion limit is raised in this file (maxRecDepth 1000000), as in FormsAtFifty.lean:
for the elaboration of the kernel's evaluations alone.
What is not claimed. That the table is right. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.FormsAtFifty
import Johnson.Desc.K1.Law.LaterOne
import Johnson.Desc.K13.Law.BridgeK13

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open Cb Johnson.Pack
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf weightsMore)
open VerifiableInference.Desc.Sound (linksFull MsgT MgData CellsQ mgAll d13 mgMore
  mgAll_more_closed)
open VerifiableInference.Desc.K13.Law (openAt plus13 k13Asks pileMasksMore pileWithinMore
  oneRowMore)
open VerifiableInference.Desc.K12.Door (K12Data k12More shapesMore)
open IM (k1Ix)

/-- **The closed term**: the composed meaning's closed list, with the three struck layers' lists
merged in again, in the layers' order. -/
def mwMore : More :=
  ((mgMore.merge (k12More.merge shapesMore)).merge weightsMore).merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore)))

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

theorem plus13_more_closed (h : Mg₀.more = {}) :
    (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more = mwMore := by
  show ((((mgAll Dm Mg₀).more.merge (k12More.merge shapesMore)).merge weightsMore).merge
    (k13Asks.merge (pileMasksMore.merge (pileWithinMore.merge oneRowMore)))) = mwMore
  rw [mgAll_more_closed Dm Mg₀ h]
  rfl

end

/-- The item stands in the open public set in front of sub-protocol k, or is tied to an item that is
open there. -/
def openB (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) (q : Pub) : Bool :=
  ((First.pubSets M links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k)).contains q

theorem open_of {M : More} {links : List ModelPart} {ps : List Place} {k : ℕ} {q : Pub}
    (h : openB M links ps k q = true) :
    q ∈ (First.pubSets M links ps)[k]?.getD [] ++ First.pubOfItems (openAt links ps k) :=
  List.contains_iff_mem.1 h

theorem noForms_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    noFormsB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)) = true := by
  decide +kernel

theorem fitsOpen_mw : ((List.range 25).all fun l => [false, true].all fun d =>
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)
      (.more none "K12.bookFits")) = true := by
  decide +kernel

/-- **The tests can fail**: a name that no list holds is not open; and at the composed meaning's own
closed list, from which the name has been struck, "K12.bookFits" is not open. -/
theorem doorTests_fail :
    openB mwMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (.more none "K12.bookFit") = false ∧
    openB mgMore linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 true + 2)
      (.more none "K12.bookFits") = false := by
  decide +kernel

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (Dm : MgData Xi P Tok rows cols nR X) (dk : K12Data)
  (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **`BoolsK1.noForms`, to the letter**, at the wider meaning's own list. -/
theorem noForms_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool,
    noFormsB (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull (flatPlacesOf linksFull true)
      (noL l d) = true := by
  intro l hl d
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact List.all_eq_true.1 (List.all_eq_true.1 noForms_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp)

/-- **`BoolsK1.fitsOpen`, to the letter**, at fI := the name "K12.bookFits". -/
theorem fitsOpen_plus13 (h : Mg₀.more = {}) : ∀ l, l < 25 → ∀ d : Bool,
    Pub.more none "K12.bookFits" ∈
      (First.pubSets (plus13 (d13 Dm) dk (mgAll Dm Mg₀)).more linksFull
        (flatPlacesOf linksFull true))[noL l d]?.getD [] ++
      First.pubOfItems (openAt linksFull (flatPlacesOf linksFull true) (noL l d)) := by
  intro l hl d
  rw [plus13_more_closed Dm dk Mg₀ h]
  exact open_of (List.all_eq_true.1 (List.all_eq_true.1 fitsOpen_mw l (List.mem_range.2 hl)) d
    (by cases d <;> simp))

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.plus13_more_closed
#print axioms VerifiableInference.Desc.K1.noForms_plus13
#print axioms VerifiableInference.Desc.K1.fitsOpen_plus13
#print axioms VerifiableInference.Desc.K1.doorTests_fail
