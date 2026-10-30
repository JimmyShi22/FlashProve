-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/GoAtLater.lean: K01_law: THE BINDER hgo OF k01_later_tied (Johnson/Desc/K1/Law/LaterOne.lean) («a riding item's sentence goes back over the block's own yes, from inside the promise in front»), AT EACH OF THE FIFTY LATER PLACES, BROUGHT DOWN TO EIGHT ARMS, ONE A
CONSTRUCTOR OF First.Item THAT RIDES THERE: pinW · pile · pinI · pin · wo · constr · row · forms. No other constructor rides past any of the fifty: BY THE KERNEL, at the table's own written list.
  riderB i          the item's constructor is one of the eight
  ridersB links ps k   a test on the table: every item that is open at border k and that block k's row neither closes nor reads is such a one
  riders_full       [kernel] the test says yes at all fifty · riders_can_fail [kernel]: it says no at the block in front of a link's reads (there formsT rides)
  tableOk_full      [kernel] the table's own two tests readsOpen | rowsApart at the full list: so the rule's open set is openSets' members (openIsList · openL_iff_openSets, Johnson/Desc/Sound/SpineList.lean: CALLED IN A COPY UNDER ANOTHER NAMESPACE, Johnson/Desc/K1/Law/SpineListK1.lean)
  open_mem          what the rule has open at border k of the full list is a member of openAt linksFull ps k
  hgo_of_arms       **hgo at (l, d), to the top's binder's letter, from the eight arms.** Each arm is handed: the block's own yes · the promise in front · KeptBelow · that the item is open in front.
WHO PAYS THE ARMS: pinW: pinW_back_blind (K13/Law/SigDecodes.lean) · pile: pileBackAtLater (K1/Law/PileAtLater.lean) with readerAtCommit (K13/Law/ReaderAtCommit.lean) · pin | pinI: pin_arms
(K1/Law/PinsGoBack.lean) under SmpLeft · forms | constr: go_forms_later | constr_back_one (K1/Law/GoAtLaterForms.lean) under their named premises · row: no payer named here · wo: another layer of mgAll
(Johnson/Desc/Sound/MgAll.lean).
What is not claimed. No arm is shown here. Nothing on soundness.

-/
import Johnson.Desc.K1.Law.RowLFull
import Johnson.Desc.K1.Law.SpineListK1

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace VerifiableInference.Desc.K1
open OnBytes.Maker
open VerifiableInference.Desc.First (S ModelPart Item Pub Meaning Numbers More flatPlacesOf)
open VerifiableInference.Desc.Sound (linksFull insQ outsQ openAfter)
open VerifiableInference.Desc.K1.SL (insL outsL openIsList openL_iff_openSets rowsApart)
open VerifiableInference.Desc.K13.Law (openAt)
open IM (k1Ix)

variable {Pp W : Type}

/-- The item's constructor is one of the eight that ride past a later sending. -/
def riderB : Item → Bool
  | .pinW | .pile | .pinI | .pin _ _ | .wo _ | .constr _ _ | .row _ _ | .forms _ _ _ => true
  | _ => false

/-- A TEST ON THE TABLE: what is open at border k, and is neither closed nor read by block k's row, is of the eight. -/
def ridersB (links : List ModelPart) (ps : List Place) (k : ℕ) : Bool :=
  ((openAt links ps k).filter fun i => !(insL links ps k).contains i).all riderB

theorem riders_full : ((List.range 25).all fun l => [false, true].all fun d =>
    ridersB linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2)) = true := by
  decide +kernel

/-- **The test can fail.** -/
theorem riders_can_fail :
    ridersB linksFull (flatPlacesOf linksFull true) (14 * 3 + k1Ix 3 false + 1) = false := by
  decide +kernel

theorem tableOk_full :
    (First.readsOpen linksFull (flatPlacesOf linksFull true) (First.start linksFull) &&
      rowsApart linksFull (flatPlacesOf linksFull true) &&
      (First.start linksFull).contains Item.unmarked) = true := by
  decide +kernel

/-- What the rule has open at a border of the full list is a member of the tests' open set there. -/
theorem open_mem (k : ℕ) (hk : k ≤ (flatPlacesOf linksFull true).length) (i : Item)
    (h : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ First.start linksFull) k i) :
    i ∈ openAt linksFull (flatPlacesOf linksFull true) k := by
  have t := tableOk_full
  simp only [Bool.and_eq_true] at t
  exact (openL_iff_openSets linksFull (flatPlacesOf linksFull true) (First.start linksFull) t.1.1
    t.1.2 (List.contains_iff_mem.1 t.2) k hk i).1
    ((openIsList Item (insL linksFull (flatPlacesOf linksFull true))
      (outsL linksFull (flatPlacesOf linksFull true)) (First.start linksFull) k i).1 h)

/-- **hgo AT (l, d), FROM THE EIGHT ARMS.** B: the lot's own block there. -/
theorem hgo_of_arms (N : Numbers) (Mg : Meaning Pp W) (B : Block S Unit) (base l : ℕ)
    (hl : l < 25) (d : Bool)
    (aPinW : ∀ (x x' : Pp × S) y y' w, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' → Mg.pinW x' y' w → Mg.pinW x y w)
    (aPile : ∀ (x x' : Pp × S) y y' w, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' → Mg.pile x' y' w → Mg.pile x y w)
    (aPinI : ∀ (x x' : Pp × S) y y' w, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      Item.pinI ∈ openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) →
      Item.pinI.holds N Mg x' y' w → Item.pinI.holds N Mg x y w)
    (aPin : ∀ (x x' : Pp × S) y y' w m t, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      Item.pin m t ∈ openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) →
      (Item.pin m t).holds N Mg x' y' w → (Item.pin m t).holds N Mg x y w)
    (aWo : ∀ (x x' : Pp × S) y y' w m, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      Item.wo m ∈ openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) →
      Mg.wo m x' y' w → Mg.wo m x y w)
    (aConstr : ∀ (x x' : Pp × S) y y' w m p, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      Item.constr m p ∈ openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) →
      Mg.constr m p x' y' w → Mg.constr m p x y w)
    (aRow : ∀ (x x' : Pp × S) y y' w m c, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      Item.row m c ∈ openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) →
      Mg.row m c x' y' w → Mg.row m c x y w)
    (aForms : ∀ (x x' : Pp × S) y y' w m k r, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      Item.forms m k r ∈ openAt linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) →
      Mg.forms m k r x' y' w → Mg.forms m k r x y w) :
    ∀ (x x' : Pp × S) y y' w i, YesOf B x x' →
      InAt N Mg linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) x y →
      KeptBelow base y y' →
      openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ First.start linksFull)
        (14 * l + k1Ix l d + 2) i →
      ¬ insQ linksFull (flatPlacesOf linksFull true) (14 * l + k1Ix l d + 2) i →
      i.holds N Mg x' y' w → i.holds N Mg x y w := by
  intro x x' y y' w i hy hIn hK ho hn h
  have hk : 14 * l + k1Ix l d + 2 ≤ (flatPlacesOf linksFull true).length := by
    have e := of_decide_eq_true (List.all_eq_true.1
      (List.all_eq_true.1 k01_later_places l (List.mem_range.2 hl)) d (by cases d <;> simp))
    exact Nat.le_of_lt (List.getElem?_eq_some_iff.1 e).1
  have hi := open_mem _ hk i ho
  have hr : riderB i = true := by
    have a := List.all_eq_true.1 (List.all_eq_true.1 riders_full l (List.mem_range.2 hl)) d
      (by cases d <;> simp)
    refine List.all_eq_true.1 a i (List.mem_filter.2 ⟨hi, ?_⟩)
    rw [Bool.not_eq_true', ← Bool.not_eq_true, List.contains_iff_mem]
    exact hn
  cases i with
  | pinW => exact aPinW x x' y y' w hy hIn hK h
  | pile => exact aPile x x' y y' w hy hIn hK h
  | pinI => exact aPinI x x' y y' w hy hIn hK hi h
  | pin m t => exact aPin x x' y y' w m t hy hIn hK hi h
  | wo m => exact aWo x x' y y' w m hy hIn hK hi h
  | constr m p => exact aConstr x x' y y' w m p hy hIn hK hi h
  | row m c => exact aRow x x' y y' w m c hy hIn hK hi h
  | forms m k r => exact aForms x x' y y' w m k r hy hIn hK hi h
  | _ => exact absurd hr (by simp [riderB])

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.riders_full
#print axioms VerifiableInference.Desc.K1.tableOk_full
#print axioms VerifiableInference.Desc.K1.open_mem
#print axioms VerifiableInference.Desc.K1.hgo_of_arms
