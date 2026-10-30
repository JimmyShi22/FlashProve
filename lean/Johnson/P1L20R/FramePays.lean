-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FramePays.lean:
THE DEBT "every item that is open behind the block goes back over the step", AT THE
LINK's FRAME's 51 PLACES OF THE WRITTEN LIST, CUT DOWN TO ONE SENTENCE A FIELD OF THE MEANING.

  readsOpen_full, rowsApart_full   the table's two tests at the written list: by Lean's kernel
  open_mem          so an item that is open at a border, as the rule of the chain reads it, stands
                    in the table's computed list at that border
  partlessB_full, open_partless   BEHIND THE FRONT, BEHIND EVERY "laid" AND BEHIND EVERY "cleared"
                    NO OPEN ITEM HAS A PART OF A SEGMENT OF ITS OWN: by Lean's kernel
  items_at          so LettersRide's field "items" there, at whatever step rel: from FieldsBack
                    (Johnson/Desc/Sound/ItemsRide.lean: eight sentences, one a field) and two facts
                    on the members of the computed list: none is a part of a segment's relation that
                    "own" names; the trees that its pins name have "low"

Limits. FieldsBack, "own" and "low" are letters and premises. No soundness statement.

-/
import Johnson.P1L20R.FrameSits
import Johnson.Top.H0.Walk.FrameItemsBack
import Johnson.Desc.Sound.SpineList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1L20

open VerifiableInference.Desc (Place KindName Strs)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Part Meaning Numbers start openSets readsOpen
  flatPlacesOf)
open Johnson.Desc.First.Walk.Tied

set_option maxRecDepth 1000000 in
theorem readsOpen_full :
    readsOpen linksFull (flatPlacesOf linksFull true) (start linksFull) = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem rowsApart_full : rowsApart linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- An item that is open at a border stands in the table's computed list there. -/
theorem open_mem {k : ℕ} {i : Item} (hk : k ≤ (flatPlacesOf linksFull true).length)
    (h : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) k i) :
    i ∈ (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD [] := by
  have hu : Item.unmarked ∈ start linksFull := List.mem_append_left _ List.mem_cons_self
  have hL : i ∈ openL (insL linksFull (flatPlacesOf linksFull true))
      (outsL linksFull (flatPlacesOf linksFull true)) (start linksFull) k :=
    (openIsList Item (insL linksFull (flatPlacesOf linksFull true))
      (outsL linksFull (flatPlacesOf linksFull true)) (start linksFull) k i).1 h
  exact (openL_iff_openSets linksFull (flatPlacesOf linksFull true) (start linksFull)
    readsOpen_full rowsApart_full hu k hk i).1 hL

/-- The borders behind the frame's 51 blocks. -/
def behind51 : List ℕ :=
  1 :: ((List.range 25).map fun l => 14 * l + 1 + 1) ++ (List.range 25).map fun l => clearIx l + 1

/-- A test with code on the written list: at these borders no open item has a part. -/
def partlessB : Bool :=
  behind51.all fun k =>
    ((openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD []).all
      fun i => i.part.isNone

set_option maxRecDepth 1000000 in
theorem partlessB_full : partlessB = true := by decide +kernel

theorem behind51_le {k : ℕ} (hk : k ∈ behind51) : k ≤ (flatPlacesOf linksFull true).length := by
  rw [places_length_full]
  unfold behind51 at hk
  simp only [List.cons_append, List.mem_cons, List.mem_append, List.mem_map, List.mem_range] at hk
  rcases hk with rfl | ⟨l, hl, rfl⟩ | ⟨l, hl, rfl⟩
  · omega
  · omega
  · unfold clearIx
    split <;> omega

/-- **Behind the frame's 51 blocks no open item has a part of a segment of its own.** -/
theorem open_partless {k : ℕ} (hk : k ∈ behind51) {i : Item}
    (h : openAfter (insQ linksFull (flatPlacesOf linksFull true))
      (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) k i) :
    i.part = none := by
  have h1 := List.all_eq_true.1 (List.all_eq_true.1 partlessB_full k hk) i
    (open_mem (behind51_le hk) h)
  exact Option.isNone_iff_eq_none.1 h1

/-- **LettersRide's field "items" at the 51, from one sentence a field.** -/
theorem items_at {P W : Type} {N : Numbers} {Mg : Meaning P W} {rel : S → S → Prop} {base : ℕ}
    {In : P × S → Strs → Prop} {k : ℕ} (hk : k ∈ behind51) (own : ℕ → Part → Bool)
    (low : ℕ → Prop) (H : FieldsBack Mg own low (StepRel rel base In))
    (hO : ∀ i ∈ (openSets linksFull (flatPlacesOf linksFull true) (start linksFull))[k]?.getD [],
      notOwn own i ∧ lowItem N low i) :
    ∀ p s t y y' w i, rel s t → Stays base y y' → In (p, s) y →
      openAfter (insQ linksFull (flatPlacesOf linksFull true))
        (outsQ linksFull (flatPlacesOf linksFull true)) (· ∈ start linksFull) k i →
      i.holds N Mg (p, t) y' w → i.holds N Mg (p, s) y w :=
  items_of_fields own low H fun i hi =>
    ⟨open_partless hk hi, hO i (open_mem (behind51_le hk) hi)⟩

end P1L20

#print axioms P1L20.readsOpen_full
#print axioms P1L20.rowsApart_full
#print axioms P1L20.partlessB_full
#print axioms P1L20.open_partless
#print axioms P1L20.items_at
