-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set of files on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyOff.lean: the table of joints of the key file: what its promise and its claim say at an instance that is no record's key. The reason: premises are asked at every instance, while
the first boundary's promise and claim read the record through a default off the image of the map from records to instances: there they speak of a fixed record that has nothing to do with the instance, and may be unmeetable.
Here the record is read through an option, never through a default: the letter Reading.recOf : A → Option Rec («the stored table's record, off the chain's record»). The value meant: some rec just where the instance is rec's key; nothing elsewhere.
  FreeAt G coll     **the promise's clause on the stored table, as a definition**: there is a record off the chain's record, and the stored table has no collision at it
  not_free_off · not_on_off   proved: where recOf gives nothing (and the record bears no mark) the promise is false at every border: so every law «on the statements with the promise …» is idle there: nothing is owed
  not_rel_off       proved: where recOf gives nothing the relation is false at every witness at every border at which pinT is open (all twenty of the first chain; the shared chain's first two): so «the claim behind gives the claim in front» is idle there too
  on_gives_rec      proved: the promise (at an unmarked record) gives a record off the chain's record
So: idle, not unmeetable, off the image: provided recOf is filled by a partial inverse and not by a total one with a default. What the first boundary's fact then wants: recOf (the key of rec, the first state) = some rec: that is: the map from records to keys is one-to-one.
Behind the border at which pinT closes the claim does not name the record: there the promise alone keeps the laws idle off the image: so every later border's promise must hold FreeAt too (free₂ | free₃).
No Mathlib. Nothing on soundness.
-/
import Johnson.Desc.Key.KeyBorders

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

section
variable {XI P S Cells M Smp Rec : Type} (F : FileDescription XI) (G : Reading (P × S) Cells M Smp Rec)

/-- **The promise's clause on the stored table.** coll: the stored table has a collision at the record's seed: the configuration's. -/
def FreeAt (coll : Strs → Rec → Prop) (a : P × S) (y : Strs) : Prop := ∃ r, G.recOf a = some r ∧ ¬ coll y r

theorem not_free_off (coll : Strs → Rec → Prop) (a : P × S) (y : Strs) (h : G.recOf a = none) : ¬ FreeAt G coll a y := by
  intro ⟨r, hr, _⟩
  rw [h] at hr
  cases hr

/-- Off the image the promise is false at every border. -/
theorem not_on_off (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) (shape : S → Bool) (coll : Strs → Rec → Prop) (O : List KItem) (a : P × S) (y : Strs)
    (hm : Mg.unmarked a) (h : G.recOf a = none) : ¬ onAt F G at_ Mg shape (FreeAt G coll) O a y := by
  intro ho
  cases ho with
  | inl hn => exact hn hm
  | inr hr => exact not_free_off G coll a y h hr.2.2.1

/-- Off the image the relation is false at every witness wherever pinT is open. -/
theorem not_rel_off (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) (O : List KItem) (a : P × S) (y : Strs) (w : Wit Cells Unit M)
    (hO : KItem.pinT ∈ O) (h : G.recOf a = none) : ¬ relAt F G at_ Mg O a y w := by
  intro hr
  obtain ⟨r, hr', _⟩ : PINW G a y w := hr .pinT hO
  rw [h] at hr'
  cases hr'

/-- The promise, at an unmarked record, gives a record. -/
theorem on_gives_rec (at_ : Where) (Mg : KMeaning P S (Wit Cells Unit M)) (shape : S → Bool) (coll : Strs → Rec → Prop) (O : List KItem) (a : P × S) (y : Strs)
    (hm : Mg.unmarked a) (ho : onAt F G at_ Mg shape (FreeAt G coll) O a y) : ∃ r, G.recOf a = some r ∧ ¬ coll y r := by
  cases ho with
  | inl hn => exact absurd hm hn
  | inr hr => exact hr.2.2.1

end

end VerifiableInference.Desc.Key

#print axioms VerifiableInference.Desc.Key.not_on_off
#print axioms VerifiableInference.Desc.Key.not_rel_off
#print axioms VerifiableInference.Desc.Key.on_gives_rec
