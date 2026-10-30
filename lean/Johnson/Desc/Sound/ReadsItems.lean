-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/ReadsItems.lean: "EVERY RIDER's SENTENCE READS ONLY WHAT THE TABLE BOOKS", ITEM
BY ITEM: SO THAT EACH KIND's OWN LAW FOR A SORT CAN BE LAID IN AS IT STANDS. Two definitions, eight
theorems.

Why. `ReadsOkAtQR … k` (Johnson/Desc/Sound/BordersSidesOnR.lean) speaks of all items that ride past
border k at once. The laws that pay it lie in three forms: `ReadsAt` under no condition (the forms'
sorts, the pins' sorts), `ReadsAt` under a condition, and the clause itself at one sort (the pending
rows' two sorts, in Johnson/Desc/K13/Law/ReadsK13R.lean). Here the clause at ONE item has a name,
and the three forms meet in it.

What is said. `ReadsItemQR … k i`: the clause of `ReadsOkAtQR` at the item i. `readsOkAtQR_iff`: the
whole is the clause at every item. `readsOkAtQR_of_items`: it is enough at the members of a list
that holds every rider at k. `readsItem_of_readsAt`: from `ReadsAt` under no condition at the
table's own `Item.reads`. `readsItem_of_readsAtR`, `readsAtR_of_readsItem`: to and from `ReadsAt`
under the condition of `readsOkAtR_of_fit`. At `mgAll 𝔇 Mg`: `readsItem_pinW`, `readsItem_pins`,
`readsItem_unmarked`.

Limits. A joining of forms. Nothing on soundness. It pays no sort that had no law.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.Sound.ReadsAtMg
import Johnson.Desc.Sound.ReadsFitLawR

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker Fo.Peel Cb Johnson.Pack OnBytes.Slice
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Comp start)

section
variable {A P Cells Tok : Type} {Fr : Frame} (arr : ℕ → ℕ → ℕ) (N : Numbers)
  (Mg : Meaning P (Wit Cells Tok MsgT)) (links : List ModelPart) (ps : List Place)
  (get : A → P × First.S) (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)

/-- **The clause of `ReadsOkAtQR` at one item.** -/
def ReadsItemQR (i : Item) : Prop :=
  ∀ (a : A × Fr.E.Str) (w w' : Wit Cells Tok MsgT), onQ N Mg links ps get k a → Rch k a →
    (get a.1).2.failed = none →
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
    (∀ c ∈ i.reads arr N links, sameQ c w w') → meansQ N Mg get i a w → meansQ N Mg get i a w'

theorem readsOkAtQR_iff :
    ReadsOkAtQR (Fr := Fr) arr N Mg links ps get Rch k ↔
      ∀ i, ReadsItemQR arr N Mg links ps get Rch k i := Iff.rfl

/-- It is enough at the members of a list that holds every rider. -/
theorem readsOkAtQR_of_items (items : List Item)
    (hI : ∀ i, openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i →
      ¬ insQ links ps k i → i ∈ items)
    (h : ∀ i ∈ items, ReadsItemQR arr N Mg links ps get Rch k i) :
    ReadsOkAtQR (Fr := Fr) arr N Mg links ps get Rch k :=
  fun i a w w' ha hr hm ho hn hc hw => h i (hI i ho hn) a w w' ha hr hm ho hn hc hw

/-- From a law under no condition. -/
theorem readsItem_of_readsAt (i : Item)
    (h : ReadsAt (fun _ _ => True) (fun j => j.reads arr N links) N Mg i) :
    ReadsItemQR arr N Mg links ps get Rch k i :=
  fun a w w' _ _ _ _ _ hc hw => h (get a.1) (strsOf Fr a.2) w w' trivial hc hw

/-- The condition under which `readsOkAtR_of_fit` asks a law. -/
def fenceR (i : Item) (b : P × First.S) (y : Strs) : Prop :=
  b.2.failed = none ∧
    openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i ∧ ¬ insQ links ps k i ∧
    ∃ a : A × Fr.E.Str, get a.1 = b ∧ strsOf Fr a.2 = y ∧ onQ N Mg links ps get k a ∧ Rch k a

theorem readsItem_of_readsAtR (i : Item)
    (h : ReadsAt (fenceR N Mg links ps get Rch k i) (fun j => j.reads arr N links) N Mg i) :
    ReadsItemQR arr N Mg links ps get Rch k i :=
  fun a w w' ha hr hm ho hn hc hw =>
    h (get a.1) (strsOf Fr a.2) w w' ⟨hm, ho, hn, a, rfl, rfl, ha, hr⟩ hc hw

theorem readsAtR_of_readsItem (i : Item) (h : ReadsItemQR arr N Mg links ps get Rch k i) :
    ReadsAt (fenceR N Mg links ps get Rch k i) (fun j => j.reads arr N links) N Mg i := by
  rintro b y w w' ⟨hm, ho, hn, a, rfl, rfl, ha, hr⟩ hc hw
  exact h a w w' ha hr hm ho hn hc hw

end

section
variable {A Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public} {Fr : Frame}
  (𝔇 : MgData Xi P Tok rows cols nR X) (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))
  (links : List ModelPart) (ps : List Place) (get : A → P × First.S)
  (Rch : ℕ → A × Fr.E.Str → Prop) (k : ℕ)

theorem readsItem_pinW : ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k .pinW :=
  readsItem_of_readsAt _ _ _ _ _ _ _ _ _ (readsAt_pinW 𝔇 Mg links)

theorem readsItem_pins (i : Item) (hi : pinsSort i = true) :
    ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k i :=
  readsItem_of_readsAt _ _ _ _ _ _ _ _ _ (readsAt_pins 𝔇 Mg links i hi)

theorem readsItem_unmarked : ReadsItemQR 𝔇.arr 𝔇.N (mgAll 𝔇 Mg) links ps get Rch k .unmarked :=
  readsItem_of_readsAt _ _ _ _ _ _ _ _ _ (readsAt_unmarked 𝔇 Mg links)

end

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.readsOkAtQR_of_items
#print axioms VerifiableInference.Desc.Sound.readsItem_of_readsAtR
#print axioms VerifiableInference.Desc.Sound.readsAtR_of_readsItem
#print axioms VerifiableInference.Desc.Sound.readsItem_pins
