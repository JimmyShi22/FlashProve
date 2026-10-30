-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/PubHeldStep.lean: the table of joints' promise (Johnson/Desc/First/Borders.lean):
THE PUBLIC ITEMS BEHIND A BLOCK, CUT BY THE BLOCK's OWN TWO ROWS: what a
kind reads off its rows: "I keep it", "I make it", an item a lemma. It pays two premises of the
rule "the promise rides past a block" (onAt_step_held, Johnson/Desc/First/PromiseRides.lean):
hPub and hPP, at Q' := pubStep Q pr. General in the kind.

Main names:
  `tiesOf i`: the public items that are tied to an item (`pubOfItems` is its flatMap:
    `pubOfItems_eq`).
  `pubHeld_step`: pubHeld at (O, Q, a) gives pubHeld at (stepOpen O r, pubStep Q pr, b), where:
    every open public item that the row does not drop is kept · every public item tied to an open
    item that the row does not close is kept · every item that the row makes holds behind · every
    item tied to an item that the row opens holds behind.
  `pubP_step`: the like for what the open public items say beside their Bools (Meaning.pubP).
Limits. Rules over letters: each premise is the kind's files' to pay.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.PromiseRides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open VerifiableInference.Desc

/-- The public items that are tied to an item. -/
def tiesOf : Item → List Pub
  | .forms m k r => [.formsIn m k r]
  | .formsT m k r => [.formsInT m k r]
  | .total m => [.totalIn m]
  | .wo m => [.hasRow m]
  | .pinI => [.indexIs, .indexThere]
  | _ => []

theorem pubOfItems_eq (O : List Item) : pubOfItems O = O.flatMap tiesOf := by
  unfold pubOfItems
  refine congrArg (fun f => O.flatMap f) (funext fun i => ?_)
  cases i <;> rfl

section
variable {P W : Type} (Mg : Meaning P W)

/-- **The public items' Bools behind a block, by the block's two rows.** -/
theorem pubHeld_step (O : List Item) (Q : List Pub) (r : BlockRow) (pr : PubRow) (a b : P × S)
    (h : pubHeld Mg O Q a = true)
    (hkeepQ : ∀ q ∈ Q, pr.drops.contains q = false → Mg.pub q a = true → Mg.pub q b = true)
    (hkeepO : ∀ i ∈ O, r.ins.contains i = false → ∀ q ∈ tiesOf i, Mg.pub q a = true →
      Mg.pub q b = true)
    (hmakeQ : ∀ q ∈ pr.makes, Mg.pub q b = true)
    (hmakeO : ∀ i ∈ r.outs, ∀ q ∈ tiesOf i, Mg.pub q b = true) :
    pubHeld Mg (stepOpen O r) (pubStep Q pr) b = true := by
  unfold pubHeld at h ⊢
  have c := List.all_eq_true.1 h
  refine List.all_eq_true.2 fun q hq => ?_
  rcases List.mem_append.1 hq with hq | hq
  · unfold pubStep at hq
    rcases List.mem_append.1 hq with hq | hq
    · obtain ⟨g1, g2⟩ := List.mem_filter.1 hq
      exact hkeepQ q g1 (by simpa using g2) (c q (List.mem_append_left _ g1))
    · exact hmakeQ q (List.mem_filter.1 hq).1
  · rw [pubOfItems_eq] at hq
    obtain ⟨i, hiO, ht⟩ := List.mem_flatMap.1 hq
    unfold stepOpen at hiO
    rcases List.mem_append.1 hiO with hiO | hiO
    · obtain ⟨g1, g2⟩ := List.mem_filter.1 hiO
      refine hkeepO i g1 (by simpa using g2) q ht (c q (List.mem_append_right _ ?_))
      rw [pubOfItems_eq]
      exact List.mem_flatMap.2 ⟨i, g1, ht⟩
    · exact hmakeO i (List.mem_filter.1 hiO).1 q ht

/-- **What the open public items say beside their Bools, behind a block.** -/
theorem pubP_step (Q : List Pub) (pr : PubRow) (a b : P × S) (h : ∀ q ∈ Q, Mg.pubP q a)
    (hkeep : ∀ q ∈ Q, pr.drops.contains q = false → Mg.pubP q a → Mg.pubP q b)
    (hmake : ∀ q ∈ pr.makes, Mg.pubP q b) : ∀ q ∈ pubStep Q pr, Mg.pubP q b := by
  intro q hq
  unfold pubStep at hq
  rcases List.mem_append.1 hq with hq | hq
  · obtain ⟨g1, g2⟩ := List.mem_filter.1 hq
    exact hkeep q g1 (by simpa using g2) (h q g1)
  · exact hmake q (List.mem_filter.1 hq).1

end

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.pubOfItems_eq
#print axioms VerifiableInference.Desc.First.pubHeld_step
#print axioms VerifiableInference.Desc.First.pubP_step
