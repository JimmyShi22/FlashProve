-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/ShapeDoorMore.lean: WHETHER ONE OF THE FIRST TABLE'S OWN PUBLIC
ITEMS IS OPEN AT A BORDER DOES NOT HANG ON THE LIST OF EXTRA PUBLIC TESTS; SO "evalLaid" IS OPEN AT
THE FIRST CHAIN'S LAST BORDER, AT THE FULL SIZE'S WRITTEN LISTS, AT EVERY SUCH LIST. Statements with
their proofs; one test with code. It pays the field laidOpen of `DoorStays`
(Johnson/Desc/Last/ShapeDoorFold.lean) at every meaning.



A list of extra tests (`First.More`) adds NAMED
items alone to a row's makes and drops. Here that is a theorem, and the evaluation is at the empty
list. The file does not import the composed meaning.

Main names (namespace `VerifiableInference.Desc.Last`).
  `mem_pubStep`: q is open behind a sub-protocol iff it was open and is not dropped, or is made.
    `own_mem_plus`, `own_step_iff`, `own_sets_iff`: a step, and all borders, at two lists M, M':
    alike on an item q that is no `moreItem`.
  **`own_open_iff q hq M M' links ps k`**: q ∈ `(pubSets M links ps)[k]?.getD []` ↔ q ∈ `(pubSets M'
    links ps)[k]?.getD []`, for q with hq : ∀ x, q ≠ `moreItem x`. GENERAL IN links, ps, k.
  `laidOpenB M links ps`: the test. `laidOpenB_full`: it accepts at M := {}, `Sound.linksFull` and
    its written list of places: BY LEAN'S KERNEL. **`laid_open_any M`**: the membership, AT EVERY M.

Limits. Facts on the table's text; they say nothing of a run. Of a NAMED extra item nothing is said.
Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.Borders
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Last
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound (linksFull)
open VerifiableInference.Desc.First (ModelPart Pub More MoreRow MoreName PubRow pubStep pubSetsBy pubSets
  pubRowM pubRowOf pubStartM pubStart moreItem flatPlacesOf)

/-- What is open behind a sub-protocol: what was open and is not dropped, and what is made. -/
theorem mem_pubStep (q : Pub) (Q : List Pub) (r : PubRow) :
    q ∈ pubStep Q r ↔ (q ∈ Q ∧ q ∉ r.drops) ∨ q ∈ r.makes := by
  have hc : ∀ l : List Pub, ((!l.contains q) = true) ↔ q ∉ l := fun l => by simp
  unfold pubStep
  dsimp only
  simp only [List.mem_append, List.mem_filter, hc]
  constructor
  · rintro (h | ⟨h, -⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl h
    · by_cases k : q ∈ Q ∧ q ∉ r.drops
      · exact Or.inl k
      · exact Or.inr ⟨h, k⟩

/-- One of the table's own items is no member of a list of named extra items. -/
theorem own_mem_plus (q : Pub) (hq : ∀ x, q ≠ moreItem x) (l : List Pub) (n : List MoreName) :
    q ∈ l ++ n.map moreItem ↔ q ∈ l := by
  simp only [List.mem_append, List.mem_map]
  constructor
  · rintro (h | ⟨x, -, e⟩)
    · exact h
    · exact absurd e.symm (hq x)
  · exact Or.inl

/-- A step of the table, at two lists of extra tests: alike on the table's own items. -/
theorem own_step_iff (q : Pub) (hq : ∀ x, q ≠ moreItem x) (r : PubRow) (m m' : MoreRow)
    (Q Q' : List Pub) (h : q ∈ Q ↔ q ∈ Q') :
    q ∈ pubStep Q (r.plus m) ↔ q ∈ pubStep Q' (r.plus m') := by
  rw [mem_pubStep, mem_pubStep]
  simp only [PubRow.plus, own_mem_plus q hq, h]

/-- All borders. -/
theorem own_sets_iff (q : Pub) (hq : ∀ x, q ≠ moreItem x) (M M' : More) (links : List ModelPart) :
    ∀ (ps : List Place) (Q Q' : List Pub), (q ∈ Q ↔ q ∈ Q') → ∀ k : ℕ,
      (q ∈ (pubSetsBy (pubRowM M links) ps Q)[k]?.getD [] ↔
        q ∈ (pubSetsBy (pubRowM M' links) ps Q')[k]?.getD [])
  | [], Q, Q', h, 0 => by simpa [pubSetsBy] using h
  | [], Q, Q', _, k + 1 => by simp [pubSetsBy]
  | p :: ps, Q, Q', h, 0 => by simpa [pubSetsBy] using h
  | p :: ps, Q, Q', h, k + 1 => by
    simp only [pubSetsBy, List.getElem?_cons_succ]
    exact own_sets_iff q hq M M' links ps _ _
      (own_step_iff q hq (pubRowOf links p) (M.rows links p) (M'.rows links p) Q Q' h) k

/-- **WHETHER ONE OF THE TABLE's OWN PUBLIC ITEMS IS OPEN AT A BORDER DOES NOT HANG ON THE LIST OF
EXTRA PUBLIC TESTS.** -/
theorem own_open_iff (q : Pub) (hq : ∀ x, q ≠ moreItem x) (M M' : More) (links : List ModelPart)
    (ps : List Place) (k : ℕ) :
    q ∈ (pubSets M links ps)[k]?.getD [] ↔ q ∈ (pubSets M' links ps)[k]?.getD [] :=
  own_sets_iff q hq M M' links ps _ _
    ((own_mem_plus q hq pubStart M.start).trans (own_mem_plus q hq pubStart M'.start).symm) k

/-- The test: the table's own item "evalLaid" is among the public items open at the last border. -/
def laidOpenB (M : More) (links : List ModelPart) (ps : List Place) : Bool :=
  decide (Pub.evalLaid ∈ (pubSets M links ps)[ps.length]?.getD [])

theorem laidOpenB_full : laidOpenB {} linksFull (flatPlacesOf linksFull true) = true := by
  decide +kernel

/-- **"evalLaid" IS OPEN AT THE LAST BORDER, AT THE FULL SIZE's WRITTEN LISTS, AT EVERY LIST OF
EXTRA PUBLIC TESTS.** -/
theorem laid_open_any (M : More) :
    Pub.evalLaid ∈ (pubSets M linksFull (flatPlacesOf linksFull true))[
      (flatPlacesOf linksFull true).length]?.getD [] := by
  have h := laidOpenB_full
  unfold laidOpenB at h
  exact (own_open_iff .evalLaid (fun x e => by unfold moreItem at e; cases e) M {} _ _ _).2
    (of_decide_eq_true h)

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.mem_pubStep
#print axioms VerifiableInference.Desc.Last.own_mem_plus
#print axioms VerifiableInference.Desc.Last.own_step_iff
#print axioms VerifiableInference.Desc.Last.own_sets_iff
#print axioms VerifiableInference.Desc.Last.own_open_iff
#print axioms VerifiableInference.Desc.Last.laidOpenB_full
#print axioms VerifiableInference.Desc.Last.laid_open_any
