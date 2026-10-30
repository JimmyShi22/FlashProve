-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/TiePromise.lean: "NO COLLISION" OUT OF THE FIRST TABLE'S PROMISE, AND THAT A
SEGMENT'S FIRST TWO PINS ARE OPEN IN FRONT OF KIND K8'S DRAW, AT THE FULL SIZE. Statements with
their proofs; one test with code.

Main names (namespace `VerifiableInference.Desc.First.K8`).
  **`noColl_of_onQ`**: inside the promise at border k (`onQ`, Johnson/Desc/Sound/BordersQ.lean), at
    a verifier's state without a mark, where the item `pin m t` is open at that border: `Mg.noColl
    e.1 e.2` holds of every tenant e of `N.sent m t`. By the promise's third clause (`onAt`,
    Johnson/Desc/First/Borders.lean), which speaks of `sampledIn N O`; that list flat-maps `pin m t`
    to `N.sent m t`. `shown_of_onQ`: the like for `Mg.shown`, the same clause's other half.
  `drawAt l`: the number of kind K8's sub-protocol of segment l in the first chain's flat list: 14 l
    + 6; at the output head's segment (24): 343. `pinsOpenB links ps k l`: the test: both `pin l 0`
    and `pin l 1` are among the items open at border k.
  `pinsOpenB_full`: the test accepts at all twenty-five, at `Sound.linksFull` and its written list
    of places: BY LEAN'S KERNEL (`decide +kernel`). **`pins_open_full`**: so, for l ≤ 24, both are
    members.

Every "there is": none.
Limits. The closed fact is one on the table's rows at the full size's list of segments; it says
nothing of a run. `drawAt` is said again here with the text of `P1K8T.ixOf`
(Johnson/P1K8R/Tied.lean, which this file does not import): `drawAt l = ixOf l` is rfl for
whoever holds both. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersQ
import Johnson.Desc.Sound.AtDriver

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers start openSets sampledIn
  flatPlacesOf)

/-- A tenant that a segment sends at a moment whose pin is open is among the sampled tenants. -/
theorem sent_sampled (N : Numbers) (O : List Item) (m t : ℕ) (hO : Item.pin m t ∈ O)
    (e : ℕ × ℕ) (he : e ∈ N.sent m t) : e ∈ sampledIn N O :=
  List.mem_flatMap.2 ⟨_, hO, he⟩

/-- **"NO COLLISION" OUT OF THE PROMISE.** -/
theorem noColl_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k m t : ℕ)
    (a : A × Fr.E.Str) (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none)
    (hO : Item.pin m t ∈ (openSets links ps (start links))[k]?.getD []) :
    ∀ e ∈ N.sent m t, Mg.noColl e.1 e.2 (get a.1) (strsOf Fr a.2) := by
  intro e he
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · exact (h'.2.2.1 e (sent_sampled N _ m t hO e he)).2

/-- The same clause's other half. -/
theorem shown_of_onQ {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W)
    (links : List ModelPart) (ps : List Place) (get : A → P × First.S) (k m t : ℕ)
    (a : A × Fr.E.Str) (h : onQ N Mg links ps get k a) (hm : (get a.1).2.failed = none)
    (hO : Item.pin m t ∈ (openSets links ps (start links))[k]?.getD []) :
    ∀ e ∈ N.sent m t, Mg.shown e.1 e.2 (strsOf Fr a.2) := by
  intro e he
  rcases h.2 with h' | h'
  · exact absurd hm h'
  · exact (h'.2.2.1 e (sent_sampled N _ m t hO e he)).1

/-- The number of kind K8's sub-protocol of segment l in the first chain's flat list. -/
def drawAt (l : ℕ) : ℕ := if l = 24 then 343 else 14 * l + 6

/-- The test: the segment's first two pins are among the items open at border k. -/
def pinsOpenB (links : List ModelPart) (ps : List Place) (k l : ℕ) : Bool :=
  decide (Item.pin l 0 ∈ (openSets links ps (start links))[k]?.getD []) &&
    decide (Item.pin l 1 ∈ (openSets links ps (start links))[k]?.getD [])

theorem pinsOpenB_full :
    ((List.range 25).all fun l =>
      pinsOpenB linksFull (flatPlacesOf linksFull true) (drawAt l) l) = true := by
  decide +kernel

/-- **THE CLOSED FACT**: at the full size, in front of kind K8's draw of every segment, the
segment's first two pins are open. -/
theorem pins_open_full (l : ℕ) (hl : l ≤ 24) :
    Item.pin l 0 ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[drawAt l]?.getD [] ∧
      Item.pin l 1 ∈ (openSets linksFull (flatPlacesOf linksFull true)
        (start linksFull))[drawAt l]?.getD [] := by
  have h := List.all_eq_true.1 pinsOpenB_full l (List.mem_range.2 (Nat.lt_succ_of_le hl))
  unfold pinsOpenB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

end VerifiableInference.Desc.First.K8

#print axioms VerifiableInference.Desc.First.K8.sent_sampled
#print axioms VerifiableInference.Desc.First.K8.noColl_of_onQ
#print axioms VerifiableInference.Desc.First.K8.shown_of_onQ
#print axioms VerifiableInference.Desc.First.K8.pinsOpenB_full
#print axioms VerifiableInference.Desc.First.K8.pins_open_full
