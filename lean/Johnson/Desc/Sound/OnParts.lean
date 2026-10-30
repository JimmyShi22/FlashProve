-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/OnParts.lean: THE PROMISE OF THE FIRST CHAIN'S TABLE OF JOINTS AT A BORDER, AT A
RECORD WITHOUT A MARK, CLAUSE BY CLAUSE: so that a block's first tie can take a clause out of it and
its second tie can be paid a clause at a time. Two names, one structure, four lemmas.

What is said. `openQ`, `pubQ`: the items and the public items that are open at border k.
  `OnParts k a`: the nine clauses of `onAt`
    (Johnson/Desc/First/Borders.lean) behind "the stored table decodes" at a record without a mark,
    each a field: shape, rows, members, order, pub, book, samples, shown, pubP.
  `onParts_of_on`: the promise at a record without a mark gives them.
  `on_of_parts`: "decodes" and the nine give the promise.
  `asks_open`: where the test `pubFitBy` on the promise's table says yes, whatever the row of the
    block at number k asks is open at border k. `asked_of_on`: so the promise in front of a block,
    at a record without a mark, gives every public item that the block's row asks.

Limits. Unfoldings of the table's own text; nothing is said of any block. `pubFit`'s yes is a
premise: a test on the table at concrete lists. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.BordersQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.First (ModelPart Item Meaning Numbers Pub PubRow start onAt openSets pubSets
  shapeAt rowsHeld membersHeld pubHeld samplesHeld sampledIn pubOfItems pubFitBy pubSetsBy pubStep
  pubFit pubRowOf pubRowM pubStartM More bookAt)

/-- The items that are open at border k. -/
def openQ (links : List ModelPart) (ps : List Place) (k : ℕ) : List Item :=
  (openSets links ps (start links))[k]?.getD []

/-- The public items that are open at border k, at a filling M of the table's door. -/
def pubQ (M : More) (links : List ModelPart) (ps : List Place) (k : ℕ) : List Pub :=
  (pubSets M links ps)[k]?.getD []

section
variable {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
  (ps : List Place) (get : A → P × First.S)

/-- **The promise at border k, at a record without a mark, behind "decodes": clause by clause.** -/
structure OnParts (k : ℕ) (a : A × Fr.E.Str) : Prop where
  shape : shapeAt links ps[k]? (get a.1).2 = true
  rows : rowsHeld N (openQ links ps k) (get a.1).2 = true
  members : membersHeld N (openQ links ps k) (get a.1).2 = true
  order : Mg.inOrder (get a.1) = true
  pub : ∀ q ∈ pubQ Mg.more links ps k ++ pubOfItems (openQ links ps k), Mg.pub q (get a.1) = true
  book : bookAt N ps[k]? (get a.1).2 = true
  samples : ∀ x ∈ sampledIn N (openQ links ps k), Mg.held x.1 x.2 (get a.1) = true
  shown : ∀ x ∈ sampledIn N (openQ links ps k),
    Mg.shown x.1 x.2 (strsOf Fr a.2) ∧ Mg.noColl x.1 x.2 (get a.1) (strsOf Fr a.2)
  pubP : ∀ q ∈ pubQ Mg.more links ps k, Mg.pubP q (get a.1)

theorem onParts_of_on (k : ℕ) (a : A × Fr.E.Str) (h : onQ N Mg links ps get k a)
    (hm : (get a.1).2.failed = none) : OnParts N Mg links ps get k a := by
  have h' : onAt N Mg links ps[k]? (openQ links ps k) (pubQ Mg.more links ps k) (get a.1)
      (strsOf Fr a.2) := h
  unfold onAt at h'
  obtain ⟨_, h2⟩ := h'
  rcases h2 with h2 | ⟨hb, hs, hc, hpp⟩
  · exact absurd hm h2
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := hb
    unfold pubHeld at h5
    unfold samplesHeld at hs
    exact ⟨h1, h2, h3, h4, fun q hq => List.all_eq_true.1 h5 q hq, h6,
      fun x hx => List.all_eq_true.1 hs x hx, hc, hpp⟩

theorem on_of_parts (k : ℕ) (a : A × Fr.E.Str) (hd : Mg.decodes (get a.1) (strsOf Fr a.2))
    (h : OnParts N Mg links ps get k a) : onQ N Mg links ps get k a := by
  show onAt N Mg links ps[k]? (openQ links ps k) (pubQ Mg.more links ps k) (get a.1)
    (strsOf Fr a.2)
  unfold onAt
  refine ⟨hd, Or.inr ⟨?_, ?_, h.shown, h.pubP⟩⟩
  · simp only [Bool.and_eq_true]
    refine ⟨⟨⟨⟨⟨h.shape, h.rows⟩, h.members⟩, h.order⟩, ?_⟩, h.book⟩
    unfold pubHeld
    exact List.all_eq_true.2 h.pub
  · unfold samplesHeld
    exact List.all_eq_true.2 h.samples

end

/-- Where the test on the promise's table says yes, what a row asks is open in front of it. -/
theorem asks_open (rows : Place → PubRow) :
    ∀ (ps : List Place) (Q : List Pub) (k : ℕ) (p : Place), pubFitBy rows ps Q = true →
      ps[k]? = some p → ∀ q ∈ (rows p).asks, q ∈ (pubSetsBy rows ps Q)[k]?.getD []
  | [], _, _, _, _, hp, _, _ => by simp at hp
  | p₀ :: ps, Q, 0, p, hf, hp, q, hq => by
    have e : p₀ = p := by simpa using hp
    subst e
    unfold pubFitBy at hf
    simp only [Bool.and_eq_true] at hf
    have h1 := List.all_eq_true.1 hf.1.1.1.1 q hq
    show q ∈ ((Q :: pubSetsBy rows ps (pubStep Q (rows p₀)))[0]?).getD []
    simpa using h1
  | p₀ :: ps, Q, k + 1, p, hf, hp, q, hq => by
    unfold pubFitBy at hf
    simp only [Bool.and_eq_true] at hf
    have hp' : ps[k]? = some p := by simpa using hp
    have := asks_open rows ps (pubStep Q (rows p₀)) k p hf.2 hp' q hq
    show q ∈ ((Q :: pubSetsBy rows ps (pubStep Q (rows p₀)))[k + 1]?).getD []
    simpa using this

/-- **The promise in front of a block, at a record without a mark, gives every public item that the
block's row in the promise's table asks.** -/
theorem asked_of_on {A P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (links : List ModelPart)
    (ps : List Place) (get : A → P × First.S) (hfit : pubFit Mg.more links ps = true) (k : ℕ)
    (p : Place)
    (hp : ps[k]? = some p) (a : A × Fr.E.Str) (h : onQ N Mg links ps get k a)
    (hm : (get a.1).2.failed = none) (q : Pub) (hq : q ∈ (pubRowOf links p).asks) :
    Mg.pub q (get a.1) = true :=
  (onParts_of_on N Mg links ps get k a h hm).pub q
    (List.mem_append_left _ (asks_open (pubRowM Mg.more links) ps (pubStartM Mg.more) k p hfit hp q
      (List.mem_append_left _ hq)))

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.onParts_of_on
#print axioms VerifiableInference.Desc.Sound.on_of_parts
#print axioms VerifiableInference.Desc.Sound.asks_open
#print axioms VerifiableInference.Desc.Sound.asked_of_on
