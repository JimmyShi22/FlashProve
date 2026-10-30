-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/K4PubBehind.lean: THE PUBLIC ITEMS BEHIND K4's BLOCK, CUT INTO "KEPT" AND "MADE",
WITH THE MADE ONES BY NAME: the two fields pub and pubP of `K4Keeps` (K4PromiseBehind.lean) from
sentences on single items. Statements and proofs on lists: no draw, no count, nothing on any record.

  `mem_pubStep`: a member of the open public set behind a block was open in front and is not
    dropped, or is made by the block's row. `mem_tied_step`: a public item that is tied to an item
    open behind a block is tied to one open in front, or to one that the block's row opens.
  `k4_tied_new`: the public items tied to what K4's row opens at a layers' segment: formsInT m 3
    "own" · formsInT m 2 "planes" · formsInT m 2 "join" · hasRow m.
  `k4_makes`, `k4_drops`: K4's row in the promise's table makes lookIn m 7 · leftOn m and drops look
    m · left m · callerIn m, beside what the meaning's filling of the door adds at the place.
  **`k4_pubHeld_behind`**: the Bools behind, from: keepQ (an open item that the row does not drop
    stays true) · keepT (a tied item stays true) · make (each of lookIn m 7, leftOn m, the four tied
    ones and the door's makes is true behind).
  **`k4_pubP_behind`**: what the open items say beside their Bools, likewise (keepP · makeP).
  **`k4Keeps_of_items`**: `K4Keeps` from its eleven other fields and these five sentences, each
  asked
    at a `Yes` of K4's piece, inside the promise in front, at an unmarked statement.

Limits. keepQ, keepT, make, keepP, makeP ARE PREMISES ON THE MEANING's LETTERS AT TWO RECORDS a, b:
nothing here says that a yes of K4's block gives them (makeP at leftOn m: `k4_leftOn_behind`,
K4PromiseFront.lean, under `K4Front`). Nothing on soundness.
-/
import Johnson.Road.K4.K4PromiseFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Item Pub PubRow BlockRow More Meaning segRow
  pubRowM pubRowOf pubStep stepOpen pubOfItems pubHeld pubHeld_of moreItem)

/-- A member of the open public set behind a block. -/
theorem mem_pubStep {Q : List Pub} {r : PubRow} {x : Pub} (h : x ∈ pubStep Q r) :
    (x ∈ Q ∧ x ∉ r.drops) ∨ x ∈ r.makes := by
  unfold pubStep at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨h1, h2⟩ := List.mem_filter.mp h
    exact Or.inl ⟨h1, by simpa using h2⟩
  · exact Or.inr (List.mem_filter.mp h).1

/-- A public item tied to an item that is open behind a block. -/
theorem mem_tied_step {O : List Item} {r : BlockRow} {x : Pub}
    (h : x ∈ pubOfItems (stepOpen O r)) : x ∈ pubOfItems O ∨ x ∈ pubOfItems r.outs := by
  unfold pubOfItems at h ⊢
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp h
  unfold stepOpen at hi
  rcases List.mem_append.mp hi with hi | hi
  · exact Or.inl (List.mem_flatMap.mpr ⟨i, (List.mem_filter.mp hi).1, hx⟩)
  · exact Or.inr (List.mem_flatMap.mpr ⟨i, (List.mem_filter.mp hi).1, hx⟩)

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- The public items tied to what K4's row opens. -/
theorem k4_tied_new (H : AtK4 links ps k m pl) :
    pubOfItems (VerifiableInference.Desc.First.rowOf links pl).outs =
      [Pub.formsInT m 3 "own", .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m] := by
  have e : VerifiableInference.Desc.First.rowOf links pl = segRow .layers m 3 := by
    simp only [VerifiableInference.Desc.First.rowOf, H.link, H.sub, H.piece]
  rw [e]
  rfl

/-- What K4's row in the promise's table makes. -/
theorem k4_makes (H : AtK4 links ps k m pl) (M : More) :
    (pubRowM M links pl).makes =
      [Pub.lookIn m 7, .leftOn m] ++ (M.rows links pl).makes.map moreItem := by
  have e : (pubRowOf links pl).makes = [Pub.lookIn m 7, .leftOn m] := by
    simp only [pubRowOf, H.link, H.sub, H.piece]
    rfl
  unfold pubRowM PubRow.plus
  rw [← e]

/-- What it drops. -/
theorem k4_drops (H : AtK4 links ps k m pl) (M : More) :
    (pubRowM M links pl).drops =
      [Pub.look m, .left m, .callerIn m] ++ (M.rows links pl).drops.map moreItem := by
  have e : (pubRowOf links pl).drops = [Pub.look m, .left m, .callerIn m] := by
    simp only [pubRowOf, H.link, H.sub, H.piece]
    rfl
  unfold pubRowM PubRow.plus
  rw [← e]

variable {P W : Type} (Mg : Meaning P W)

/-- **The public items' Bools behind K4's block: kept, or made.** -/
theorem k4_pubHeld_behind (H : AtK4 links ps k m pl) (O : List Item) (Q : List Pub) (a b : P × S)
    (h : pubHeld Mg O Q a = true)
    (keepQ : ∀ x ∈ Q, x ∉ (pubRowM Mg.more links pl).drops → Mg.pub x a = true →
      Mg.pub x b = true)
    (keepT : ∀ x ∈ pubOfItems O, Mg.pub x a = true → Mg.pub x b = true)
    (make : ∀ x ∈ (pubRowM Mg.more links pl).makes ++
      [Pub.formsInT m 3 "own", .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m],
      Mg.pub x b = true) :
    pubHeld Mg (stepOpen O (VerifiableInference.Desc.First.rowOf links pl))
      (pubStep Q (pubRowM Mg.more links pl)) b = true := by
  have ha : ∀ x ∈ Q ++ pubOfItems O, Mg.pub x a = true := List.all_eq_true.mp h
  unfold pubHeld
  refine List.all_eq_true.mpr fun x hx => ?_
  rcases List.mem_append.mp hx with hx | hx
  · rcases mem_pubStep hx with ⟨h1, h2⟩ | h1
    · exact keepQ x h1 h2 (ha x (List.mem_append_left _ h1))
    · exact make x (List.mem_append_left _ h1)
  · rcases mem_tied_step hx with h1 | h1
    · exact keepT x h1 (ha x (List.mem_append_right _ h1))
    · rw [k4_tied_new H] at h1
      exact make x (List.mem_append_right _ h1)

/-- **What the open public items say beside their Bools, behind K4's block.** -/
theorem k4_pubP_behind (Q : List Pub) (a b : P × S) (h : ∀ x ∈ Q, Mg.pubP x a)
    (keepP : ∀ x ∈ Q, x ∉ (pubRowM Mg.more links pl).drops → Mg.pubP x a → Mg.pubP x b)
    (makeP : ∀ x ∈ (pubRowM Mg.more links pl).makes, Mg.pubP x b) :
    ∀ x ∈ pubStep Q (pubRowM Mg.more links pl), Mg.pubP x b := fun x hx => by
  rcases mem_pubStep hx with ⟨h1, h2⟩ | h1
  · exact keepP x h1 h2 (h x h1)
  · exact makeP x h1

section
open Iop OnBytes OnBytes.Model OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc.First (Numbers start openSets pubSets sampledIn)
open VerifiableInference.Desc.Sound (Frame Piece onQ strsOf)

variable {Cl : Type} {Fr : Frame} (N : Numbers) (Z : P) {q : Piece (ckP .two) Fr S Cl W}
  {par : Par} {pl' : Place}

/-- **`K4Keeps` (K4PromiseBehind.lean) WITH ITS TWO FIELDS ON THE PUBLIC ITEMS TAKEN APART**: its
eleven other fields are handed over as they are; the five sentences on single items are asked at a
`Yes`, inside the promise, at an unmarked statement. -/
theorem k4Keeps_of_items (H : AtK4 links ps k m pl)
    (next : ps[k + 1]? = some pl') (link' : pl'.link = some m) (piece' : pl'.piece = 4)
    (trees : N.treesAt (some pl') = N.treesAt (some pl))
    (msgs : N.msgsAt (some pl') = N.msgsAt (some pl))
    (dec : ∀ a τ fo o G, Yes seatS par q a τ fo o G → Mg.decodes (Z, a.1) (strsOf Fr a.2) →
      Mg.decodes (Z, (behindOf seatS q a τ o G).1) (strsOf Fr (behindOf seatS q a τ o G).2))
    (inOrder : ∀ x y : S × Fr.E.Str, SameIn N Mg Z links ps k q.base x y →
      Mg.inOrder (Z, x.1) = true → Mg.inOrder (Z, y.1) = true)
    (held : ∀ (x y : S × Fr.E.Str) (t j : ℕ), SameIn N Mg Z links ps k q.base x y →
      Mg.held t j (Z, x.1) = true → Mg.held t j (Z, y.1) = true)
    (below : ∀ z ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []), z.1 < q.base)
    (shown : ∀ (x y : S × Fr.E.Str) (t j : ℕ), t < q.base →
      SameIn N Mg Z links ps k q.base x y →
      Mg.shown t j (strsOf Fr x.2) → Mg.shown t j (strsOf Fr y.2))
    (noColl : ∀ (x y : S × Fr.E.Str) (t j : ℕ), t < q.base →
      SameIn N Mg Z links ps k q.base x y →
      Mg.noColl t j (Z, x.1) (strsOf Fr x.2) → Mg.noColl t j (Z, y.1) (strsOf Fr y.2))
    (keepQ : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G → ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [],
      x ∉ (pubRowM Mg.more links pl).drops → Mg.pub x (Z, a.1) = true →
      Mg.pub x (Z, (behindOf seatS q a τ o G).1) = true)
    (keepT : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G →
      ∀ x ∈ pubOfItems ((openSets links ps (start links))[k]?.getD []),
      Mg.pub x (Z, a.1) = true → Mg.pub x (Z, (behindOf seatS q a τ o G).1) = true)
    (make : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G → ∀ x ∈ (pubRowM Mg.more links pl).makes ++
        [Pub.formsInT m 3 "own", .formsInT m 2 "planes", .formsInT m 2 "join", .hasRow m],
      Mg.pub x (Z, (behindOf seatS q a τ o G).1) = true)
    (keepP : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G → ∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [],
      x ∉ (pubRowM Mg.more links pl).drops → Mg.pubP x (Z, a.1) →
      Mg.pubP x (Z, (behindOf seatS q a τ o G).1))
    (makeP : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
      Yes seatS par q a τ fo o G → ∀ x ∈ (pubRowM Mg.more links pl).makes,
      Mg.pubP x (Z, (behindOf seatS q a τ o G).1)) :
    K4Keeps N Mg Z links ps k m pl pl' q par where
  next := next
  link' := link'
  piece' := piece'
  trees := trees
  msgs := msgs
  dec := dec
  inOrder := inOrder
  held := held
  below := below
  shown := shown
  noColl := noColl
  pub := fun a τ fo o G ha hu y h =>
    k4_pubHeld_behind Mg H _ _ _ _ h (keepQ a τ fo o G ha hu y) (keepT a τ fo o G ha hu y)
      (make a τ fo o G ha hu y)
  pubP := fun a τ fo o G ha hu y h =>
    k4_pubP_behind Mg _ _ _ h (keepP a τ fo o G ha hu y) (makeP a τ fo o G ha hu y)

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_pubHeld_behind
#print axioms OnBytes.Road.K4.k4_pubP_behind
#print axioms OnBytes.Road.K4.k4Keeps_of_items
