-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/K4PromiseBehind.lean: THE TABLE OF JOINTS' PROMISE BEHIND K4's BLOCK (`onQ (k + 1)`,
Johnson/Desc/Sound/BordersQ.lean) FROM THE PROMISE IN FRONT, AT A YES: the second implication of the
table's door (hon' of K4AtTable.lean), by the table's rule by sort of clause
(`onQ_step_quiet`, Johnson/Desc/Sound/PromiseRidesQ.lean). A record of lines, statements and proofs.
GLUE: no draw, no count.

WHAT IS PAID HERE, off what a yes of K4's piece leaves (`sameRead_of_yes`, RidesBack.lean;
`kept_of_yes`, KeptOfYes.lean; `mark_of_yes`, LeftOnOfYes.lean): the row is quiet · a mark stays ·
the statement's groups and the book's places are as they were · THE BOOK-KEEPING BEHIND (`shapeAt`:
the chain stands in a layers' segment; no count of rows waits; the open segment's number) ·
`bookAt`. WHAT IS A LINE (`K4Keeps`): the plan: the next block stands at piece 4 of the same segment
(next, link', piece'); the plan tells as many trees and messages there as at piece 3 (trees, msgs);
every tenant whose pin is open in front sits in a tree sent in front of K4's stretch (below) · the
meaning: decodes goes past every `Yes`; inOrder · held go from x to y wherever `SameIn … q.base x y`
(x INSIDE THE PROMISE IN FRONT, WITHOUT A MARK, and `SameRead q.base x y`: the fence); shown ·
noColl likewise AT A TREE WHOSE NUMBER IS BELOW q.base ALONE (`SameRead` says nothing of a later
tree: asked at every tree the two lines could be met by no real meaning) · pub · pubP: THE PUBLIC
ITEMS BEHIND, at a `Yes`: whole, as two fields (K4PubBehind.lean takes them apart).

  `quiet_k4`: K4's row closes and opens no class of rows and no pin with a sample.
  `bools_of_onQ`: three of the promise's six Bools at an unmarked statement: the book-keeping, the
    public items, the book.
  `shape_behind`: the book-keeping behind a yes.
  **`k4_promise_behind`**: UNDER `K4Keeps`: `onQ k a`, no mark, a yes with the statement b behind:
    `onQ (k + 1) b`.

Limits. `K4Keeps` IS A PREMISE: no filling of `Meaning` or `Numbers` is shown to meet it. Its fields
pub and pubP hold the most of the work that is left: the items that K4 makes (lookIn m 7 · leftOn m
· the tied formsInT m 3 "own", formsInT m 2 "planes" | "join", hasRow m) and those that ride. ONE
DIRECTION, FROM A YES. Nothing on soundness.
-/
import Johnson.Desc.Sound.PromiseRidesQ
import Johnson.Road.K4.K4AtTable
import Johnson.Road.K4.RidesBack

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par seatS)
open _root_.Run (ckP)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers segRow rowOf start openSets pubSets
  pubRowM pubStep stepOpen quietRow shapeAt standOf standAt pubHeld bookAt rowsHeld membersHeld
  sampledIn)
open VerifiableInference.Desc.Sound (Frame Piece below onQ strsOf onQ_step_quiet)
open VerifiableInference.Desc.Plain.K04 (HearsAs)

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- K4's row closes and opens no class of rows and no pin with a sample. -/
theorem quiet_k4 (H : AtK4 links ps k m pl) : quietRow (rowOf links pl) = true := by
  have e : rowOf links pl = segRow .layers m 3 := by
    simp only [VerifiableInference.Desc.First.rowOf, H.link, H.sub, H.piece]
  rw [e]
  rfl

variable {P W Cl : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (Z : P)
  {q : Piece (ckP .two) Fr S Cl W} {par : Par} {bk : Block S Cl}

/-- **The fence.** x stands inside the table's promise in front of block number k and bears no mark,
and y reads as x (`SameRead`). WHY THE FENCE: `SameRead`'s clause on the open link speaks only where
x
stands in a layers' link: at two records outside one it lets the open part differ at will, and a
line
asked there is false at a meaning that reads that part. -/
def SameIn (links : List ModelPart) (ps : List Place) (k base : ℕ) (x y : S × Fr.E.Str) : Prop :=
  onQ N Mg links ps (fun s => (Z, s)) k x ∧ x.1.failed = none ∧ SameRead base x y

/-- The lines on the plan, the numbers and the meaning. -/
structure K4Keeps (links : List ModelPart) (ps : List Place) (k m : ℕ) (pl pl' : Place)
    (q : Piece (ckP .two) Fr S Cl W) (par : Par) : Prop where
  next : ps[k + 1]? = some pl'
  link' : pl'.link = some m
  piece' : pl'.piece = 4
  trees : N.treesAt (some pl') = N.treesAt (some pl)
  msgs : N.msgsAt (some pl') = N.msgsAt (some pl)
  /-- AT A `Yes`, AND OUTSIDE THE FENCE: the chain's tie asks "the stored table decodes" past every
  yes,
  with no promise in hand; a `Yes` has what the lookup returned in hand, so the record stands in a
  layers' link -/
  dec : ∀ a τ fo o G, Yes seatS par q a τ fo o G → Mg.decodes (Z, a.1) (strsOf Fr a.2) →
    Mg.decodes (Z, (behindOf seatS q a τ o G).1) (strsOf Fr (behindOf seatS q a τ o G).2)
  inOrder : ∀ x y : S × Fr.E.Str, SameIn N Mg Z links ps k q.base x y →
    Mg.inOrder (Z, x.1) = true → Mg.inOrder (Z, y.1) = true
  held : ∀ (x y : S × Fr.E.Str) (t j : ℕ), SameIn N Mg Z links ps k q.base x y →
    Mg.held t j (Z, x.1) = true → Mg.held t j (Z, y.1) = true
  /-- the plan: every tenant whose pin is open in front of K4's block sits in a tree that was sent
  in
  front of K4's stretch -/
  below : ∀ z ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []), z.1 < q.base
  shown : ∀ (x y : S × Fr.E.Str) (t j : ℕ), t < q.base → SameIn N Mg Z links ps k q.base x y →
    Mg.shown t j (strsOf Fr x.2) → Mg.shown t j (strsOf Fr y.2)
  noColl : ∀ (x y : S × Fr.E.Str) (t j : ℕ), t < q.base → SameIn N Mg Z links ps k q.base x y →
    Mg.noColl t j (Z, x.1) (strsOf Fr x.2) → Mg.noColl t j (Z, y.1) (strsOf Fr y.2)
  pub : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
    Yes seatS par q a τ fo o G →
    pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
      ((pubSets Mg.more links ps)[k]?.getD []) (Z, a.1) = true →
    pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD []) (rowOf links pl))
      (pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links pl))
      (Z, (behindOf seatS q a τ o G).1) = true
  pubP : ∀ a τ fo o G, onQ N Mg links ps (fun s => (Z, s)) k a → a.1.failed = none →
    Yes seatS par q a τ fo o G →
    (∀ x ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP x (Z, a.1)) →
    ∀ x ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD []) (pubRowM Mg.more links pl),
      Mg.pubP x (Z, (behindOf seatS q a τ o G).1)

/-- Three of the promise's six Bools at an unmarked statement: the book-keeping, the public items,
the book. -/
theorem bools_of_onQ {a : S × Fr.E.Str} (ha : onQ N Mg links ps (fun s => (Z, s)) k a)
    (hu : a.1.failed = none) :
    shapeAt links ps[k]? a.1 = true ∧
      pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) (Z, a.1) = true ∧
      bookAt N ps[k]? a.1 = true := by
  obtain ⟨hB, _⟩ := ha.2.resolve_left fun h => h hu
  simp only [Bool.and_eq_true] at hB
  exact ⟨hB.1.1.1.1.1, hB.1.2, hB.2⟩

/-- **The book-keeping behind a yes.** -/
theorem shape_behind (H : AtK4 links ps k m pl) {pl' : Place} (hl : pl'.link = some m)
    (hp : pl'.piece = 4) {a : S × Fr.E.Str} {τ : Tr (uLT (ckP .two) q.ds)} {fo : Forest.Heard}
    {o : Own} {G : Fork} (y : Yes seatS par q a τ fo o G)
    (hs : shapeAt links (some pl) a.1 = true) :
    shapeAt links (some pl') (behindOf seatS q a τ o G).1 = true := by
  obtain ⟨al, ha, _⟩ := lay_of_look y.look
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hro, _, hR, _⟩ := kept_of_yes y
  obtain ⟨a', ha', _⟩ := hR.here al ha
  have s1 : standOf (behindOf seatS q a τ o G).1 = .link .layers := by
    unfold standOf
    rw [ha']
  have s2 : standAt links pl' = .link .layers := by
    simp [standAt, hl, H.sub, hp]
  have s3 : (behindOf seatS q a τ o G).1.noneWaits = true := by
    unfold S.noneWaits
    rw [hro]
  simp only [shapeAt, Bool.and_eq_true] at hs ⊢
  refine ⟨⟨by rw [s1, s2]; rfl, by rw [s3]; rfl⟩, ?_⟩
  rw [hR.link, hl, ← H.link]
  exact hs.2

/-- **UNDER `K4Keeps` (A PREMISE): the promise in front, no mark, a yes of a piece that holds
`below bk`, bk hearing as K4's own block: the promise behind.** -/
theorem k4_promise_behind (H : AtK4 links ps k m pl) {pl' : Place}
    (Kp : K4Keeps N Mg Z links ps k m pl pl' q par) (hb : q.b = below bk)
    (hh : HearsAs seatS par bk) (hback : q.back = []) (a : S × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) q.ds)) (b : S × Fr.E.Str)
    (ha : onQ N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (h : q.ior.red.out a τ = some b) : onQ N Mg links ps (fun s => (Z, s)) (k + 1) b := by
  obtain ⟨_, fo, o, G, y, rfl⟩ := yes_of_out seatS hh hb hback a b τ h
  have sr := sameRead_of_yes y
  have si : SameIn N Mg Z links ps k q.base a (behindOf seatS q a τ o G) := ⟨ha, hu, sr⟩
  obtain ⟨b1, _, _⟩ := bools_of_onQ N Mg Z ha hu
  refine onQ_step_quiet N Mg links ps (fun s => (Z, s)) k pl H.here (quiet_k4 H) a _ ha
    (fun hm => absurd hu hm) (Kp.dec a τ fo o G y) (fun _ => ?_) (by rw [sr.rest.st])
    (by rw [sr.rest.book]) (Kp.inOrder _ _ si) (fun _ => Kp.pub a τ fo o G ha hu y) (fun _ hk => ?_)
    (fun _ => Kp.pubP a τ fo o G ha hu y) (fun x _ => Kp.held _ _ x.1 x.2 si)
    (fun x hx => Kp.shown _ _ x.1 x.2 (Kp.below x hx) si)
    (fun x hx => Kp.noColl _ _ x.1 x.2 (Kp.below x hx) si)
  · rw [Kp.next]
    rw [H.here] at b1
    exact shape_behind H Kp.link' Kp.piece' y b1
  · rw [H.here] at hk
    rw [Kp.next]
    simp only [bookAt, Bool.and_eq_true] at hk ⊢
    rw [sr.rest.book, sr.rest.st, Kp.trees, Kp.msgs]
    exact hk

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.shape_behind
#print axioms OnBytes.Road.K4.k4_promise_behind
