-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/K4PromiseFront.lean: OUT OF THE TABLE OF JOINTS' PROMISE IN FRONT OF K4's BLOCK
(`onQ k`, Johnson/Desc/Sound/BordersQ.lean), AT AN UNMARKED STATEMENT, UNDER FOUR LINES ON THE
MEANING (`K4Front`): THE LOOKUP's SHARP PROMISE AT THE SEAT `seatS`'s READERS, which K04's road asks
in front (`K3LeftAt (some ∘ seatS.fork) seatS.look …`): the first implication of the table's door
(hon of K4AtTable.lean), but for the road's own letter on0; AND, BEHIND A `Yes`, WHAT THE ITEM
leftOn m SAYS. A record of lines, statements and proofs. GLUE: no draw, no count.

  `asks_open`: where the table's test `pubFitBy` says yes, whatever a block's row asks is a member
    of the open public set in front of the block.
  `k4_asks`: K4's row at a layers' segment asks ledger m · look m · left m · linkFresh m · freeAbove
    m · callerIn m, at every filling of the door.
  `lay_of_shape`: where the book-keeping holds in front of K4's block, the record stands in a
    layers' link.
  `leftAt_seatS`: the lookups' promise at THEIR readers (`S.fork?`, `S.lookHeard?`) gives it at
    seatS's, in a layers' link whose two readers of what the lookup returned give one thing.
  `leftAt_mono`: it passes to every weaker condition Q on the ledger in front of the lookup (the
    lookups' item says more of that ledger than the road asks): TO BE CALLED BEHIND `k4_left_front`,
    not by the choice of Q3.
  `K4Front`: FOUR LINES: fit (the table's test says yes at the real lists, at the meaning's filling
    of the door) · left (what `Meaning.pubP` says at left m gives `K3LeftAt` at the lookups'
    readers, at the letters h3, lm, first, Q3) · look (what `Meaning.pub` says at look m gives
    "both readers give one thing") · leftOn (where left m held at s, what was heard at the lookup's
    reader is the same at s' and `K3LeftOn` holds at s', at these readers and letters: what
    `Meaning.pubP` says at leftOn m holds at s': IN THIS FORM, NOT "`K3LeftOn` gives the item": the
    item may say more of what was heard than the promise does, and that rides with what was heard).
  **`k4_left_front`**: UNDER `K4Front`: `onQ k a`, no mark: `K3LeftAt` at seatS's readers, at a.1.
  **`k4_leftOn_behind`**: UNDER `K4Front`: `onQ k a`, no mark, a `Yes`: what `Meaning.pubP` says at
    leftOn m holds of the record behind (`kept_of_yes`; `leftOn_of_kept`, LeftOnKept.lean): the
    sentence makeP of K4PubBehind.lean at that item.
  `k4_pub_front`: each of the six asked items' Bools is true at a.1.

Limits. `K4Front` IS A PREMISE: WITHOUT IT NOTHING COMES OUT (`Meaning.pubP` is True by default).
ITS LINE left HOLDS FOUR TIES: that the lookup's own shape, lm, first and Q at segment m ARE h3, lm,
first, Q3 (K4FrontLeft.lean pays them at the lookup's own item). left AND leftOn TOGETHER FIX Q3:
the first wants that the item's own condition gives Q3, the second that Q3 gives it: Q3 IS MEANT AS
THE ITEM's OWN. A weaker Q for the road comes behind `k4_left_front`, by `leftAt_mono`. That the
lookup's yes MAKES left m is that kind's law's. Nothing on soundness.
-/
import Johnson.Road.K4.K4PromiseBehind
import Johnson.Road.K4.LeftOnKept

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Flat OnBytes.Maker
open OnBytes.Desc.First.K4 (seatS seatS_look seatS_forkQ)
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S LayOwn ModelPart Item Pub PubRow More Meaning Numbers start
  openSets pubSets pubSetsBy pubFit pubFitBy pubRowM pubRowOf pubStartM shapeAt standOf standAt
  pubHeld)
open VerifiableInference.Desc.Sound (Frame onQ)
open VerifiableInference.OnPublicFiles (K3LeftAt K3LeftOn)

/-- Where the table's test says yes, what a row asks is open in front of its block. -/
theorem asks_open (rows : Place → PubRow) : ∀ (ps : List Place) (Q : List Pub) (k : ℕ) (p : Place),
    pubFitBy rows ps Q = true → ps[k]? = some p → ∀ x ∈ (rows p).asks,
      x ∈ (pubSetsBy rows ps Q)[k]?.getD []
  | [], _, _, _, _, hp, _, _ => by simp at hp
  | p0 :: ps, Q, 0, p, hf, hp, x, hx => by
    obtain rfl : p0 = p := by simpa using hp
    simp only [pubFitBy, Bool.and_eq_true] at hf
    have h1 := List.all_eq_true.mp hf.1.1.1.1 x hx
    simpa [pubSetsBy] using h1
  | p0 :: ps, Q, k + 1, p, hf, hp, x, hx => by
    simp only [pubFitBy, Bool.and_eq_true] at hf
    have hp' : ps[k]? = some p := by simpa using hp
    have h1 := asks_open rows ps _ k p hf.2 hp' x hx
    simpa [pubSetsBy] using h1

variable {links : List ModelPart} {ps : List Place} {k m : ℕ} {pl : Place}

/-- What K4's row asks at a layers' segment. -/
theorem k4_asks (H : AtK4 links ps k m pl) (M : More) :
    ∀ x ∈ [Pub.ledger m, .look m, .left m, .linkFresh m, .freeAbove m, .callerIn m],
      x ∈ (pubRowM M links pl).asks := by
  have e : (pubRowOf links pl).asks =
      [Pub.ledger m, .look m, .left m, .linkFresh m, .freeAbove m, .callerIn m] := by
    simp only [pubRowOf, H.link, H.sub, H.piece]
    rfl
  intro x hx
  unfold pubRowM PubRow.plus
  rw [← e] at hx
  exact List.mem_append_left _ hx

/-- The book-keeping in front of K4's block: the record stands in a layers' link. -/
theorem lay_of_shape (H : AtK4 links ps k m pl) {s : S} (hs : shapeAt links (some pl) s = true) :
    ∃ a : LayOwn, s.here = .lay a := by
  simp only [shapeAt, Bool.and_eq_true, beq_iff_eq] at hs
  have e : standOf s = .link .layers := by
    rw [hs.1.1]
    simp [standAt, H.link, H.sub, H.piece]
  unfold standOf at e
  cases hh : s.here with
  | lay a => exact ⟨a, rfl⟩
  | between => rw [hh] at e; cases e
  | att a => rw [hh] at e; cases e
  | head a =>
    rw [hh] at e
    dsimp only at e
    split at e <;> cases e
  | fin a => rw [hh] at e; cases e
  | mem a => rw [hh] at e; cases e

/-- The lookups' promise at their own readers gives it at the seat's. -/
theorem leftAt_seatS {h : Forest.Shape} {lm first : ℕ} {Q : Fork → Prop} {s : S} {a : LayOwn}
    (ha : s.here = .lay a) (hfo : a.fo = a.lookHeard)
    (H : K3LeftAt S.fork? S.lookHeard? h lm first Q s) :
    K3LeftAt (fun s => some (seatS.fork s)) seatS.look h lm first Q s := by
  obtain ⟨F, F', g, rs, q, n, L, hg, hF⟩ := H
  refine ⟨F, F', g, rs, q, n, L, ?_, ?_⟩
  · rw [seatS_look ha, hfo]
    unfold S.lookHeard? at hg
    rw [ha] at hg
    exact hg
  · show some (seatS.fork s) = some F'
    rw [← seatS_forkQ ha]
    exact hF

/-- The lookups' promise passes to every weaker condition on the ledger in front of the lookup. -/
theorem leftAt_mono {T : Type} {fork : T → Option Fork} {heard : T → Option Forest.Heard}
    {h : Forest.Shape} {lm first : ℕ} {Q Q' : Fork → Prop} (hq : ∀ F, Q F → Q' F) {s : T}
    (H : K3LeftAt fork heard h lm first Q s) : K3LeftAt fork heard h lm first Q' s := by
  obtain ⟨F, F', g, rs, q, r⟩ := H
  exact ⟨F, F', g, rs, hq F q, r⟩

variable {P W : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P W) (Z : P)

/-- The four lines on the meaning. -/
structure K4Front (links : List ModelPart) (ps : List Place) (m : ℕ) (h3 : Forest.Shape)
    (lm first : ℕ) (Q3 : Fork → Prop) : Prop where
  fit : pubFit Mg.more links ps = true
  /-- FOUR TIES IN ONE LINE: the shape, lm, first and Q at which the meaning's item left m speaks
  ARE
  h3, lm, first, Q3. WITH leftOn THIS FIXES Q3: it is meant as the item's own condition -/
  left : ∀ s, Mg.pubP (.left m) (Z, s) → K3LeftAt S.fork? S.lookHeard? h3 lm first Q3 s
  look : ∀ s a, Mg.pub (.look m) (Z, s) = true → s.here = .lay a → a.fo = a.lookHeard
  /-- the way out: where the item left m held at s, what was heard at the lookup's reader is the
  same
  at s', and the lasting promise holds at s', at the same letters: what the item leftOn m says holds
  at s' (the item may say more than the promise of what was heard: that rides with it) -/
  leftOn : ∀ s s', Mg.pubP (.left m) (Z, s) → s'.lookHeard? = s.lookHeard? →
    K3LeftOn S.fork? S.lookHeard? h3 lm first Q3 s' → Mg.pubP (.leftOn m) (Z, s')

/-- Each item that K4's row asks is open in front of its block. -/
theorem k4_open (H : AtK4 links ps k m pl) (hf : pubFit Mg.more links ps = true) :
    ∀ x ∈ [Pub.ledger m, .look m, .left m, .linkFresh m, .freeAbove m, .callerIn m],
      x ∈ (pubSets Mg.more links ps)[k]?.getD [] := fun x hx =>
  asks_open (pubRowM Mg.more links) ps (pubStartM Mg.more) k pl hf H.here x
    (k4_asks H Mg.more x hx)

/-- The six asked items' Bools are true in front. -/
theorem k4_pub_front (H : AtK4 links ps k m pl) (hf : pubFit Mg.more links ps = true)
    {a : S × Fr.E.Str} (ha : onQ N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none) :
    ∀ x ∈ [Pub.ledger m, .look m, .left m, .linkFresh m, .freeAbove m, .callerIn m],
      Mg.pub x (Z, a.1) = true := fun x hx =>
  List.all_eq_true.mp (bools_of_onQ N Mg Z ha hu).2.1 x
    (List.mem_append_left _ (k4_open Mg H hf x hx))

/-- **UNDER `K4Front` (A PREMISE; its line left holds four unpaid ties): the lookup's sharp promise
at the seat's readers, out of the table's promise in front, at an unmarked statement.** -/
theorem k4_left_front (H : AtK4 links ps k m pl) {h3 : Forest.Shape} {lm first : ℕ}
    {Q3 : Fork → Prop} (Kf : K4Front Mg Z links ps m h3 lm first Q3) {a : S × Fr.E.Str}
    (ha : onQ N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none) :
    K3LeftAt (fun s => some (seatS.fork s)) seatS.look h3 lm first Q3 a.1 := by
  obtain ⟨b1, _, _⟩ := bools_of_onQ N Mg Z ha hu
  rw [H.here] at b1
  obtain ⟨al, hal⟩ := lay_of_shape H b1
  obtain ⟨_, _, _, hPP⟩ := ha.2.resolve_left fun h => h hu
  exact leftAt_seatS hal
    (Kf.look a.1 al (k4_pub_front N Mg Z H Kf.fit ha hu _ (by simp)) hal)
    (Kf.left a.1 (hPP _ (k4_open Mg H Kf.fit _ (by simp))))

section
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Piece)

/-- **UNDER `K4Front` (A PREMISE): what the item leftOn m says holds of the record behind a `Yes`**,
from the table's promise in front, at an unmarked statement. -/
theorem k4_leftOn_behind {Cl : Type} (H : AtK4 links ps k m pl) {h3 : Forest.Shape}
    {lm first : ℕ} {Q3 : Fork → Prop} (Kf : K4Front Mg Z links ps m h3 lm first Q3)
    {q : Piece (ckP .two) Fr S Cl W} {par : Par} {a : S × Fr.E.Str}
    {τ : Tr (uLT (ckP .two) q.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}
    (ha : onQ N Mg links ps (fun s => (Z, s)) k a) (hu : a.1.failed = none)
    (y : Yes seatS par q a τ fo o G) :
    Mg.pubP (.leftOn m) (Z, (behindOf seatS q a τ o G).1) := by
  obtain ⟨_, _, _, hPP⟩ := ha.2.resolve_left fun h => h hu
  have hl := hPP _ (k4_open Mg H Kf.fit (.left m) (by simp))
  exact Kf.leftOn a.1 _ hl (rest_of_yes y).1.lookHeard
    (leftOn_of_kept (kept_of_yes y) (Kf.left a.1 hl))

end

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.asks_open
#print axioms OnBytes.Road.K4.k4_left_front
#print axioms OnBytes.Road.K4.k4_leftOn_behind
