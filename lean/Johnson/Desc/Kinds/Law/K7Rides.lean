-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K7Rides.lean.
WHAT IT DOES NOT SHOW. No soundness. THE PROMISE DOES NOT RIDE OVER THE NEXT TOKEN's PLACE
WITHOUT PREMISES: of the eleven that the table's files' rule for a quiet row asks (Desc/Sound/
PromiseRidesQ.lean: onQ_step_held) FIVE ARE PAID HERE (the mark · the shape · the rows' lists · the
groups' members · the book) AND SIX STAY, BY NAME: hDec ("the stored table decodes" rides) · hIn
(the statement is in order: IT READS THE STATEMENT, WHICH TURNS HERE: one fresh group is pushed) ·
hPub, hPP (the public items: "a token is heard and is small" is made here; "nothing is heard" is
dropped) · hHeld, hSN (the samples held; shown and no collision). OF THE FIVE, THREE LEAN ON
PREMISES OF THEIR OWN: hFresh: THE FRESH GROUP's NUMBER IS THE NUMBER OF NO SEGMENT OF WHICH A CLASS
OF ROWS IS OPEN AT THE BORDER IN FRONT (a test on the table, and "the statement has just so many
groups there": paid by nobody) · hf, hn: the table's test on the book says yes, and the block tells
no tree. IT SPEAKS OF THE SEATED CONSTANT (the entry of the head's link, then the next token's
block).
LETTERS. No "there is" in the tops. c, m: the fresh group's two codes: read by hst alone.
OBJECT. The table's promise at two neighbouring borders (Desc/Sound/BordersQ.lean: onQ), in front of
and behind piece 1 of a head's link.
USER. The field "rides" of the bill of the next token's tie (Law/K7Tied.lean: K7Due).
WHAT IT IS.
  front_unmarked    the entry of the head's link says yes at no marked record.
  groups_at         a statement with one fresh group pushed has, at every number but the fresh
                    one's, the group that it had.
  rowsHeld_at, membersHeld_at   the promise's two Bools on the groups ride where the groups AT THE
                                OPEN SEGMENTS' NUMBERS are as they were (and, for the second, the
                                book's places). NEAREST RELATIVES:
                                Desc/First/PromiseRides.lean: rowsHeld_of_groups |
                                membersHeld_of_groups: they ask that the WHOLE array of groups is as
                                it was: false at this place.
  place_facts       what the record behind the seated constant's yes is, in the form that the next
                    theorem reads.
  k7_rides          the promise one border on.
A search (statements that name rowsHeld | membersHeld, over Desc/First and
Desc/Sound, the table's files, the code switch's files and K6's and K7's files,
in versions other than these: 947 files): the relatives named above.

-/
import Mathlib
import Johnson.Desc.Sound.PromiseRidesQ
import Johnson.Desc.Sound.OnParts
import Johnson.Desc.First.BookFit
import Johnson.Desc.Kinds.Law.ReplyShape
import Johnson.Desc.Kinds.Law.ReplyRest

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place KindName Oracle)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers standOf shapeAt rowSegs rowsHeld
  membersHeld start openSets pubSets pubRowM pubStep stepOpen rowOf pubHeld sampledIn bookFit)
open VerifiableInference.Desc.First.K2 (headFrontQ headFrontQ_iff headFrontQ_rest withFresh)
open VerifiableInference.Desc.Sound (Frame onQ strsOf openQ onParts_of_on onQ_step_held)

/-- **The entry of the head's link says yes at no marked record.** -/
theorem front_unmarked {tl : HTailF2} {s s0 : S} (h : headFrontQ tl s = .ok s0) :
    s.failed = none := by
  obtain ⟨x, s₁, a, k⟩ := (headFrontQ_iff tl s s0).1 h
  have h0 : (s.enterHead tl).unmarked = .ok s₁ := k.enters
  have h1 := ((S.unmarked_ok _ _).1 h0).2
  have h2 : s0.failed = s₁.failed := by rw [k.out]
  rw [← (headFrontQ_rest h).2.2.2.1, h2, h1]

/-- At every number but the fresh one's the group is as it was. -/
theorem groups_at (T : Statement) (c m i : Nat) (hi : i ≠ T.groups.size) :
    (withFresh T c m).groups[i]? = T.groups[i]? := by
  simp [withFresh, Array.getElem?_push, hi]

/-- The rows' lists ride where the open segments' groups are as they were. -/
theorem rowsHeld_at (N : Numbers) (O : List Item) (s t : S)
    (hg : ∀ x ∈ rowSegs O, t.st.groups[N.groupAt x]? = s.st.groups[N.groupAt x]?)
    (h : rowsHeld N O s = true) : rowsHeld N O t = true := by
  unfold rowsHeld at h ⊢
  refine List.all_eq_true.2 fun x hx => ?_
  have h1 := List.all_eq_true.1 h x hx
  rw [hg x hx]
  exact h1

/-- The groups' members ride there too, where the book's places are as they were. -/
theorem membersHeld_at (N : Numbers) (O : List Item) (s t : S)
    (hg : ∀ x ∈ rowSegs O, t.st.groups[N.groupAt x]? = s.st.groups[N.groupAt x]?)
    (hb : t.book = s.book) (h : membersHeld N O s = true) : membersHeld N O t = true := by
  unfold membersHeld at h ⊢
  refine List.all_eq_true.2 fun x hx => ?_
  have h1 := List.all_eq_true.1 h x hx
  rw [hg x hx, hb]
  exact h1

/-- **What the record behind the seated constant's yes is.** -/
theorem place_facts (W : Verify.Public) (l : Nat) (name : String) (front : Block S Unit)
    (tl : HTailF2)
    (hfront : ∀ s rs gs s1, front.decide s rs gs = .ok s1 → headFrontQ tl s = .ok s1) :
    ∀ s rs gs t, (front.andThen name (Reply.blockOf W l)).decide s rs gs = .ok t →
      s.failed = none ∧
        t.st = withFresh s.st s.check.frame.shape.code s.check.frame.shape.maskCode ∧
        t.book = s.book ∧
        (standOf t = .headFront ∧ t.link? = none ∧ t.noneWaits = s.noneWaits) := by
  intro s rs gs t h
  obtain ⟨s0, h0, _⟩ := place_rest W l name front tl hfront s rs gs t h
  obtain ⟨a1, a2, _⟩ := place_whole W l name front tl hfront s rs gs t h
  exact ⟨front_unmarked h0, a1, a2, joined_stand W l name front tl hfront s rs gs t h⟩

/-- **THE PROMISE ONE BORDER ON, OVER THE NEXT TOKEN's PLACE.** -/
theorem k7_rides {A P Wt : Type} {Fr : Frame} (N : Numbers) (Mg : Meaning P Wt)
    (links : List ModelPart) (ps : List Place) (get : A → P × S) (k hd : Nat) (k1 k2 : KindName)
    (hl : links[hd]? = some .head) (hp : ps[k]? = some ⟨1, some hd, 1, k1⟩)
    (hp' : ps[k + 1]? = some ⟨1, some hd, 2, k2⟩) (a b : A × Fr.E.Str)
    (ha : onQ N Mg links ps get k a) (c m : Nat) (h0 : (get a.1).2.failed = none)
    (hst : (get b.1).2.st = withFresh (get a.1).2.st c m)
    (hbk : (get b.1).2.book = (get a.1).2.book)
    (hsh : standOf (get b.1).2 = .headFront ∧ (get b.1).2.link? = none ∧
      (get b.1).2.noneWaits = (get a.1).2.noneWaits)
    (hFresh : ∀ x ∈ rowSegs (openQ links ps k), N.groupAt x ≠ (get a.1).2.st.groups.size)
    (told : List (List Oracle)) (hf : bookFit N ps told = true) (hn : told[k]? = some [])
    (hDec : Mg.decodes (get a.1) (strsOf Fr a.2) → Mg.decodes (get b.1) (strsOf Fr b.2))
    (hIn : (get a.1).2.failed = none → (get b.1).2.failed = none →
      Mg.inOrder (get a.1) = true → Mg.inOrder (get b.1) = true)
    (hPub : (get a.1).2.failed = none → (get b.1).2.failed = none →
      pubHeld Mg ((openSets links ps (start links))[k]?.getD [])
        ((pubSets Mg.more links ps)[k]?.getD []) (get a.1) = true →
      pubHeld Mg (stepOpen ((openSets links ps (start links))[k]?.getD [])
          (rowOf links ⟨1, some hd, 1, k1⟩))
        (pubStep ((pubSets Mg.more links ps)[k]?.getD [])
          (pubRowM Mg.more links ⟨1, some hd, 1, k1⟩))
        (get b.1) = true)
    (hPP : (get a.1).2.failed = none → (get b.1).2.failed = none →
      (∀ q ∈ (pubSets Mg.more links ps)[k]?.getD [], Mg.pubP q (get a.1)) →
      ∀ q ∈ pubStep ((pubSets Mg.more links ps)[k]?.getD [])
          (pubRowM Mg.more links ⟨1, some hd, 1, k1⟩),
        Mg.pubP q (get b.1))
    (hHeld : (get a.1).2.failed = none → (get b.1).2.failed = none →
      ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.held x.1 x.2 (get a.1) = true → Mg.held x.1 x.2 (get b.1) = true)
    (hSN : (get a.1).2.failed = none → (get b.1).2.failed = none →
      ∀ x ∈ sampledIn N ((openSets links ps (start links))[k]?.getD []),
        Mg.shown x.1 x.2 (strsOf Fr a.2) ∧ Mg.noColl x.1 x.2 (get a.1) (strsOf Fr a.2) →
        Mg.shown x.1 x.2 (strsOf Fr b.2) ∧ Mg.noColl x.1 x.2 (get b.1) (strsOf Fr b.2)) :
    onQ N Mg links ps get (k + 1) b := by
  have hk : k < ps.length := (List.getElem?_eq_some_iff.1 hp).1
  have hq : First.quietRow (rowOf links ⟨1, some hd, 1, k1⟩) = true := by
    unfold First.rowOf
    simp only [hl]
    rfl
  have hg : ∀ x ∈ rowSegs (openQ links ps k),
      (get b.1).2.st.groups[N.groupAt x]? = (get a.1).2.st.groups[N.groupAt x]? := by
    intro x hx
    rw [hst]
    exact groups_at _ c m _ (hFresh x hx)
  have hs0 : shapeAt links (some ⟨1, some hd, 1, k1⟩) (get a.1).2 = true := by
    have := (onParts_of_on N Mg links ps get k a ha h0).shape
    rw [hp] at this
    exact this
  refine onQ_step_held N Mg links ps get k _ hp hq a b ha (fun h => absurd h0 h) hDec ?_
    (fun _ _ h => rowsHeld_at N _ _ _ hg h) (fun _ _ h => membersHeld_at N _ _ _ hg hbk h) hIn hPub
    ?_ hPP hHeld hSN
  · intro _ _
    rw [hp']
    exact shape_rides links hd hl k1 k2 hsh hs0
  · intro _ _ h
    refine First.bookAt_step N ps told hf k hk hn _ _ hbk ?_ h
    rw [hst]
    rfl

end VerifiableInference.Desc.Kinds.Head.Law
