-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/Slides.lean: the verifier's listeners neither read nor turn the kept notes and
the name of a failed test.

The routines that hear a layers' sub-proof (OnBytes/Model/Layer.lean) keep intermediate values
(`Blk.note`) and mark failed tests on values (`Blk.check`) between two rounds, once between the
first round of a sumcheck and its other rounds. These steps turn two fields of the context,
`notes` and `failed`. The calls that receive items and close rounds read and turn other fields
alone. So such a step can be moved behind the calls that follow it.

Main names:
  `reMark c n f`: the context c with the notes n and the mark f.
  `Slides b`: what the block b yields from `reMark c n f`, it yields from c, and the context that
    it leaves is the other one with the notes n and the mark f.
  `slides_pure`, `Slides.bind`, `slides_fail`, `slides_of_eq`: how the property is had.
  `slides_item`, `slides_close`: the two calls on the channel from which the others are made
    (`Blk.item`, `Blk.close`, OnBytes/Iop/Ground.lean).
  `slides_recvE`, `slides_recvEsInto`, `slides_recvEs`, `slides_closeOne`, `slides_closeEmpty`,
    `slides_hearOne`, `slides_hearMany`: the listeners of a masked sumcheck
    (OnBytes/Iop/Psc.lean).

Limits: one direction: from a success. Nothing is said on `Blk.requireRows`, `recvAnswer`,
`recvRoot`, `closeElems`, `closePositions`, `lastEntry` or on the calls that open columns. That a
mark was or was not set is not said here.
-/
import OnBytes.Iop.GroundLaws
import OnBytes.Iop.Psc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes
open OnBytes.Psc (hearMany hearOne)

/-- The context with other kept notes and another name of a failed test. -/
def reMark (c : Ctx) (n : Array (String × E)) (f : Option String) : Ctx :=
  { c with notes := n, failed := f }

/-- The block neither reads nor turns the kept notes and the name of a failed test: what it yields
from a context with other ones, it yields from the context itself, and leaves them as they were. -/
def Slides {α : Type} (b : Blk α) : Prop :=
  ∀ c n f a c', b.Yields (reMark c n f) a c' → ∃ c0, b.Yields c a c0 ∧ c' = reMark c0 n f

theorem slides_pure {α : Type} (a : α) : Slides (pure a : Blk α) := fun c n f x c' h => by
  obtain ⟨e1, e2⟩ := (Blk.yields_pure _ _ _ _).1 h
  exact ⟨c, (Blk.yields_pure _ _ _ _).2 ⟨e1, rfl⟩, e2⟩

theorem Slides.bind {α β : Type} {b1 : Blk α} {b2 : α → Blk β} (h1 : Slides b1)
    (h2 : ∀ a, Slides (b2 a)) : Slides (b1 >>= b2) := fun c n f y c' h => by
  obtain ⟨x, c1, a1, a2⟩ := (Blk.yields_bind _ _ _ _ _).1 h
  obtain ⟨d1, g1, rfl⟩ := h1 c n f x c1 a1
  obtain ⟨d2, g2, e2⟩ := h2 x d1 n f y c' a2
  exact ⟨d2, (Blk.yields_bind _ _ _ _ _).2 ⟨x, d1, g1, g2⟩, e2⟩

theorem slides_fail {α : Type} (name : String) : Slides (Blk.fail name : Blk α) :=
  fun c n f a c' h => by
    rw [Blk.yields_iff] at h
    cases h

/-- A block for which the two can be moved through it slides. -/
theorem slides_of_eq {α : Type} (b : Blk α)
    (h : ∀ c n f, b (reMark c n f) = Except.map (fun r => (r.1, reMark r.2 n f)) (b c)) :
    Slides b := fun c n f a c' hy => by
  rw [Blk.yields_iff, h] at hy
  cases hb : b c with
  | error e =>
    rw [hb] at hy
    cases hy
  | ok r =>
    rw [hb] at hy
    cases hy
    exact ⟨r.2, (Blk.yields_iff _ _ _ _).2 hb, rfl⟩

theorem slides_item (i : Fmt.Item) (d : Fmt.ItemValue) : Slides (Blk.item i d) :=
  slides_of_eq _ fun c n f => by
    unfold Blk.item reMark
    dsimp only
    cases hd : c.ch.dry with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, if_false]
      cases hc : c.ch.cur with
      | some r =>
        dsimp only
        cases hv : r.vals <;> rfl
      | none =>
        dsimp only
        cases hl : c.ch.left with
        | nil => rfl
        | cons r t =>
          dsimp only
          cases hv : r.vals <;> rfl

theorem slides_close (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Slides (Blk.close name kind nz) :=
  slides_of_eq _ fun c n f => by
    unfold Blk.close reMark
    dsimp only
    cases he : c.ch.entries with
    | nil => rfl
    | cons e es =>
      dsimp only
      split
      · rfl
      · cases hd : c.ch.dry with
        | true => rfl
        | false =>
          simp only [Bool.false_eq_true, if_false]
          cases hc : c.ch.cur with
          | some r =>
            dsimp only
            split <;> rfl
          | none =>
            dsimp only
            cases hl : c.ch.left with
            | nil => rfl
            | cons r t =>
              dsimp only
              split <;> rfl

theorem slides_recvE : Slides Blk.recvE := by
  unfold Blk.recvE
  refine (slides_item _ _).bind fun g => ?_
  split
  · exact slides_pure _
  · exact slides_fail _

theorem slides_recvEsInto : ∀ (n : Nat) (acc : Array E), Slides (Blk.recvEsInto n acc)
  | 0, acc => by
    unfold Blk.recvEsInto
    exact slides_pure _
  | n + 1, acc => by
    unfold Blk.recvEsInto
    exact slides_recvE.bind fun x => slides_recvEsInto n _

theorem slides_recvEs (n : Nat) : Slides (Blk.recvEs n) := by
  unfold Blk.recvEs
  exact (slides_recvEsInto n _).bind fun _ => slides_pure _

theorem slides_closeOne (name : String) (kind : Fmt.Kind) (nz : Nat) :
    Slides (Blk.closeOne name kind nz) := by
  unfold Blk.closeOne
  refine (slides_close _ _ _).bind fun d => ?_
  split
  · exact slides_pure _
  · exact slides_fail _

theorem slides_closeEmpty (name : String) : Slides (Blk.closeEmpty name) := by
  unfold Blk.closeEmpty
  exact (slides_close _ _ _).bind fun _ => slides_pure _

theorem slides_hearOne (name : String) (kind : Fmt.Kind) (n nz : Nat) :
    Slides (hearOne name kind n nz) := by
  unfold hearOne
  exact (slides_recvEs n).bind fun _ => (slides_closeOne _ _ _).bind fun _ => slides_pure _

theorem slides_hearMany : ∀ ns : List Nat, Slides (hearMany ns)
  | [] => by
    unfold hearMany
    exact slides_pure _
  | n :: ns => by
    unfold hearMany
    exact (slides_hearOne _ _ _ _).bind fun _ => (slides_hearMany ns).bind fun _ => slides_pure _

end OnBytes.Tie.Pv.Lay

#print axioms OnBytes.Tie.Pv.Lay.slides_hearOne
#print axioms OnBytes.Tie.Pv.Lay.slides_hearMany
#print axioms OnBytes.Tie.Pv.Lay.slides_recvEs
#print axioms OnBytes.Tie.Pv.Lay.slides_closeEmpty
