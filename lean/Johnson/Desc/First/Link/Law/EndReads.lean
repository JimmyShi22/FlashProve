-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Link/Law/EndReads.lean: WHAT THE STATE AND THE STRINGS BEHIND K10's CLOSING KEEP
OF THOSE IN FRONT, OFF THE CLOSING's OWN WRITING (`wrK`, Johnson/Desc/First/Close/Law/AtBlock.lean)
AND THE PIECE's OWN STRINGS: so that `hF_of_door`'s premises at the border behind (HFOfDoor.lean:
the three tests on the book; hy | hyF) come from what is known IN FRONT of the closing: no «reached»
behind is wanted for them. Theorems. No text already in the library turns.

  `putLive_book`, `wrK_book`, `wrK_roots`: the closing's writing touches neither the book nor the
    number of roots.
  `putLive_not_head`, `wrK_not_head`: where the state in front does not stand at the head's link,
    the state behind does not: so the premise hH of `skel_old_door` | `doorReads_door`
    (FrontStEnds.lean) may be asked in front.
  `tests_behind`: **s' = wrK s f S' ⊢ the three tests atFirstBook | atFirstSeats | atFirstFits
    (Johnson/Desc/K12/Door/DoorBools.lean) at s' are those at s.**
  `imp_stays`: a'.2 = p.ior.imp a.2 τ ⊢ the column at every leaf of every tree below the piece's
    base is the same off a'.2 and off a.2 (`K10EndS`'s first clause has that form).
Limits. Book-keeping on two texts. Nothing on soundness.
-/
import Johnson.Desc.First.Link.Law.StaysAt
import Johnson.Desc.First.Close.Law.AtBlock
import Johnson.Desc.K12.Door.DoorBools

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Close (wrK)
open VerifiableInference.Desc.K12.Door (atFirstBook atFirstSeats atFirstFits Laid)
open _root_.Run.PQ (CK)
open _root_.Johnson.Desc.First.Walk.Tied (stays_behind)

theorem putLive_book (s : First.S) (c : ChainCheck) :
    (s.putLive c).book = s.book ∧ (s.putLive c).roots = s.roots := by
  unfold First.S.putLive
  split
  · unfold First.S.putLink
    split
    all_goals first
      | exact ⟨rfl, rfl⟩
      | (split <;> exact ⟨rfl, rfl⟩)
  · exact ⟨rfl, rfl⟩

/-- The closing's writing leads to the head's link from no other sort of place. -/
theorem putLive_not_head (s : First.S) (c : ChainCheck) (h : ∀ b, s.here ≠ .head b) :
    ∀ b, (s.putLive c).here ≠ .head b := by
  unfold First.S.putLive
  split
  · unfold First.S.putLink
    cases hh : s.here with
    | head a => exact absurd hh (h a)
    | lay a => intro b hb; cases hb
    | att a => intro b hb; cases hb
    | between => intro b hb; rw [hh] at hb; cases hb
    | fin a => intro b hb; rw [hh] at hb; cases hb
    | mem a => intro b hb; rw [hh] at hb; cases hb
  · exact h

theorem wrK_not_head (s : First.S) (f : ReqFrame) (S' : Statement)
    (h : ∀ b, s.here ≠ .head b) : ∀ b, (wrK s f S').here ≠ .head b :=
  putLive_not_head s _ h

theorem wrK_book (s : First.S) (f : ReqFrame) (S' : Statement) : (wrK s f S').book = s.book :=
  (putLive_book s _).1

theorem wrK_roots (s : First.S) (f : ReqFrame) (S' : Statement) : (wrK s f S').roots = s.roots :=
  (putLive_book s _).2

/-- **THE THREE TESTS ON THE BOOK BEHIND THE CLOSING ARE THOSE IN FRONT.** -/
theorem tests_behind {s s' : First.S} {f : ReqFrame} {S' : Statement} (h : s' = wrK s f S')
    (ft : ℕ) (Lp : Laid) :
    atFirstBook ft s' = atFirstBook ft s ∧ atFirstSeats Lp s' = atFirstSeats Lp s ∧
      atFirstFits s' = atFirstFits s := by
  subst h
  unfold atFirstBook atFirstSeats atFirstFits
  rw [wrK_book, wrK_roots]
  exact ⟨rfl, rfl, rfl⟩

/-- The trees below a piece's base stay, in the form of K10's end's first clause. -/
theorem imp_stays {C : CK} {F : Frame} {T Cl W : Type} (p : Piece C F T Cl W) {u u' : F.E.Str}
    {τ : Iop.Tr (uLT C p.ds)} (h : u' = p.ior.imp u τ) (j x : ℕ) (hj : j < p.base) :
    (strsOf F u').col j x = (strsOf F u).col j x := by
  subst h
  exact (stays_behind C F p.base p.ds u τ).2 j x hj

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.putLive_book
#print axioms VerifiableInference.Desc.LinkJoin.wrK_not_head
#print axioms VerifiableInference.Desc.LinkJoin.wrK_book
#print axioms VerifiableInference.Desc.LinkJoin.wrK_roots
#print axioms VerifiableInference.Desc.LinkJoin.tests_behind
#print axioms VerifiableInference.Desc.LinkJoin.imp_stays
