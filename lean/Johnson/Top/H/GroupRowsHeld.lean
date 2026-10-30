-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/GroupRowsHeld.lean: a choice of kept messages in the kept slots of a group of sent
oracle messages with kept main rows, and its laws from laws member by member.

The group's data are `RowsK` (Johnson/Top/H/GroupRowsKept.lean). A choice of kept messages is
`GHeld` (Cb/Ld/LdGroupSeg.lean): whole members, all of whose main rows stand in kept slots, each
with a way back from its main rows to its own word, message and randomness. Here that way back is
a record on one member (`Undo`), and its five laws speak of that member's change of shape alone.
Definitions, statements and proofs.

Main names:
  `Undo C D`: for a member's code C and the code D of its main rows: the native word from the main
    rows (unW); where an entry of the message, of the randomness, is (cJ, cQ).
  `Undo.Laws u pos v`: at the change of shape v of the member, read at pos: unW undoes v on words;
    cJ and cQ name the entries as v does; unW of the rows' encoding is the member's own encoding;
    rows read alike at a position of the group give words read alike where the member is read.
  `RowsK.held R kp sk kq u`: the choice: held is every message with kq that is a member with kp;
    sk names the slot of each main row of a member with kp; u gives its `Undo`.
  `RowsK.held_laws`: `GHeld.Laws`, if the slot that sk names holds that row and every u has its
    laws.
  `Rows.held R kp kq u`, `Rows.held_laws`: the same where whole members are kept (`Rows.keep`):
    the slot of a row is the row itself, so the laws of every u are the one premise.
  `RowsK.held_cl`, `Rows.held_cl`: which messages are held.
Limits: no `Undo` is written here: Johnson/Top/H/MemberHeld.lean has that of a shape of the
programs. kq is any set of names; that it is the set of messages read after the round before the
fold is the caller's matter (Johnson/Top/H/CallerHeld.lean). A member with kp that has not kq is
not held, though its rows stand in slots. The laws leave no room for mask rows that carry
something: every entry of a held member has a place in a main row. The limits of the files named
hold here.

-/
import Johnson.Top.H.GroupRowsKept
import Cb.Ld.LdGroupSeg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb

/-- The way back from a member's main rows: the data. C: the member's code. D: the code of its
main rows. -/
structure Undo {P P' : Type} (C : LdCode GE P') (D : LdCode GE P) where
  /-- the member's native word, from its main rows -/
  unW : D.Word → C.Word
  /-- where an entry of its message, of its randomness, is -/
  cJ : C.J → D.J
  cQ : C.Q → D.Q

namespace Undo
variable {P P' : Type} {C : LdCode GE P'} {D Z : LdCode GE P} (u : Undo C D)

/-- The laws, at a change of shape of the member as it is read at pos. -/
structure Laws (pos : P → P') (v : Reshape (C.atPos pos) (D.pair Z)) : Prop where
  word : ∀ f : C.Word, u.unW (LdCode.fstW (v.wd f)) = f
  upJ : ∀ (w : (C.J → GE) × (C.Q → GE)) j, (v.up w).1 (.inl (u.cJ j)) = w.1 j
  upQ : ∀ (w : (C.J → GE) × (C.Q → GE)) q, (v.up w).2 (.inl (u.cQ q)) = w.2 q
  enc : ∀ m r, u.unW (D.enc m r) = C.enc (fun j => m (u.cJ j)) (fun q => r (u.cQ q))
  loc : ∀ f g x, D.T f x = D.T g x → C.T (u.unW f) (pos x) = C.T (u.unW g) (pos x)

end Undo

namespace RowsK
variable {S : Sig GE} (R : RowsK S) (kp : {o // R.mem o} → Prop) [DecidablePred kp]
  (sk : ∀ a, kp a → Fin (R.nM a) → R.Kp) (kq : S.O → Prop)
  (u : ∀ a, kp a → Undo (S.om a.1).C (R.s.cM.il (Fin (R.nM a))))

/-- The choice of kept messages: the messages with kq that are members with kp. -/
@[reducible] noncomputable def held : GHeld R.Sh kq where
  cl := fun k => ∃ h : R.mem k.1, kp ⟨k.1, h⟩
  decCl := fun k => inferInstanceAs (Decidable (∃ h : R.mem k.1, kp ⟨k.1, h⟩))
  mem := fun k => k.2.fst
  slot := fun k r => sk ⟨k.1.1, k.2.fst⟩ k.2.snd r
  unW := fun k => (u ⟨k.1.1, k.2.fst⟩ k.2.snd).unW
  cJ := fun k => (u ⟨k.1.1, k.2.fst⟩ k.2.snd).cJ
  cQ := fun k => (u ⟨k.1.1, k.2.fst⟩ k.2.snd).cQ

/-- Which messages are held. -/
theorem held_cl (k : {o // kq o}) :
    (R.held kp sk kq u).cl k ↔ ∃ h : R.mem k.1, kp ⟨k.1, h⟩ := Iff.rfl

/-- The laws of the choice, from the slots' law and the laws member by member. -/
theorem held_laws (hk : ∀ a k r, R.kept (sk a k r) = ⟨a, r⟩)
    (hu : ∀ a k, (u a k).Laws (R.pos a) (R.view a)) : (R.held kp sk kq u).Laws where
  kept := fun k r => hk ⟨k.1.1, k.2.fst⟩ k.2.snd r
  word := fun k f => (hu ⟨k.1.1, k.2.fst⟩ k.2.snd).word fun p => f ⟨⟨k.1.1, k.2.fst⟩, p⟩
  upJ := fun k w j => (hu ⟨k.1.1, k.2.fst⟩ k.2.snd).upJ (Reshape.atP w ⟨k.1.1, k.2.fst⟩) j
  upQ := fun k w q => (hu ⟨k.1.1, k.2.fst⟩ k.2.snd).upQ (Reshape.atP w ⟨k.1.1, k.2.fst⟩) q
  enc := fun k m r => (hu ⟨k.1.1, k.2.fst⟩ k.2.snd).enc m r
  loc := fun k f g x h => (hu ⟨k.1.1, k.2.fst⟩ k.2.snd).loc f g x h

end RowsK

namespace Rows
variable {S : Sig GE} (R : Rows S) (kp : {o // R.mem o} → Prop) [DecidablePred kp]
  (kq : S.O → Prop) (u : ∀ a, kp a → Undo (S.om a.1).C (R.s.cM.il (Fin (R.nM a))))

/-- The choice of kept messages where whole members are kept: the slot of a row is the row. -/
@[reducible] noncomputable def held : GHeld (R.keep kp).Sh kq :=
  (R.keep kp).held kp (fun a k r => ⟨⟨a, k⟩, r⟩) kq u

/-- Which messages are held. -/
theorem held_cl (k : {o // kq o}) :
    (R.held kp kq u).cl k ↔ ∃ h : R.mem k.1, kp ⟨k.1, h⟩ := Iff.rfl

/-- The laws of the choice, from the laws member by member. -/
theorem held_laws (hu : ∀ a k, (u a k).Laws (R.pos a) (R.view a)) : (R.held kp kq u).Laws :=
  RowsK.held_laws (R.keep kp) kp (fun a k r => ⟨⟨a, k⟩, r⟩) kq u (fun _ _ _ => rfl) hu

end Rows

end Johnson.Top.H
