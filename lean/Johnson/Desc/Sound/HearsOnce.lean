-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/HearsOnce.lean: THE TWO SMALL SHAPES THAT THE REPLY's ROW WANTS BESIDE Block.Leaves (Johnson/Desc/Sound/FoldHeard.lean), AND THAT THE
KIND K7 HAS THE FIRST.

  Block.HearsOnce r: where the block's decision goes on, r of the record in front is none and r of the record behind is some value.
  Block.Under b' b: where b' says yes, b says the same yes, on the same rounds and columns: so is a block with a test more in front of or behind its
    decision, and a block with another name, place or test on the plan.
  leaves_of_under, hearsOnce_of_under: both shapes go from b to b'. under_refl, under_of_decide, Block.Under.trans.
  hearsOnce_andThen, hearsOnce_andThen': a block that hears once, joined with one that leaves r, behind it or in front of it.
  **Kinds.Reply.kind_hearsOnce**: K7's kind, at EVERY seat whose reply reads back what setReply lays: by "heard once" and the one laying.

Silly members. A block that never says yes has all three shapes for nothing. A block that says yes to all and writes nothing has Leaves r and fails
HearsOnce r at every record. r := fun _ => none: HearsOnce r holds of no block that ever says yes.
Every "there is", walked: no statement has one.
Nearest kin: Block.Lays h rd (FoldHeard.lean): what is laid, as a function of the rounds shown; it does not say that nothing was heard in front.
reply_blockAt_lays (declared nowhere in this library) is in that shape. Block.Under: none found by shape; Piece.under (Johnson/Desc/Plain/LiftBelow.lean) is another thing:
the piece with the test "below the prime" in front: its block stands under the piece's own in this file's sense.
Limits. Of decide alone. K7's kind as it stands (Johnson/Desc/Kinds/ReplyKind.lean, ReplyBlock.lean); general in the seat.

-/
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Desc.Kinds.ReplyBlock

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

variable {S Cl α β : Type}

/-- Where the block's decision goes on: nothing was heard in front, and something is heard behind. -/
def Block.HearsOnce (r : S → Option β) (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b.decide s rs gs = .ok s' → r s = none ∧ (r s').isSome = true

/-- Where b' says yes, b says the same yes. -/
def Block.Under {Cl' : Type} (b' : Block S Cl') (b : Block S Cl) : Prop :=
  ∀ s rs gs s', b'.decide s rs gs = .ok s' → b.decide s rs gs = .ok s'

theorem under_refl (b : Block S Cl) : b.Under b := fun _ _ _ _ H => H

theorem under_of_decide {Cl' : Type} {b' : Block S Cl'} {b : Block S Cl} (e : b'.decide = b.decide) :
    b'.Under b := fun s rs gs s' H => by rw [e] at H; exact H

theorem Block.Under.trans {Cl' Cl'' : Type} {b'' : Block S Cl''} {b' : Block S Cl'} {b : Block S Cl}
    (h₁ : b''.Under b') (h₂ : b'.Under b) : b''.Under b :=
  fun s rs gs s' H => h₂ s rs gs s' (h₁ s rs gs s' H)

theorem leaves_of_under {Cl' : Type} {b' : Block S Cl'} {b : Block S Cl} {h : S → α} (u : b'.Under b)
    (hb : b.Leaves h) : b'.Leaves h := fun s rs gs s' H => hb s rs gs s' (u s rs gs s' H)

theorem hearsOnce_of_under {Cl' : Type} {b' : Block S Cl'} {b : Block S Cl} {r : S → Option β}
    (u : b'.Under b) (hb : b.HearsOnce r) : b'.HearsOnce r :=
  fun s rs gs s' H => hb s rs gs s' (u s rs gs s' H)

/-- It hears once, and what is joined behind it leaves r. -/
theorem hearsOnce_andThen {r : S → Option β} (name : String) {p q : Block S Cl} (hp : p.HearsOnce r)
    (hq : q.Leaves r) : (Block.andThen name p q).HearsOnce r := by
  intro s rs gs s' H
  obtain ⟨t, ht, H⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨h0, h1⟩ := hp _ _ _ _ ht
  exact ⟨h0, by rw [hq _ _ _ _ H]; exact h1⟩

/-- The like with the block that leaves r in front. -/
theorem hearsOnce_andThen' {r : S → Option β} (name : String) {p q : Block S Cl} (hp : p.Leaves r)
    (hq : q.HearsOnce r) : (Block.andThen name p q).HearsOnce r := by
  intro s rs gs s' H
  obtain ⟨t, ht, H⟩ := bindOk (x := p.decide s (rs.take p.rounds.length) (gs.take p.openings)) H
  obtain ⟨h0, h1⟩ := hq _ _ _ _ H
  exact ⟨by rw [← hp _ _ _ _ ht]; exact h0, h1⟩

namespace Kinds.Reply
open OnBytes.Desc.Reply (readReply isToken)

/-- **K7 hears once**, at every seat whose reply reads back what setReply lays. -/
theorem kind_hearsOnce (L : Seat S) (hL : ∀ s x, L.reply (L.setReply s x) = some x)
    (link piece V : Nat) : (kind (Cl := Cl) L link piece V).HearsOnce L.reply := by
  intro s rs gs s' H
  have H' : decideE V L s rs = .ok s' := H
  match rs, H' with
  | [r], H' =>
    have h1 : (if (L.reply s).isSome then Except.error "heard once" else
      match readReply r with
      | none => Except.error "one element, nothing drawn"
      | some h => if isToken V h then Except.ok (L.setReply s h) else Except.error "a token") =
        Except.ok s' := H'
    split at h1
    · exact nomatch h1
    · rename_i hn
      split at h1
      · exact nomatch h1
      · split at h1
        · have e := Except.ok.inj h1
          rw [← e, hL]
          exact ⟨Option.not_isSome_iff_eq_none.1 hn, rfl⟩
        · exact nomatch h1
  | [], H' => exact nomatch H'
  | _ :: _ :: _, H' => exact nomatch H'

end Kinds.Reply

end VerifiableInference.Desc

#print axioms VerifiableInference.Desc.leaves_of_under
#print axioms VerifiableInference.Desc.hearsOnce_of_under
#print axioms VerifiableInference.Desc.hearsOnce_andThen
#print axioms VerifiableInference.Desc.hearsOnce_andThen'
#print axioms VerifiableInference.Desc.Kinds.Reply.kind_hearsOnce
