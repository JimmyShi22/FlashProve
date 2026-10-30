-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
This file stands over Johnson/Desc/Block.lean and Johnson/Desc/First/State.lean,
and over the seats that go with them (Johnson/Stored/HeadSeatAt.lean,
ReplySeatAt.lean).


Johnson/Desc/Kinds/Law/ReplyPins.lean: THE NEXT TOKEN's ROW OF THE TABLE OF JOINTS, FROM THE FOLD's OWN CALL Block.step OF THE BLOCK AS IT IS SEATED (Reply.blockOf W l, Johnson/Stored/ReplySeatAt.lean), in the form of Law/RowPins.lean: STATED AND PROVED. The table's
row: it closes "every key of every call of the head's lookup is a row of its table" AT THE WITNESS's OWN TOKEN, it opens the same sentence AT THE TOKEN THAT THE RECORD HAS HEARD, and its extractor LAYS the heard token into the witness.
NO CHALLENGE IS DRAWN IN ITS ONE ROUND: THE RULE OF BAD ELEMENTS IS EMPTY, the ceiling 0, "no bad draw" holds of all rounds.
  reply_record   THE RECORD BEHIND, WRITTEN OUT: the record in front stands in the head's link, entered and not yet opened, nothing heard; the record behind is that record with ONE FIELD laid: out.reply := some h, h an
                 element that is a token of the vocabulary. Nothing else turns: a mark stays; no mark is laid.
  LookCallsAt    the sentence, at a record's public request, a token y and cells c (HeadTablesLaw.lean: HeadParts.lookCalls).
  K7Out · K7In · RowReplyStatement · rowReply    where the step goes on: the seat was empty in front; behind it holds a token y below V; and what the row opens at the record behind gives what it closes at the record in front AT THAT y.
WHAT IT DOES NOT SAY. (That the token laid here is the token that the output head reads is no debt any more: the heard reply has one home, out.reply, and the head's seat takes this seat by name.) That the heard token is the asked
one: the last test's (Law/K07Statement.lean). That tab is the record's table, c the committed cells: letters (Law/RowPins.lean says of c what holds here too: tied to nothing in front; here no draw can profit of it). That a description seats this text: not here.
OwnOfRule is not called (Law/RowPins.lean: why). Nothing on chance: there is none.

-/
import Mathlib
import Johnson.Stored.ReplySeatAt
import Johnson.Desc.Kinds.HeadTablesLaw
import Johnson.Desc.Kinds.Law.ReplyProof
import Johnson.Desc.Kinds.Law.RowPins

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Desc.Reply (isToken tokOf readReply)
open Norm (lt ls d lPd S2 T)
open VerifiableInference.Desc.First (S HeadOwn)

/-- Every place of every call's key table is a row of that call's table: at the public record's sizes and policy, a record's public request, a token y and cells c. -/
def LookCallsAt (W : OnBytes.Model.Verify.Public) (tab : Nat → Nat) (s : S) (y : Nat) (c : NCells) :
    Prop :=
  let _ : Sizes := sizesOf W.hS
  let _ : Policy := (parOf W.hS 0).policy
  let _ : Request := requestOf s
  let _ : Token := ⟨y⟩
  ∀ call, call < 6 → ∀ col, col < 2 ^ lJ (parOf W.hS 0).floor (callKeys call) → ∀ t, t < T →
    InTable tab call (keyTable c call col t)

/-- What the row opens: the sentence at the token that the record has heard. -/
def K7Out (W : OnBytes.Model.Verify.Public) (tab : Nat → Nat) (s' : S) (c : NCells) : Prop :=
  ∃ y, Reply.token Reply.seatAt s' = some y ∧ LookCallsAt W tab s' y c

/-- What it closes: the sentence at the witness's own token. -/
def K7In (W : OnBytes.Model.Verify.Public) (tab : Nat → Nat) (s : S) (c : NCells) (y : Nat) : Prop :=
  LookCallsAt W tab s y c

/-- **THE NEXT TOKEN's ROW.** -/
def RowReplyStatement : Prop :=
  ∀ (W : OnBytes.Model.Verify.Public) (l firstTree : Nat) (s : S) (tab : Nat → Nat) (c : NCells)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (s' : S) (n : Nat),
    (Reply.blockOf W l).step firstTree s rs cols = .ok (s', n) →
    Reply.token Reply.seatAt s = none ∧ s'.failed = s.failed ∧
    ∃ y, Reply.token Reply.seatAt s' = some y ∧ y < W.hS.V ∧ (K7Out W tab s' c → K7In W tab s c y)

namespace Came

/-- **THE RECORD BEHIND, WRITTEN OUT.** -/
theorem reply_record (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s') :
    ∃ (o : HeadOwn) (h : E), s.here = .head o ∧ o.opened = false ∧ s.out.reply = none ∧
      isToken V h = true ∧ s' = { s with out := { s.out with reply := some h } } := by
  unfold Reply.blockAt Reply.entered at hd
  dsimp only at hd
  split at hd
  · rename_i o ho
    split at hd
    · cases hd
    · rename_i hop
      have hd2 : Reply.decideE V Reply.seatAt s rs = .ok s' := hd
      have hrep : Reply.seatAt.reply s = s.out.reply := rfl
      unfold Reply.decideE at hd2
      split at hd2
      · split at hd2
        · cases hd2
        · rename_i hnone
          split at hd2
          · cases hd2
          · rename_i h hr
            split at hd2
            · rename_i htok
              simp only [Except.ok.injEq] at hd2
              refine ⟨o, h, ho, by simpa using hop, ?_, htok, ?_⟩
              · rw [hrep] at hnone
                simpa using hnone
              · rw [← hd2]
                rfl
            · cases hd2
      · cases hd2
  · cases hd

theorem rowReply : RowReplyStatement := by
  intro W l firstTree s tab c rs cols s' n hstep
  obtain ⟨gs, hd⟩ := step_decide firstTree (Reply.blockOf W l) s rs cols s' n hstep
  obtain ⟨o, h, ho, _, hnone, htok, rfl⟩ := reply_record l W.hS.V hd
  have t0 : Reply.token Reply.seatAt s = none := by
    simp [Reply.token, Reply.seatAt, hnone]
  have t1 : Reply.token Reply.seatAt { s with out := { s.out with reply := some h } }
      = some (tokOf h) := by
    simp [Reply.token, Reply.seatAt]
  refine ⟨t0, rfl, tokOf h, t1, tokOf_lt htok, ?_⟩
  rintro ⟨y, hy, hlook⟩
  rw [t1] at hy
  obtain rfl : tokOf h = y := Option.some.inj hy
  exact hlook

end Came

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.reply_record
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.rowReply
