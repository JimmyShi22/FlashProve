-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TokenSmall.lean.
WHAT IT DOES NOT SHOW. No soundness. That every step between the next token's block and the output
head's leaves the reply: a premise here (rides): the driver's guard asks it of each step. Of
K6Left's
three clauses this pays ONE.
OBJECT. Stored/ReplySeatAt.lean's Reply.blockAt l V (the next token's block as it is seated);
Law/SeatedSays.lean's K6Left, its second clause.
WHAT IT IS. "A HEARD TOKEN IS BELOW V", AS A PROMISE THAT THE NEXT TOKEN's BLOCK MAKES AND EVERY
STEP
THAT LEAVES THE REPLY KEEPS.
  TokSmall V s      every element in the reply's seat is an entry of a vocabulary of V tokens.
  tokSmall_none     it holds where nothing is heard.
  tokSmall_made     behind a yes of the next token's block.
  tokSmall_rides    it rides over a step that leaves the reply.
  tokSmall_pays     it gives K6Left's second clause, at V := W.hS.V.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReplyPins
import Johnson.Desc.Kinds.Law.SeatedSays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Desc.Reply (isToken tokOf)
open VerifiableInference.Desc.First (S)

/-- Every element in the reply's seat is an entry of the vocabulary. -/
def TokSmall (V : Nat) (s : S) : Prop := ∀ x, s.out.reply = some x → isToken V x = true

theorem tokSmall_none (V : Nat) (s : S) (h : s.out.reply = none) : TokSmall V s := by
  intro x hx
  rw [h] at hx
  cases hx

/-- **The next token's block makes it.** -/
theorem tokSmall_made (l V : Nat) {s s' : S} {rs : List Fmt.RoundView}
    {gs : List (List (Nat × List UInt64))} (hd : (Reply.blockAt l V).decide s rs gs = .ok s') :
    TokSmall V s' := by
  obtain ⟨o, h, _, _, _, htok, rfl⟩ := Came.reply_record l V hd
  intro x hx
  have e : h = x := Option.some.inj hx
  rw [← e]
  exact htok

/-- **It rides over a step that leaves the reply.** -/
theorem tokSmall_rides (V : Nat) {s t : S} (h : TokSmall V s) (e : t.out.reply = s.out.reply) :
    TokSmall V t := by
  intro x hx
  exact h x (e ▸ hx)

/-- **It pays K6Left's second clause.** -/
theorem tokSmall_pays (W : OnBytes.Model.Verify.Public) (s : S) (h : TokSmall W.hS.V s) :
    ∀ y, Reply.token (seatAt W.hS (readsOf W)).toSeat s = some y →
      y < (parOf W.hS (workOf W)).sizes.V := by
  intro y hy
  have hy' : (s.out.reply).map tokOf = some y := hy
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp hy'
  have ht := h x hx
  unfold isToken at ht
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
  exact ht.2

end VerifiableInference.Desc.Kinds.Head.Law
