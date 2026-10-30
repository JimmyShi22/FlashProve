-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyTokIs.lean.
WHAT IT DOES NOT SHOW. No soundness. That a token stands in the reply's seat, or that what stands
there is an entry of the vocabulary: the premise TokSmall (Law/TokenSmall.lean: made by the next
token's block, kept by every step that leaves the reply). That the vocabulary's size is at most the
field's prime: a premise on a public number (hV). Nothing on the witness's token.
LETTERS. No "there is".
OBJECT. Two readers of the one seat of the heard reply, S.out.reply: the record's own S.replyTok?
(Desc/First/State.lean: the element's first word, IF the element is the field's element of that
number; else nothing) and the kinds' Reply.token at the seat out.reply (Kinds/ReplyKind.lean: the
element's first word, through tokOf and nothing else): the output head's letter Token is the second
(Law/ETies.lean: given_letters).
USER. Whoever ties the token that the table's terms read off the record (through S.replyTok?) to the
token at which the output head's laws are stated.
WHAT IT IS. ONE NUMBER, TWO READERS: WHERE WHAT STANDS IN THE REPLY's SEAT IS AN ENTRY OF THE
VOCABULARY, THE RECORD's OWN READER AND THE KINDS' READER ANSWER THE SAME; AND THE NUMBER IS BELOW
THE VOCABULARY's SIZE.
  replyTok_is       the equation of options. (Its heart is this library's ofNat_token,
                    Law/ReplyHears.lean: the guard inside S.replyTok? holds of every token.)
  replyTok_lt       what the record's reader answers is below V.
A search (statements that name ofNat with c0.toNat, over Desc/ and OnBytes/
in another version; every line that names replyTok? there, in the table's files and in
K6's and K7's files, in versions other than these): ofNat_token and
joined_hearsTok (this library's) alone; of S.replyTok? others say only that a block leaves it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.ReplyHears
import Johnson.Desc.Kinds.Law.TokenSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

/-- **ONE NUMBER, TWO READERS.** -/
theorem replyTok_is (V : Nat) (hV : V ≤ OnBytes.pW.toNat) (s : S) (h : TokSmall V s) :
    s.replyTok? = Reply.token Reply.seatAt s := by
  show s.replyTok? = s.out.reply.map OnBytes.Desc.Reply.tokOf
  unfold S.replyTok?
  cases hr : s.out.reply with
  | none => rfl
  | some g =>
    have e := ofNat_token V hV g (h g hr)
    show (if OnBytes.Model.ofNat g.c0.toNat == g then some g.c0.toNat else none) = _
    rw [e, if_pos (beq_self_eq_true _)]
    rfl

/-- What the record's reader answers is below the vocabulary's size. -/
theorem replyTok_lt (V : Nat) (s : S) (h : TokSmall V s) (n : Nat) (hn : s.replyTok? = some n) :
    n < V := by
  unfold S.replyTok? at hn
  cases hr : s.out.reply with
  | none => rw [hr] at hn; cases hn
  | some g =>
    rw [hr] at hn
    have hn' : (if OnBytes.Model.ofNat g.c0.toNat == g then some g.c0.toNat else none) = some n :=
      hn
    have ht := h g hr
    simp only [OnBytes.Desc.Reply.isToken, Bool.and_eq_true, decide_eq_true_eq] at ht
    split at hn'
    · obtain rfl := Option.some.inj hn'
      exact ht.2
    · cases hn'

end VerifiableInference.Desc.Kinds.Head.Law
