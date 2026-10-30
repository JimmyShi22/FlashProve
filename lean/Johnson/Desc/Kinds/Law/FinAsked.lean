-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/FinAsked.lean.
WHAT IT DOES NOT SHOW. No soundness. That a description's last test asks S.finAsked, and that the
record at the end still holds the request's words that its start tested: not here. TWO PREMISES
BESIDE THE LAST TEST: the record's own test on the request (S.reqOk, asked where the record starts),
at the record at the end; and that the asked element is an entry of the vocabulary: the next
token's block asks that of what it HEARS, and the last test makes the two one: fin_of_heard takes it
in that form.
OBJECT. Desc/First/State.lean's S.finAsked: the helper for a description's last test; and
Desc/Kinds/ReplyKind.lean's fin, which the laws on the next token take as a premise, at the one
seat of the heard reply (Stored/ReplySeatAt.lean: Reply.seatAt; the output head's seat reads the
same field).
WHAT IT IS. WHERE THE RECORD's LAST TEST SAYS YES, THE KIND's PART OF THE LAST TEST SAYS YES, at the
request's own numbers in the record and the asked element's number.
  fin_of_finAsked   at Reply.seatAt.
  fin_at_head       the same at the output head's seat (the laws' letter L.toSeat).
  fin_of_heard      with "every heard element is a token" in the place of "the asked one is".

-/
import Mathlib
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes (E)
open OnBytes.Desc.Reply (isToken tokOf replyGate reqForm)
open VerifiableInference.Desc.First (S)

/-- **The record's last test gives the kind's.** -/
theorem fin_of_finAsked (V T : Nat) (asked : E) (s : S) (h : s.finAsked asked = true)
    (ht : isToken V asked = true) (hq : s.reqOk T V = true) :
    Reply.fin V T s.rowR s.rowE (tokOf asked) Reply.seatAt s = true := by
  unfold S.finAsked at h
  unfold S.reqOk at hq
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
    decide_eq_true_eq, beq_iff_eq, Bool.or_eq_false_iff] at h hq
  obtain ⟨⟨_, hr⟩, h3⟩ := h
  obtain ⟨⟨hsz, _⟩, hre, heT⟩ := hq
  have hT : s.reqT = T := by
    unfold S.reqT
    omega
  unfold Reply.fin
  have e1 : Reply.seatAt.reply s = some asked := hr
  rw [e1]
  unfold replyGate reqForm
  simp only [ht, Bool.true_and, beq_self_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true, beq_iff_eq]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  rcases h3 with h3 | h3
  · left
    rw [hT] at h3
    omega
  · right
    rw [h3]
    rfl

/-- The same at the output head's seat. -/
theorem fin_at_head (hS : OnBytes.Model.Head.Shape) (iU3 V T : Nat) (asked : E) (s : S)
    (h : s.finAsked asked = true) (ht : isToken V asked = true) (hq : s.reqOk T V = true) :
    Reply.fin V T s.rowR s.rowE (tokOf asked) (seatAt hS iU3).toSeat s = true :=
  fin_of_finAsked V T asked s h ht hq

/-- With the next token's block's own test, carried to the end, in the place of the premise on what
is asked. -/
theorem fin_of_heard (V T : Nat) (asked : E) (s : S) (h : s.finAsked asked = true)
    (ht : ∀ x, s.out.reply = some x → isToken V x = true) (hq : s.reqOk T V = true) :
    Reply.fin V T s.rowR s.rowE (tokOf asked) Reply.seatAt s = true := by
  refine fin_of_finAsked V T asked s h (ht asked ?_) hq
  unfold S.finAsked at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1.2

end VerifiableInference.Desc.Kinds.Head.Law
