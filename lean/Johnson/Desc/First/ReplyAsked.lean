-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/ReplyAsked.lean: WHAT THE LAST TEST'S HELPER `S.finAsked` GIVES ON THE REPLY.
Three small theorems on Johnson/Desc/First/State.lean's own text. No protocol's soundness is said.

What is said.
  `finAsked_reply`: where `finAsked asked s` says yes, the reply that the record holds IS what was
    asked.
  `c0_ofNat`: a natural number below the prime, laid as an element, is read back by its first word.
  `finAsked_tok`: so where what was asked is the number t below the prime, laid as an element, the
    record's heard reply, read as a token's number (`replyTok?`), is t.

What it is for: a description's last test that calls `finAsked` at the instance's asked reply then
has "the last test's yes: the reply heard is the one asked" as a theorem, once the instance's asked
reply is tied to the request's own (an equation on the map of instances, in other files).

Silly members. A record that holds no reply: `finAsked` says no at it: the theorems are idle there,
rightly. Limits: nothing is said of how the reply came into the record. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

namespace S

/-- **The last test's helper's yes: what the record holds as heard is what was asked.** -/
theorem finAsked_reply (asked : E) (s : S) (h : s.finAsked asked = true) :
    s.out.reply = some asked := by
  unfold finAsked at h
  have h1 := Eq.mp (Bool.and_eq_true _ _) h
  have h2 := Eq.mp (Bool.and_eq_true _ _) h1.1
  exact eq_of_beq h2.2

/-- A number below the prime, laid as an element, is read back by the element's first word. -/
theorem c0_ofNat (t : Nat) (ht : t < pW.toNat) : (ofNat t).c0.toNat = t := by
  show ((t % pW.toNat).toUInt64).toNat = t
  rw [Nat.mod_eq_of_lt ht]
  have hp : pW.toNat < 2 ^ 64 := pW.toNat_lt
  show (UInt64.ofNat t).toNat = t
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_trans ht hp)]

/-- **Where the number t below the prime was asked, the heard reply is the token's number t.** -/
theorem finAsked_tok (t : Nat) (ht : t < pW.toNat) (s : S) (h : s.finAsked (ofNat t) = true) :
    s.replyTok? = some t := by
  unfold replyTok?
  rw [finAsked_reply _ s h]
  show (if ofNat (ofNat t).c0.toNat == ofNat t then some (ofNat t).c0.toNat else none) = some t
  rw [c0_ofNat t ht, if_pos (beq_self_eq_true _)]

end S

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.S.finAsked_reply
#print axioms VerifiableInference.Desc.First.S.c0_ofNat
#print axioms VerifiableInference.Desc.First.S.finAsked_tok
