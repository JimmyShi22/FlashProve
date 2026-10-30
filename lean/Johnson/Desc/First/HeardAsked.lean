-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/HeardAsked.lean: THE REPLY THAT WAS HEARD, AS A TOKEN'S NUMBER, THROUGH THE ONE
READING `S.heard`. One definition and three small theorems. No protocol's soundness is said.

Why. In the record as it is carried the heard element lies at two places, one after the other
(Johnson/Desc/First/StateHeard.lean): the reply's place lays it into the head's own part; the place
behind it lays `out.reply`; the last test reads `out.reply`. A reader of `out.reply` alone
(`S.replyTok?`, State.lean) therefore shows nothing right behind the reply's block and turns one
place later: "the reply's block lays it; no other block turns it" IS FALSE OF THAT READER. `S.heard`
is the reading of which it is meant to be true.
  `S.heardTok?`: `S.replyTok?`'s text at `S.heard` in the place of `out.reply`.
  `S.finAsked_heardTok`: where the number t below the prime was asked and the last test's helper
    says yes, it is t.
  `S.heardTok?_none`: nothing where nothing was heard.
  `isStart_heard`: at a first record (`IsStart`, BordersStart.lean) nothing was heard.

Limits: those of StateHeard.lean. Nothing is said of how the reply came into the record. Nothing on
hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.First.StateHeard
import Johnson.Desc.First.ReplyAsked
import Johnson.Desc.First.BordersStart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First
open OnBytes OnBytes.Model

namespace S

/-- **The heard reply as a token's number**, through the one reading: none until it is heard, and
where what was heard is not a natural number below the field's prime, as ofNat lays one. -/
def heardTok? (s : S) : Option Nat :=
  s.heard.bind fun g => if ofNat g.c0.toNat == g then some g.c0.toNat else none

/-- **Where the number t below the prime was asked, what was heard is the token's number t.** -/
theorem finAsked_heardTok (t : Nat) (ht : t < pW.toNat) (s : S)
    (h : s.finAsked (ofNat t) = true) : s.heardTok? = some t := by
  unfold heardTok?
  rw [heard_of_finAsked _ s h]
  show (if ofNat (ofNat t).c0.toNat == ofNat t then some (ofNat t).c0.toNat else none) = some t
  rw [c0_ofNat t ht, if_pos (beq_self_eq_true _)]

/-- Nothing where nothing was heard. -/
theorem heardTok?_none (s : S) (h : s.heard = none) : s.heardTok? = none := by
  unfold heardTok?
  rw [h]
  rfl

end S

/-- At a first record nothing was heard. -/
theorem isStart_heard {codes : Codes} {req : Array UInt32} {s : S} (h : IsStart codes req s) :
    s.heard = none := by
  rcases h with ⟨c, rfl⟩ | rfl <;> rfl

end VerifiableInference.Desc.First

#print axioms VerifiableInference.Desc.First.S.finAsked_heardTok
#print axioms VerifiableInference.Desc.First.S.heardTok?_none
#print axioms VerifiableInference.Desc.First.isStart_heard
