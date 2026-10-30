-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/ReplyAt.lean: WHERE THE REPLY IS LAID, AS A TERM ON THE WRITTEN
LIST. The first chain's thread at the library's head (`lettersHead`, Honest/Thread/FirstHead.lean)
has a letter b₀: from that border on its `rides` says that the state's reply is what the instance
asks. The laws at the members hold that letter from one side alone (0 < b₀; b₀ ≠ b + 1 at each
member that does not lay the reply): nothing says where it is. Here the number that is meant, made
of the library's written list of places (`P5J.At.ps`) by the library's own test (`hearsReply`,
Johnson/Desc/First/Driver/Chain.lean: the place's kind is K7), and one closed fact on it. One
definition: a number; two closed facts by the kernel, the second a control; two corollaries.

  `b0Head`   THE NUMBER: the border behind the first place of the list that hears the reply
  `b0Head_closed`   just one place of the list hears the reply; the number is 339
  `b0Head_control`   a control: without member 338 no place of the list hears the reply
  `b0Head_pos`, `b0Head_ne`   what the laws at the members ask of the letter, at this number

`lettersHead` KEEPS ITS LETTER: this number is meant to be laid for it at the last laying.

Credit. THE KIND K5's LEMMAS HAD THE SAME TERM FIRST: their
`K5.replyBorder` (Honest/K5/Law/ReplyAt.lean) is this definition's right side to the letter; their
closed fact holds that number against their own twelve borders and does not name it. This file names
the number, for the authors of every kind, and stands over the library alone. Where both are
imported the two are one by unfolding.

Limits. THE FULL SIZE's WRITTEN LIST ALONE. It speaks of a list of places: of no run, no state, no
thread. None is one of the library's goals. This file proves nothing about soundness, completeness,
hiding or any other property of the protocol.
-/
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread
open VerifiableInference.Desc.First (hearsReply)

/-- **The border behind the one place of the written list whose decision may write the reply.** It
is a definition: a number, made of the written list. -/
def b0Head : Nat := P5J.At.ps.findIdx hearsReply + 1

set_option maxRecDepth 1000000 in
/-- **Just one place of the written list hears the reply; it is member number 338.** A closed fact,
by the kernel. -/
theorem b0Head_closed : (P5J.At.ps.filter hearsReply).length = 1 ∧ b0Head = 339 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: without that member no place of the list hears the reply. -/
theorem b0Head_control : ((P5J.At.ps.eraseIdx 338).filter hearsReply).length = 0 := by
  decide +kernel

theorem b0Head_pos : 0 < b0Head := by
  rw [b0Head_closed.2]
  omega

theorem b0Head_ne {b : Nat} (h : b ≠ 338) : b0Head ≠ b + 1 := by
  rw [b0Head_closed.2]
  omega

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.b0Head_closed
#print axioms ProofFile.Honest.FirstThread.b0Head_control
#print axioms ProofFile.Honest.FirstThread.b0Head_pos
#print axioms ProofFile.Honest.FirstThread.b0Head_ne
