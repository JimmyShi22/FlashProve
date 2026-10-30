-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Thread/ReplyIs.lean: THE BORDER BEHIND THE MEMBER THAT HEARS THE
REPLY, IN OUR NAME AND IN THE NAME OF THE HOUSE OF THE KIND K5, IS ONE NUMBER. Our
`b0Head` (Honest/Thread/ReplyAt.lean) and the house's `K5.replyBorder` (Honest/K5/Law/ReplyAt.lean)
are one term over the library's written list of places: so a law of the house's at its name can be
called at ours. Two lemmas; no definition.

  `b0Head_is_replyBorder`   the two names are one number, by unfolding
  `b0Head_ne_k5`   that border is not 28 g + 19, at whatever g: so it is not the one right behind a
     member of the kind K5

Limits. That the thread's letter b₀ is laid at this number is said by nobody here. None is one of
the library's goals. Nothing on any property.

-/
import Johnson.Desc.ProofFile.Honest.Thread.ReplyAt
import Johnson.Desc.ProofFile.Honest.K5.Law.ReplyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.FirstThread

theorem b0Head_is_replyBorder : b0Head = K5.replyBorder := rfl

theorem b0Head_ne_k5 (g : Nat) : b0Head ≠ K5.borderOf g + 1 :=
  b0Head_ne (by unfold K5.borderOf; omega)

end ProofFile.Honest.FirstThread

#print axioms ProofFile.Honest.FirstThread.b0Head_is_replyBorder
#print axioms ProofFile.Honest.FirstThread.b0Head_ne_k5
