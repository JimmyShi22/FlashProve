-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/ReplyNat.lean.
WHAT IT DOES NOT SHOW. No soundness. THAT TokSmall HOLDS AT A STATE IS A PREMISE: it is not shown
here of any state, reached or not. IT DOES NOT FOLLOW FROM THE PUBLIC TEST "a small token is heard"
(Stored/FillK6K7.lean: tokenHeardB), which reads the heard element's first coordinate alone.
WORDS. "The verifier's state": the value of type S that the sub-protocols hand on. TokSmall V s
(Law/TokenSmall.lean): whatever lies in the reply's seat is an entry of the vocabulary: its second
and third coordinates are 0 and its first is below V.
LETTERS. No "there is". V: the vocabulary's size; hV: it is at most the prime.
OBJECT. The heard element in the verifier's state (out.reply) and the field's element of a number
(OnBytes.Model.ofNat).
USER. The lookup's files' sentence that the state's own reader of the token answers at the head's
third place (Desc/Sound/MgAt/K3HeadIn.lean: headMg_tokIn: its premise hNat, to the letter).
WHAT IT IS. UNDER TokSmall THE HEARD ELEMENT IS THE FIELD's ELEMENT OF ITS OWN FIRST COORDINATE.
  replyNat_of_tokSmall   by Law/ReplyHears.lean: ofNat_token.
NEAREST RELATIVE: Law/ReplyTokIs.lean: replyTok_is: under the same premise the two readers of the
token agree.

-/
import Johnson.Desc.Kinds.Law.ReplyHears
import Johnson.Desc.Kinds.Law.TokenSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open VerifiableInference.Desc.First (S)

/-- **Under TokSmall the heard element is the field's element of its own first coordinate.** -/
theorem replyNat_of_tokSmall (V : Nat) (hV : V ≤ OnBytes.pW.toNat) (s : S) (h : TokSmall V s) :
    ∀ g, s.out.reply = some g → OnBytes.Model.ofNat g.c0.toNat = g :=
  fun g hg => ofNat_token V hV g (h g hg)

end VerifiableInference.Desc.Kinds.Head.Law

#print axioms VerifiableInference.Desc.Kinds.Head.Law.replyNat_of_tokSmall
