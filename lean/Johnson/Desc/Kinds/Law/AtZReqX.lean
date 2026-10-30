-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/AtZReqX.lean: rqAt (Johnson/Desc/Kinds/Head/AtZ.lean) AGAINST THE LIBRARY's
REQUEST OF AN INSTANCE (reqX, Law/HeadPartsAtX.lean): ONE LETTER, where the words of
p.request are requestWordsOf x. STATED AND PROVED: one call of requestOf_words.
  rq_is_reqX: words32 p.request = OnBytes.Flat.requestWordsOf x → rqAt Z p = Law.reqX x.
WHAT IT DOES NOT SAY. THE PREMISE IS SHOWN BY NOBODY HERE: that the bytes of a request file which
passes the tests spell requestWordsOf of the instance that the library's parse makes of them (the
words' reading and the bytes' parse agree) is other files' to show. x is a free
letter beside p: the premise alone ties them. It stands apart from Law/AtZLaw.lean because
Law/HeadPartsAtX.lean is on no list yet. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Head.AtZ
import Johnson.Desc.Kinds.Law.HeadPartsAtX

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.AtZ

open Inst.Model (ppref Instance)

/-- **rqAt is the library's request of the instance whose request file's words p.request
spells.** -/
theorem rq_is_reqX (Z : ProofFile.Pub) (p : ProofFile.InstPub) (x : Instance ppref)
    (h : OnBytes.Model.Verify.words32 p.request = OnBytes.Flat.requestWordsOf x) :
    rqAt Z p = Law.reqX x :=
  Law.Came.requestOf_words (Z.s₀.withReq (OnBytes.Model.Verify.words32 p.request)) x h

end VerifiableInference.Desc.Kinds.Head.AtZ

#print axioms VerifiableInference.Desc.Kinds.Head.AtZ.rq_is_reqX
