-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/ReqBoth.lean: the two strings that a proof file's first chain statement takes
from the request, the item `request` and the request file's bytes, as one function of a typed
instance that holds the public input; and the equation at a call.



A definition and one law. Johnson/Maker/Page/ReqPub.lean writes the item (`HoldsPub.reqX`) from the
instance's public input. The request's file is a field of the same public input: so both strings
come from one source.

Main names:
  `HoldsPub.req2 H x`: the item of the public input of x, and that input's request file.
  `req2_early`: at the early part of an instance that holds the public input u, where the program
    forms the item: the pair is (item, u.request).
What is asked, by name: hx: the instance holds the public input u. hi: the program forms the item.
No letter stands under "there is".

Limits: those of Johnson/Maker/Page/ReqPub.lean: where H is a letter, hx pins nothing of the
instance. That two instances have two pairs is not claimed. Nothing on soundness.
-/
import Johnson.Maker.Page.ReqPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Session
open OnBytes
open OnBytes.TieK (ProofPub)

variable {X : Type} {early : X → X}

/-- **The value of the letter `reqX`**: the item of the instance's public input, and that input's
request file. -/
def HoldsPub.req2 (H : HoldsPub X early) (x : X) : ByteArray × ByteArray :=
  (H.reqX x, (H.pub x).request)

/-- **The equation.** -/
theorem req2_early (H : HoldsPub X early) (x : X) (u : ProofPub) (item : ByteArray)
    (hx : H.pub x = u) (hi : Proof.requestItem u.pol u.KL u.request = some item) :
    H.req2 (early x) = (item, u.request) := by
  unfold HoldsPub.req2
  rw [reqX_early H x u item hx hi, (H.early_same x).2.2, hx]

end Johnson.Session
