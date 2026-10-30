-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/SentAgree.lean: the description's own test on the shape of a message that
is sent (Johnson/Desc/Own/Sent.lean) says just what the hand-written program's OnBytes.Blk.shapeOk
(OnBytes/Iop/Ground.lean) says, at all arguments. BY rfl: THE TWO TEXTS ARE THE SAME FOUR CONJUNCTS
IN THE SAME ORDER: there is one way to ask them.
A YARDSTICK BESIDE: no block imports this file. It says nothing on whether the test asks enough.
No soundness is claimed.
-/
import Johnson.Desc.Own.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem sentShapeFits_agrees (codes : OnBytes.Codes) (s : OnBytes.OracleShape) :
    OnBytes.Blk.shapeOk codes s = sentShapeFits codes s := rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.sentShapeFits_agrees
