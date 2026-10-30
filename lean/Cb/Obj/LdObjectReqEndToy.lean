-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectReqEndToy.lean: at the toy: the names of the coefficients of the batching's hiding
polynomial (`ReToy.WBt`).

A request's preamble is an interactive oracle reduction from a request to claims on the encoded
index and on the oracles that it leaves. Its last moves, the final batching, make the claims on the
encoded index that are still pending into one.
One definition. No parameter of a protocol.
































Limits: this file says nothing on the moves of a request. Nothing on the size of errors.
One field: the end of a toy request over two different fields is Cb/GlVal/GlToyReqEnd.lean.



Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectReqEndProofs
import Cb.Obj.LdObjectToyConf7

set_option autoImplicit false

namespace Cb
namespace ReToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy LdToy7

noncomputable section

/-- The names of the coefficients of the batching's hiding polynomial. -/
abbrev WBt : Type := PIdx (List.replicate 1 (pfCube K 2))

end
end ReToy

end Cb
