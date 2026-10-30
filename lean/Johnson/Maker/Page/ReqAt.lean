-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Maker/Page/ReqAt.lean: how the two strings that the statement takes from the request (the
value of the item `request`; the request file's bytes) come out of the typed instance in a proof
file's first chain query: a value for the page's letter `req`, and what the premise on it comes to.

The verifier of a proof file hands its chains the instance `xinBA r₀ (x, rec) = some (some x, r₀,
r₀)` (Johnson/TypedOracleCompiler/RecCompile/CmsAns.lean); the first query holds its early part, and the carrier's
`early` works on the first component alone (Johnson/RecCompile/Cms.lean). The page spells the first
chain's statement from that typed value through a function `req` into two strings.

Main names.
  `reqOf reqX`: the two strings `reqX x` of the instance x in the first component; two empty strings
    where there is none.
  `early_xinBA`: the early part of what the verifier hands on is `(some (L.early x), r₀, r₀)`.
  `req_xinBA`: at `req := reqOf reqX` the strings that the page takes out of the first query's
    instance are `reqX (L.early x)`.
  `hreq_of`: so the premise "these are the item's value and the file's bytes" comes to
    `reqX (L.early x) = (request, words)`.

Limits: the type of instances is a letter, and so is reqX: that `reqX` gives the value of the
statement's item `request` and the request file's bytes is said of no function here, and a constant
function is a value of it.
The record in the typed instance is the fixed r₀: the bytes do not hang on the session's record.
Nothing on soundness.


-/
import Johnson.TypedOracleCompiler.RecCompile.CmsAns

set_option autoImplicit false

namespace OnBytes.Maker.Page
open TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {L : HolographicProtocol I X} (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
  (r₀ : L.Rec)

/-- The two strings of the instance in the first component (the item's value, then the request
file's bytes); two empty strings where there is none. -/
def reqOf (reqX : X → ByteArray × ByteArray) (z : L.XC) : ByteArray × ByteArray :=
  (z.1.map reqX).getD default

/-- The early part of what a proof file's verifier hands its chains. -/
theorem early_xinBA (a : X × L.Rec) :
    (xinBA r₀ a).map (typedOracleCarrier L Bd aT aL).early = some (some (L.early a.1), r₀, r₀) := rfl

/-- The two strings that the page takes out of the first query's instance. -/
theorem req_xinBA (reqX : X → ByteArray × ByteArray) (a : X × L.Rec) :
    (((xinBA r₀ a).map (typedOracleCarrier L Bd aT aL).early).map (reqOf reqX)).getD default =
      reqX (L.early a.1) := rfl

/-- The premise on the two strings, from an equation on the instance's early part. -/
theorem hreq_of (reqX : X → ByteArray × ByteArray) (a : X × L.Rec) (request words : ByteArray)
    (h : reqX (L.early a.1) = (request, words)) :
    (((xinBA r₀ a).map (typedOracleCarrier L Bd aT aL).early).map (reqOf reqX)).getD default =
      (request, words) := (req_xinBA Bd aT aL r₀ reqX a).trans h

end OnBytes.Maker.Page
