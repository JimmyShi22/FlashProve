-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InnerCompiledVerifierParts.lean: `innerCompiledVerifier r` (Johnson/Top/InnerCompiledVerifier.lean), the verifier of which
that file states soundness under its named hypotheses, taken apart: one general law at every input
r.

Main names.
  `OnBytes.K.frontV_is_innerCompiledVerifier`: the front's verifier in the library's own terms (`frontV`,
    Johnson/Top/FrontGeneral.lean) at r's scheme over one hash function, r's code of a key, r's
    coinBound, r's way to build an instance and r's fixed proof is `innerCompiledVerifier r`: by unfolding.
    With `front_yes` and `front_yes_only` of that file it says when `innerCompiledVerifier r` says yes.

Limits. r is a letter: no input is given. An equation of two terms: nothing on whether either says
yes, and nothing on soundness. This file names neither the Lean program `verify-on-bytes` nor a tie
to it. For proofs only; no program imports this file.


-/
import Johnson.Top.InnerCompiledVerifier
import Johnson.Top.FrontGeneral

set_option autoImplicit false

noncomputable section

namespace OnBytes.K

open Rom
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open VerifiableInference (Token)
open VerifiableInference.OnPublicFiles

variable {r : InnerCompilerInput}

/-- `frontV` at r's terms is `innerCompiledVerifier r`. -/
theorem frontV_is_innerCompiledVerifier (c : ZKCP.Digest 256) (prompt output : List Token)
    (proof : List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)) :
    frontV (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) r.keyCode r.coinBound r.buildInstance r.fallbackProof c prompt output proof =
      innerCompiledVerifier r c prompt output proof := rfl

end OnBytes.K

#print axioms OnBytes.K.frontV_is_innerCompiledVerifier
