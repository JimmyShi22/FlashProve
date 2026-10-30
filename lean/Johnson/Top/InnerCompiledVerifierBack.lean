-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InnerCompiledVerifierBack.lean: `verifyV r.toInputV`, at every key and proof string of the
verifier's side, is `innerCompiledVerifier r` at their images under the maps back.

`innerCompiledVerifier_eq` (Johnson/Top/InnerCompiledVerifierSide.lean) starts from a proof of the argument system; this
file starts from a key and a proof string of the verifier's side. Every such pair is the image of
one of the argument system's (Johnson/TypedOracleCompiler/RecCompile/SideTies.lean), so the same equation holds from
that end.

Main names (namespace `VerifiableInference.OnPublicFiles`): `InnerCompilerInput.back`, `verifyV_toInputV`,
`verifyV_toInputV_system`.
Limits: two equations, no hypothesis. Nothing on soundness.

-/
import Johnson.Top.InnerCompiledVerifierSide
import Johnson.TypedOracleCompiler.RecCompile.SideTies

set_option autoImplicit false

namespace VerifiableInference.OnPublicFiles
open TypedOracleCompiler.Compile.Batch.Cms

/-- The way back for a whole proof: the further tokens as they are; the key and the proof string
field by field. -/
def InnerCompilerInput.back (r : InnerCompilerInput)
    (q : List Token × (KeyRootV 256 r.protocol.v × PrfRootV 256 r.protocol.v r.offlineRoundSplits r.linkRoundSplits)) :
    List Token × (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) :=
  (q.1, KeyRoot.ofV q.2.1, OfflineLinkOnlineProof.ofV q.2.2)

/-- **`verifyV` at `r.toInputV` is `innerCompiledVerifier r`**: at every commitment, prompt, output, and every
proof of the verifier's side. -/
theorem verifyV_toInputV (r : InnerCompilerInput) (commitment : Commitment) (prompt output : List Token)
    (q : List Token × (KeyRootV 256 r.protocol.v × PrfRootV 256 r.protocol.v r.offlineRoundSplits r.linkRoundSplits)) :
    verifyV r.toInputV commitment prompt output q =
      innerCompiledVerifier r commitment prompt output (r.back q) :=
  (innerCompiledVerifier_eq r commitment prompt output (r.back q)).symm

/-- So it is the verifier of which soundness is stated. -/
theorem verifyV_toInputV_system (r : InnerCompilerInput) (commitment : Commitment)
    (prompt output : List Token)
    (q : List Token × (KeyRootV 256 r.protocol.v × PrfRootV 256 r.protocol.v r.offlineRoundSplits r.linkRoundSplits)) :
    verifyV r.toInputV commitment prompt output q =
      (innerSystem r).verify commitment prompt output (r.back q) :=
  verifyV_toInputV r commitment prompt output q

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.verifyV_toInputV
#print axioms VerifiableInference.OnPublicFiles.verifyV_toInputV_system
