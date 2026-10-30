-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InputV.lean: what the verifier of Johnson/Top/InnerCompiledVerifier.lean reads, as a record of its
own over the verifier's side of the object (`LHV`, Hiop/RecSide.lean), and that verifier as a
function of that record.

Why. Compiled, a verifier that is a field of an argument system made from the whole input builds
the decoder, the honest provers, the model and the honest committer before it takes that field. So
at a concrete input all of it would need executable code. The verifier's own body reads thirteen
things; none of them is on the honest side or the decoder's.
Main names (namespace `VerifiableInference.OnPublicFiles`):
  `InputV`: X, the verifier's side L of the object, Bd, aT, aL, W, Sd, cA, r₀, p, m, enc, build: the
    names and the order that they have in `InnerCompilerInput`; their types over `LHV`.
  `verifyV v`: build the instance; ask the hash function at the key's code and compare the answer
    with the commitment; run the compiled verifier with a record over the one hash function.
`innerCompiledVerifier r` (Johnson/Top/InnerCompiledVerifier.lean) equals `verifyV r.toInputV`, at the key and the proof
string read at the verifier's side, at every argument: `innerCompiledVerifier_eq`
(Johnson/Top/InnerCompiledVerifierSide.lean).
X, Bd, p and build have the types that they have in `InnerCompilerInput`; the other nine are typed over `LHV`,
and at `protocol.v` their types unfold to `InnerCompilerInput`'s or, for L, Sd, m and enc, to those types' verifier's
sides. Thirteen equations by rfl (`InnerCompilerInput.toInputV_X` and the rest,
Johnson/Top/InnerCompiledVerifierSide.lean) keep the two texts one: they must not be dropped in a clean-up.
Limits: definitions alone. That a concrete input's verifier's side has executable code is not said.
Nothing on soundness.

-/
import Johnson.TypedOracleCompiler.RecCompile.FrontRootAnsSide
import Rom.FamilySide
import ZKCP.BuildInstanceSide
import Johnson.Top.FrontCommit
import Johnson.Top.BlocksOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- What the verifier's own body reads. -/
structure InputV where
  /-- Instances. -/
  X : Type
  /-- The verifier's side of the object with records. -/
  L : LHV X
  /-- What a query's body may hold beside. -/
  Bd : Type
  /-- The key file's marks. -/
  aT : RoundSplits L.test.shape
  /-- The entry file's marks. -/
  aL : RoundSplits L.link.shape
  /-- The wire of the object. -/
  W : QueryLayout 256 (carrierV L Bd aT aL)
  /-- The wire of the record. -/
  Sd : SeedV 256 W.K L Bd aT aL
  /-- How a record's answers are written as a list of digests. -/
  cA : L.Ans → List (Dig 256)
  /-- A fixed record. -/
  r₀ : L.Rec
  p : Params
  /-- The typed oracles in one hash function: the writing side alone. -/
  m : ImplV (typedOracleFamily 256 W.K (carrierV L Bd aT aL)) 256
  /-- The code of a key. -/
  enc : KeyRootV 256 L → Option ZKCP.Str
  /-- From a prompt with output tokens, and further tokens that the proof brings, an instance. -/
  build : List Token × List Token → List Token → Option X

/-- The verifier, written out. -/
def verifyV (v : InputV) : Commitment → List Token → List Token →
    List Token × (KeyRootV 256 v.L × PrfRootV 256 v.L v.aT v.aL) → DeterministicAlgorithm Bool :=
  fun commitment prompt output proof =>
    deterministicOf (ZKCP.verifyBuilt (ZKCP.verifyDigestKey
      (fun k x π => Rom.ofRom ((VRAV v.W v.Sd v.cA v.r₀ v.p k x π).overOneV v.m)) v.enc) v.build
      commitment (prompt, output) proof)

end VerifiableInference.OnPublicFiles
