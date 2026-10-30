-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/WholeKey/AtInput.lean: the scheme with the whole key published (argW,
Johnson/WholeKey/Defs.lean) AT AN INPUT of Johnson/Top/InnerCompiledVerifier.lean, over the typed oracles and
over one hash function; and WHERE THE 256-BIT COMMITMENT ID SITS: beside the whole key.

General definitions, three equations that hold by unfolding, and one statement that is typed here
and proved in Johnson/WholeKey/AtInputProof.lean (Spec.privacy_withId). This file states no goal of
the release.

Why. The library's scheme at an input r (schemeOverTypedOracles r) has the key (root, out-of-domain sample), and
what is made once rides in every proof. The scheme here has the same verifier behind a re-packing,
and an honest side whose letters (HonestSide) stand beside r, as SoundnessAnalysisData r does: the verifier
reads none of them.

The commitment ID is the hash function's answer at a code (r.keyCode) of (root, out-of-domain sample).
Over the typed oracles there is no oracle for it. Over one hash function the committer asks one
query more and publishes the answer IN FRONT OF the whole key (withId); the verifier asks the same
query and compares. So the published key is: the ID; the first table's root, out-of-domain sample
and proof; each copy's root, out-of-domain sample and link proof.
That step is a re-packing in the sense of ZKCP/PrivacyWrap.lean (wrapId), whose theorem
PrivacyFor.wrap carries strong index privacy at the price of one query more. The way down to a
scheme whose key is the ID alone, with all else in each proof, is a re-packing too (wrapFront): its
map on proofs reads the key.

Main names (namespace OnBytes.WholeKey).
  wholeKeySchemeOverTypedOracles r h   the scheme at r over the typed oracles.
  wholeKeySchemeOverTypedOracles_V     its verifier IS schemeOverTypedOracles r's, at the re-packed key and proof: by unfolding.
  InnerCompilerInput.withSide   an input with the type of the prover's key, the committer and the prover laid
    anew (full name VerifiableInference.OnPublicFiles.InnerCompilerInput.withSide).
  innerCompilerInputWithProverHoldingWholeKey r h, schemeOverTypedOracles_innerCompilerInputWithProverHoldingWholeKey   r with three of its five fields for an honest side (ProverKey, commit,
    prove) filled from h at the compiled verifier's own types; schemeOverTypedOracles there is argLow: by
    unfolding. The other two (coinBound, fallbackProof) stay r's.
  wholeOne r h   over one hash function, one request a call, in the form of ZKCP/Defs.lean.
  withId, wrapId   for every scheme and code: the digest of the key's code in front of the key.
  wholeId r h    THE SCHEME WHOSE PUBLISHED KEY BEGINS WITH THE COMMITMENT ID.
  wrapFront r    from the whole key to the key that is the ID alone.
  Spec.privacy_withId   typed here (its proof: privacy_withId, Johnson/WholeKey/AtInputProof.lean):
    strong index privacy passes to withId.

Limits. Nothing on hiding, binding or completeness is proved here. wrapFront is a definition without
a theorem. withId's verifier refuses a key
without a code. r.keyCode is a letter. Whether r.coinBound bounds the queries of the honest side that innerCompilerInputWithProverHoldingWholeKey
lays is not said.
Terms: lean/GLOSSARY.md.

-/
import Johnson.WholeKey.Defs
import Johnson.Top.InnerCompiledVerifier
import ZKCP.PrivacyWrap
import ZKCP.DigestKey
import ZKCP.SpecialAny

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace OnBytes.WholeKey
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open OnBytes.Prover VerifiableInference.OnPublicFiles
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-! ## For every scheme over one hash function: the digest of the key's code in front of the key -/

section General
variable {lam : ℕ} {I X W PP IVK ISK Pf : Type}

/-- The scheme A with the hash function's answer at a code of its verifier's key laid in front of
that key. The committer asks one query more; the prover is A's; the verifier asks that query,
refuses unless the answer is the digest that the key begins with, and then runs A's verifier. -/
def withId (A : ZKCP.Arg lam I X W IVK ISK Pf) (code : IVK → Option ZKCP.Str) :
    ZKCP.Arg lam I X W (ZKCP.Digest lam × IVK) ISK Pf where
  C := fun i => (A.C i).bind fun keys =>
    (ZKCP.keyDigest code keys.1).mapO fun d => ((d, keys.1), keys.2)
  P := A.P
  V := fun k x π => ZKCP.verifyDigestKey A.V code k.1 x (k.2, π)

/-- The re-packing (ZKCP.Wrap, ZKCP/PrivacyWrap.lean) that lays the digest in front of the key and
leaves proofs, instances and witnesses as they are. -/
def wrapId (code : IVK → Option ZKCP.Str) :
    ZKCP.Wrap lam IVK X W Pf (ZKCP.Digest lam × IVK) X W Pf where
  ask := code
  key := fun k a => (a.getD fun _ => false, k)
  proof := fun _ π => π
  inst := id
  wit := id
  back := id

/-- The statement (its proof: privacy_withId, Johnson/WholeKey/AtInputProof.lean). Strong index
privacy passes from A to withId A code, for every code, with the simulator that also answers the
query at the code of the key that it has made, at A's bound at one query more. -/
def Spec.privacy_withId : Prop :=
  ∀ (lam : ℕ) (I X W PP IVK ISK Pf : Type) (R : ZKCP.IndexedRelation I X W PP)
    (A : ZKCP.Arg lam I X W IVK ISK Pf) (Sm : ZKCP.Simulator lam PP IVK X Pf) (ζ : ℕ → ℕ → ℝ≥0∞)
    (code : IVK → Option ZKCP.Str),
    ZKCP.HasStrongIndexPrivacyWith R A Sm ζ →
      ZKCP.HasStrongIndexPrivacyWith R (withId A code) ((wrapId (W := W) code).sim Sm id)
        fun t N => ζ (t + 1) N

end General

/-! ## At an input -/

variable (r : InnerCompilerInput) (h : HonestSide 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)

/-- **The scheme with the whole key published, at the input r**, over the typed oracles. -/
def wholeKeySchemeOverTypedOracles : ZKCP.Gen.Arg (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) r.Index r.Instance Unit
    (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) (Isk 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (RequestProof 256 r.protocol) :=
  argW r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters h

/-- **Its verifier is the verifier of schemeOverTypedOracles r at the re-packed key and proof.** -/
theorem wholeKeySchemeOverTypedOracles_V (k : FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) (x : r.Instance) (π : RequestProof 256 r.protocol) :
    (wholeKeySchemeOverTypedOracles r h).V k x π = (schemeOverTypedOracles r).V (lowKey k) x (lowPrf k π) := rfl

/-- An input with three of its fields for an honest side laid anew: the type of the prover's key,
the committer, the prover. All else stays, the fields coinBound and fallbackProof too. What innerCompiledVerifier reads does
not change. -/
def _root_.VerifiableInference.OnPublicFiles.InnerCompilerInput.withSide (r : InnerCompilerInput) (ISK : Type)
    (commit : r.Index →
      Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)) (KeyRoot 256 r.protocol × ISK))
    (prove : ISK → (b : List (r.Instance × Unit)) →
      Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
        (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) b)) : InnerCompilerInput :=
  { r with ProverKey := ISK, commit := commit, prove := prove }

/-- The input r with these three fields filled from h, at the compiled verifier's own types: the key
is (root, out-of-domain sample); the prover's key holds the whole key, and the prover copies what
was made once into each proof. -/
def innerCompilerInputWithProverHoldingWholeKey : InnerCompilerInput :=
  r.withSide (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits × Isk 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (argLow r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters h).C (argLow r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters h).P

/-- The library's scheme at that input is argLow. -/
theorem schemeOverTypedOracles_innerCompilerInputWithProverHoldingWholeKey : schemeOverTypedOracles (innerCompilerInputWithProverHoldingWholeKey r h) = argLow r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters h := rfl

/-- Over one hash function, one request a call: a scheme of ZKCP/Defs.lean. -/
def wholeOne : ZKCP.Arg 256 r.Index r.Instance Unit (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) (Isk 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)
    (RequestProof 256 r.protocol) :=
  ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (wholeKeySchemeOverTypedOracles r h))

/-- **The scheme whose published key begins with the commitment ID**: the hash function's answer at
the input's code of (root, out-of-domain sample); then the whole key. -/
def wholeId : ZKCP.Arg 256 r.Index r.Instance Unit (ZKCP.Digest 256 × FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)
    (Isk 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits) (RequestProof 256 r.protocol) :=
  withId (wholeOne r h) fun k => r.keyCode (lowKey k)

/-- The re-packing from the whole key to a key that is the commitment ID alone: (root, out-of-domain
sample) and what was made once ride in each proof. Its map on proofs reads the key. -/
def wrapFront : ZKCP.Wrap 256 (FullKey 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) r.Instance Unit (RequestProof 256 r.protocol) (ZKCP.Digest 256)
    r.Instance Unit (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) where
  ask := fun k => r.keyCode (lowKey k)
  key := fun _ a => a.getD fun _ => false
  proof := fun k π => (lowKey k, lowPrf k π)
  inst := id
  wit := id
  back := id

end OnBytes.WholeKey
