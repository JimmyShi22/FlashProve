--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Prover/All/AtScheme.lean: COMPLETENESS IN THE DEFINITION's OWN FORM, FROM NAMED PREMISES,
ONCE, FOR ANY OBJECT WITH RECORDS: of the scheme schemeOverTypedOracles r (Johnson/Top/InnerCompiledVerifier.lean) at an
input whose three honest fields are the library's committer and the prover of a whole request
(Johnson/Prover/All/Defs.lean): over the typed oracles (ZKCP.Gen.HasCompletenessError,
ZKCP/Gen.lean); and over one hash function (ZKCP.HasCompletenessError, ZKCP/Defs.lean),
by the library's exit and by the exit that asks a Fiat-Shamir answer's first block first
(Rom/OverOneF.lean).

All three are calls: gen_complete (Johnson/Prover/All/End.lean); completeness_overOne
(Rom/ExitBind.lean) or completeness_overOneF; SpecialAny.completeness_of_gen (ZKCP/SpecialAny.lean).

Main names (namespace VerifiableInference.OnPublicFiles).
  InnerCompilerInput.withHonest   an input with its fields ProverKey, commit, prove laid anew. No verifier reads
    them.
  schemeOverTypedOracles_withHonest   the scheme there is argA: by unfolding.
  complete_schemeOverTypedOracles   over the typed oracles, for batches of at most one request.
  complete_oneHash     over one hash function: every block of every answer is asked.
  factors_proveA, complete_oneHashF   the prover factors; the same by the first-block exit.

Limits. As gen_complete's: the accept laws and the bounds on the sets' measures are premises; typed
proofs, fixed wires, a fixed coding, no public reading; a fresh copy for each request. The key is
the typed key (root, record): no commitment by a digest, no tokens (these:
Johnson/Prover/All/Front.lean). It states no goal. THE PROVER's KEY HERE IS (index, encoding
randomness, salts), and the prover draws all else anew at every proof. A scheme with a wider key
(the committer makes the key file's proof and the copies with their links once and hands them over)
is being typed elsewhere: these statements are of the present key alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.End
import Johnson.Prover.All.CountF
import Johnson.Top.InnerCompiledVerifier
import Rom.ExitBind
import Rom.OverOneF
import ZKCP.SpecialAny

set_option autoImplicit false

noncomputable section

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open OnBytes.Prover
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open scoped ENNReal

variable (r : InnerCompilerInput) {Kap : Type} (b₀ : r.LeafBody) (st : Strats r.protocol Kap) (capT capL capB : ℕ → ℕ)
  (ri : Enum r.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (dr : Enum (Draw 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits Kap))
  (π₀ : OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits)

/-- An input with its honest fields laid anew: the library's committer; the prover of a whole
request. -/
def InnerCompilerInput.withHonest : InnerCompilerInput :=
  { r with
    ProverKey := r.Index × r.protocol.EncodingRandomness × (ℕ → Bits)
    commit := committerOverTypedOracles r.queryLayout r.seedQueries ri sl b₀
    prove := proveA r.queryLayout r.seedQueries r.answerCode r.fixedSample b₀ st capT capL capB dr π₀ }

/-- The scheme there. -/
theorem schemeOverTypedOracles_withHonest :
    schemeOverTypedOracles (r.withHonest b₀ st capT capL capB ri sl dr π₀) =
      argA r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters b₀ st capT capL capB ri sl dr π₀ := rfl

variable (Yes : r.Index → r.Instance → Prop)
  (Bs : r.Index → r.protocol.EncodingRandomness → r.Instance → Draw 256 r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits Kap → Bads r.protocol)
  {ζ₁ ζ₂ δT δL δB : ℝ≥0∞}

/-- **Over the typed oracles.** -/
theorem complete_schemeOverTypedOracles (hL : LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hsl : ∀ a j, j < r.protocol.wordLength → (sl.e a j).length = r.compilerParameters.sMT) (hdr : ∀ a, DrawFit r.queryLayout r.compilerParameters (dr.e a))
    (acc : AccLaws r.queryLayout r.seedQueries st Yes Bs ζ₁ ζ₂ δT δL δB) :
    ZKCP.Gen.HasCompletenessError (ZKCP.Special.toPair (ZKCP.languageRelation Yes))
      (schemeOverTypedOracles (r.withHonest b₀ st capT capL capB ri sl dr π₀)) 1
      (alphaAll r.queryLayout capT capL capB ζ₁ ζ₂ δT δL δB) :=
  gen_complete r.queryLayout r.seedQueries r.answerCode r.fixedSample r.compilerParameters b₀ st capT capL capB ri sl dr π₀ Yes Bs hL hW hsl hdr acc

/-- **Over one hash function, in the definition's own form**: the library's exit. -/
theorem complete_oneHash (hL : LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hsl : ∀ a j, j < r.protocol.wordLength → (sl.e a j).length = r.compilerParameters.sMT) (hdr : ∀ a, DrawFit r.queryLayout r.compilerParameters (dr.e a))
    (acc : AccLaws r.queryLayout r.seedQueries st Yes Bs ζ₁ ζ₂ δT δL δB) :
    ZKCP.HasCompletenessError (ZKCP.languageRelation Yes)
      (ZKCP.SpecialAny.oneOf
        (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles (r.withHonest b₀ st capT capL capB ri sl dr π₀))))
      (alphaAll r.queryLayout capT capL capB ζ₁ ζ₂ δT δL δB) :=
  ZKCP.SpecialAny.completeness_of_gen (ZKCP.languageRelation Yes) (ZKCP.SpecialAny.agrees_oneOf _) _
    (completeness_overOne r.oracleCoding _ _ 1 _
      (complete_schemeOverTypedOracles r b₀ st capT capL capB ri sl dr π₀ Yes Bs hL hW hsl hdr acc))

/-- The prover with its coins factors, as the runs behind the coins do. -/
theorem factors_proveA {hK : 0 < r.queryLayout.K} {pass : Pass 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)}
    (H : PassFits r.queryLayout r.seedQueries hK pass) (isk : r.Index × r.protocol.EncodingRandomness × (ℕ → Bits)) :
    ∀ b : List (r.Instance × Unit),
      (proveA r.queryLayout r.seedQueries r.answerCode r.fixedSample b₀ st capT capL capB dr π₀ isk b).FactorsBy (agP hK pass)
  | [] => trivial
  | [(x, _)] => fun a =>
    OComp.FactorsBy.bind (factors_allX r.answerCode r.fixedSample b₀ st capT capL capB H isk x (dr.e a))
      fun _ => trivial
  | _ :: _ :: _ => trivial

/-- **The same by the first-block exit.** -/
theorem complete_oneHashF {hK : 0 < r.queryLayout.K} {pass : Pass 256 (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits)}
    (F : FirstIs hK r.oracleCoding) (H : PassFits r.queryLayout r.seedQueries hK pass)
    (hL : LawFit r.queryLayout r.seedQueries capT capL capB) (hW : WiresFit r.queryLayout r.answerCode)
    (hsl : ∀ a j, j < r.protocol.wordLength → (sl.e a j).length = r.compilerParameters.sMT) (hdr : ∀ a, DrawFit r.queryLayout r.compilerParameters (dr.e a))
    (acc : AccLaws r.queryLayout r.seedQueries st Yes Bs ζ₁ ζ₂ δT δL δB) :
    ZKCP.HasCompletenessError (ZKCP.languageRelation Yes)
      (ZKCP.SpecialAny.oneOf (overOneArgF r.oracleCoding (moreP pass)
        (schemeOverTypedOracles (r.withHonest b₀ st capT capL capB ri sl dr π₀))))
      (alphaAll r.queryLayout capT capL capB ζ₁ ζ₂ δT δL δB) :=
  ZKCP.SpecialAny.completeness_of_gen (ZKCP.languageRelation Yes) (ZKCP.SpecialAny.agrees_oneOf _) _
    (completeness_overOneF r.oracleCoding (moreP pass) _ _ 1 _
      (fun k b => factorsF_of hK pass r.oracleCoding F
        (factors_proveA r b₀ st capT capL capB dr π₀ H k b))
      (complete_schemeOverTypedOracles r b₀ st capT capL capB ri sl dr π₀ Yes Bs hL hW hsl hdr acc))

end VerifiableInference.OnPublicFiles
