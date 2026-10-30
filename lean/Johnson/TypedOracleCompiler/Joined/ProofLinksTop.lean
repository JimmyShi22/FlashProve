-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/TypedOracleCompiler/Joined/ProofLinksTop.lean: the hypothesis "the proof file's protocol is sound" of the
top over the compiled verifier that hashes a file as three chains (`CompilerSoundnessConditionStatements.proofSound`,
Johnson/Top/InnerCompiledVerifier.lean), from the list of hypotheses in which each chain is a link with keys
for the statements of a batch.

Statements on the verifier with records, over the second form of the compiler's verifier side, for a
key file's and a proof file's three hash chains, joined by seals. That this verifier writes what is
hashed as the prover's files have it is not shown in this folder.


One statement. Its proof is one call of `proofSound_at_links` (OnBytes/TypedOracleCompiler/Joined/MidLinks.lean) at
the object of the three files' protocols (Johnson/Flat/InnerInputOfThreeProtocols.lean).

Main names:
  `proofSound_top_links`: `CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U)`.

What is asked, by name: hBJ: the object's batch protocol is the description's. hl: no later query
takes in more of the instance. knows: `Links.KnowsJ`, record by record. decides: where the file's
verifier accepts, no chain rejects, at the early part of the instance. tieR: what the first chain's
relation says gives the object's relation. worst: every entry of the three chains' lists of errors,
over the number of values of its round, is at most the top's bound.

Limits: every premise is a premise: none is shown of any description of a file. Each chain's list of
errors is a letter and is taken as it is: `worst` has no factor for the number of slots. So what
must be counted once for each slot has to stand in the lists: `knows` asks the second chain's clause
for all slots together at its list.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Flat.InnerInputOfThreeProtocols
import OnBytes.TypedOracleCompiler.Joined.MidLinks

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Hiop OnBytes.Flat TypedOracleCompiler.Joined
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Compile.Joined (Chains Desc)

variable {C : ConfigurationWithOutOfDomainSample} (F : Files C) (P : F.Provers) (T : InnerCompilerInputFieldsOverThreeProtocols F P) (U : SoundnessAnalysisFieldsOverThreeProtocols F P)
  {G : Chains} (DJ : Desc G (C.X × (F.withProvers P).Rec) (oneExternalString (F.withProvers P).wordLength (F.withProvers P).Symbol))
  (hBJ : (F.withProvers P).onlineBatch = DJ.batch)
  {KJ : Links G ((C.X × (F.withProvers P).Rec) × (oneExternalString (F.withProvers P).wordLength (F.withProvers P).Symbol).Str)} {κ₁ κ₂ : Type}
  {k₁ : KJ.A₁ → κ₁} {k₂ : KJ.A₂ → κ₂} (toWJ : KJ.W₀ → C.Cells)

include hBJ in
/-- **The proof file's hypothesis of the top, where each of the file's three chains is a link with
keys for the statements of a batch.** -/
theorem proofSound_top_links (hl : (F.withProvers P).late = none)
    (knows : ∀ rec, (KJ.comap fun x : C.X => (x, rec)).KnowsJ (F.withProvers P).maxBatchSize k₁ k₂)
    (decides : ∀ x rec y (τ : Tr G.sh), DJ.accept (x, rec) y τ = true →
      (KJ.all.out (((F.withProvers P).early x, rec), y) τ).isSome = true)
    (tieR : ∀ x rec y (τ : Tr G.sh), DJ.accept (x, rec) y τ = true →
      (KJ.on₀ (((F.withProvers P).early x, rec), y) →
        KJ.R₀ (((F.withProvers P).early x, rec), y) (KJ.ext (((F.withProvers P).early x, rec), y) τ ())) →
      (F.withProvers P).relB C.Rno rec x y (toWJ (KJ.ext (((F.withProvers P).early x, rec), y) τ ())))
    (worst : KJ.worstMid ≤ U.εs) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataOfThreeProtocols F P T U) :=
  proofSound_at_links (F.withProvers P) DJ C.Rno toWJ hBJ hl knows decides tieR worst

end VerifiableInference.OnPublicFiles
