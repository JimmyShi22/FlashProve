-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/BindsAtInnerSystem.lean: OPENING-FORM BINDING AT "AN HONEST COMMITTER, THEN `innerCompiledVerifier`", IN TWO
STEPS, WHICH NO STATEMENT HERE JOINS (Johnson/Top/BindsTwoAt.lean does). (1) At an input of
Johnson/Top/InnerCompiledVerifier.lean whose committer is `committerOverTypedOracles` (Johnson/TypedOracleCompiler/RecCompile/CommitOverTypedOracles.lean),
under the wire's laws and hdec: `openingByCommitterMatchesExtractor`, with the bound written out. (2) At any input, from
`openingByCommitterMatchesExtractor r β` and hinj, hcode, hS, hβ: the commitment binds in the opening form, but for ε',
to the index that the library's extractor gives; nobody opens it to two indices, but for 2 ε'; and,
under the sixteen named hypotheses and hext besides, soundness and opening-form binding hold for
that one extractor. AT LETTERS: shown here of no input. THE COMMITTER IS TIED TO NO PROGRAM.

Main names (namespace `VerifiableInference.OnPublicFiles`). `InnerCompilerInput.withCommitterOverTypedOracles`: an input with that
committer laid in; `innerCompiledVerifier_withCommitterOverTypedOracles`: the verifier is the same program. `keyCodeIndexExtractorOnTokens r`: the
library's extractor behind the hash of the key's code: a written term (it inverts the code by
choice: `keyOfCode`, ZKCP/DigestKey.lean). `two_bindsWith_of_opens`, `two_noTwoOpenings_of_opens`,
`two_soundAndBinding_of_opens`: from `openingByCommitterMatchesExtractor r β` and the premises named above. `compiledIndexExtractor_eq`.
`openingByCommitterMatchesExtractor_withCommitterOverTypedOracles`: `openingByCommitterMatchesExtractor` at such an input, with the bound written out.

How: the two general layers of Johnson/Top/FrontBinds.lean (`Rec.opens_digestSchemeE`,
`Rec.bindsWith_systemE`), `innerCompiledVerifier_sound`, `opens_committerOverTypedOracles`. The three ends are the likes, at
this scheme, of `front_bindsWith_of_opens`, `front_noTwoOpenings_of_opens`,
`front_soundAndBinding_of_opens` there.

WHO READS EACH LETTER (V: `innerCompiledVerifier`; C: the committer `committerOverTypedOracles`; B: a bound in a conclusion; R:
the claim; -: nobody in these statements).
- ri, sl, b₀ (the coins' two enumerations; the filling beyond the word): C alone. Under "for all".
- prove: -. Under "for all". ProverKey, commit, prove are not read by V: `innerCompiledVerifier_withCommitterOverTypedOracles`, by
  rfl.
- r.protocol (the object): V (its three protocols); C (`wordLength`, `encodeIndex`, `honestOutOfDomainAnswer` through `recOf`, `EncodingRandomness`); the
  extractor `keyCodeIndexExtractorOnTokens r` (`decodeIndex`); hdec ties `encodeIndex`, `recOf` and `decodeIndex`. r.offlineRoundSplits, r.linkRoundSplits (the marks): V. r.Index,
  r.Instance, r.LeafBody: types.
- r.queryLayout (the wire): V; C (`embE`, `depth`, `K`); the extractor `keyCodeIndexExtractorOnTokens r` (`depth`, `prjE`,
  `B.ext.build`: `extEnc`, OnBytes/TypedOracleCompiler/Compile/Batch/Events.lean); B (`depth`, `K`, in `committerQueryCount`; `tVC
  r.queryLayout`, in `compiledSoundnessError`).
- r.seedQueries (the wire of the record): V; C (`t`, `cfg`, `shape`, `pl0`, `pl1`, `seed`; NOT `num`, `code`,
  `decS`). Not B in value: `committerQueryCount_eq`. `code`: nobody in these statements.
- r.answerCode, r.fixedSample, r.compilerParameters: V (`schemeOverTypedOracles`'s third part). Not C.
- r.oracleCoding (the coding): V; C; the extractor `keyCodeIndexExtractorOnTokens r`. Not B in value: `committerQueryCount_eq`.
- r.keyCode (the key's code): V; the system's committer, behind C; `keyCodeIndexExtractorOnTokens r`.
- r.buildInstance: V; the system's prover (`Arg.buildInstance`, ZKCP/BuildInstance.lean); `CompilerSoundnessConditionStatements.sound`.
  r.nextToken: R alone (the docstrings of `InnerCompilerInput`).
- r.coinBound: the system's committer and prover, for the coins (`Arg.coinsFirst`,
  ZKCP/CoinsFirstArg.lean; `ArgumentSystem.ofArgument`, VerifiableInference/OfArgument.lean); the
  games of `BindsWith` and `NoTwoOpenings`: an opener names a number up to it. Not V.
- r.fallbackProof: the system's prover, where no instance is built (`Arg.buildInstance`). Not V.
- b (`SoundnessAnalysisData`): not V (its docstring); `εs`, `εId`: B; the sixteen; `Rno`, `Wn`: the sixteen;
  `x₀`: no statement (the proof of `innerCompiledVerifier_soundFor` spends it: r.Instance is not empty); `ext`: tied
  to `keyCodeIndexExtractorOnTokens r` by hext.
- β, tS, ε': B; tied by ho, hS, hβ, from below alone.
All fields of r and b are written wherever r and b are written. IN THE STATEMENTS OF THIS FILE NO
LETTER THAT V READS STANDS UNDER "THERE IS". `SoundAndBinding` (VerifiableInference/Statements.lean)
begins with one, of an extractor: an object of the analysis; the two clauses beside it name it.

Limits.
- STATEMENTS AT LETTERS: that hinj, hcode, hS, hβ, hext, hdec, the wire's laws and the
  sixteen hold together at an input is not shown here.
- β, tS, ε', b.εs, b.εId ARE LETTERS: ho, hS and hβ tie the first three, the sixteen the last two,
  all from below alone, and nothing asks that an error is below 1. At an error of 1 or more the ends
  say nothing.
- hdec can hold only at a type of indices all of whose members the decoder gives. It is, to the
  letter, the field `dec_enc` of `HolographicProtocol.WiredR` (Hiop/RecInterface.lean). Beside `noneColl`, one of
  the sixteen, it forces that no honest word has a collision at any seed.
- Where `two_bindsWith_of_opens` is fed by `openingByCommitterMatchesExtractor_withCommitterOverTypedOracles` at tS := `committerQueryCount` (so in
  Johnson/Top/BindsTwoAt.lean), THE COMMITTER'S COUNT ENTERS THE BOUND TWICE: `epsOpens β tS` adds
  tS to the opener's queries, and that β holds `committerQueryCount` already. A looser bound, not a wrong one.
- THE VERIFIER IS IDLE IN EVERY END ON BINDING ALONE. Nothing says that `innerCompiledVerifier` accepts anything
  under a commitment of `committerOverTypedOracles`. Nothing on completeness. AT AN r WHOSE VERIFIER SAYS NO TO
  EVERYTHING (so where `r.seedQueries.num` is false throughout: a letter under no law, which C does not read)
  the clause on soundness of `two_soundAndBinding_of_opens` is true for nothing; the ends on binding
  say there what they say elsewhere.
- Opening-form binding is to the index. Nothing on two openings with one index and other randomness.
  One opening in a run of `BindsWith`; two in `NoTwoOpenings`. The committer's runs again are not
  among the adversary's queries: the bound has to cover them.
- What the commitment covers is the key (root, record) through the key's code. Whether it covers a
  public file is not treated here.
- Under hext and hinj one of the sixteen, `CompilerSoundnessConditionStatements.commitment`, is paid at b.εId t = (t + 2)² /
  2^256 by `Rec.commitmentBinds_of_code` (Johnson/Top/FrontCommit.lean); not spent here.
- One coding, fixed before the hash function is drawn (the limits of
  Johnson/TypedOracleCompiler/RecCompile/OpensCommitOverTypedOracles.lean).
- Not claimed: anything on hiding. No program's committer or commitment is spoken of.

Terms: lean/GLOSSARY.md.

-/
import Johnson.TypedOracleCompiler.RecCompile.OpensCommitOverTypedOracles
import Johnson.Top.FrontBinds

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

/-- The input r with the honest committer `committerOverTypedOracles` at r's own wire and wire of the record, and a
prover for that committer's key. The other fields are r's. -/
def InnerCompilerInput.withCommitterOverTypedOracles (r : InnerCompilerInput) (ri : Enum r.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : r.LeafBody)
    (prove : r.Index × r.protocol.EncodingRandomness × (ℕ → Bits) → (b : List (r.Instance × Unit)) →
      Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
        (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) b)) : InnerCompilerInput :=
  { r with
    ProverKey := r.Index × r.protocol.EncodingRandomness × (ℕ → Bits)
    commit := committerOverTypedOracles r.queryLayout r.seedQueries ri sl b₀
    prove := prove }

/-- `innerCompiledVerifier` is the same program at both inputs. -/
theorem innerCompiledVerifier_withCommitterOverTypedOracles (r : InnerCompilerInput) (ri : Enum r.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : r.LeafBody)
    (prove : r.Index × r.protocol.EncodingRandomness × (ℕ → Bits) → (b : List (r.Instance × Unit)) →
      Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
        (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) b)) :
    innerCompiledVerifier (r.withCommitterOverTypedOracles ri sl b₀ prove) = innerCompiledVerifier r := rfl

/-- The library's extractor behind the hash of the key's code, on tokens. -/
abbrev keyCodeIndexExtractorOnTokens (r : InnerCompilerInput) : Commitment → QueryLog → Option r.Index :=
  (Rec.tokenExtractorE (X := r.Instance) (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout)) r.keyCode).Ei

variable {r : InnerCompilerInput} {ε' : ℕ → ℝ≥0∞} {β : ℕ → ℕ → ℝ≥0∞} {tS : ℕ}

/-- **Where whoever opens a key opens it to what the extractor gives (`openingByCommitterMatchesExtractor`), the commitment of
`innerSystem r` binds in the opening form, but for ε', to the index that the library's extractor
gives.** hinj: no two keys have one code; hcode: every key that the committer can put out has a
code; hS: the committer asks at most tS queries to the hash function; hβ: ε' bounds
`epsOpens β tS` (Johnson/Top/FrontBinds.lean). -/
theorem two_bindsWith_of_opens (hinj : ZKCP.CodeIsOneToOne r.keyCode)
    (hcode : (ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).KeysHaveCodes r.keyCode)
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).C i).QueryBound tS)
    (ho : openingByCommitterMatchesExtractor r β) (hβ : ∀ tC tO, epsOpens β tS tC tO ≤ ε' (tC + tO)) :
    BindsWith (innerSystem r) (keyCodeIndexExtractorOnTokens r) ε' :=
  Rec.bindsWith_systemE (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout)) r.keyCode r.coinBound
    r.buildInstance r.fallbackProof r.nextToken
    (Rec.opens_digestSchemeE (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r)) (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout)) r.keyCode
      hinj hcode hS ho) hβ

/-- Under the same premises nobody opens one commitment to two different indices, but for 2 ε'. -/
theorem two_noTwoOpenings_of_opens (hinj : ZKCP.CodeIsOneToOne r.keyCode)
    (hcode : (ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).KeysHaveCodes r.keyCode)
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).C i).QueryBound tS)
    (ho : openingByCommitterMatchesExtractor r β) (hβ : ∀ tC tO, epsOpens β tS tC tO ≤ ε' (tC + tO)) :
    NoTwoOpenings (innerSystem r) fun t => 2 * ε' t :=
  (two_bindsWith_of_opens hinj hcode hS ho hβ).noTwoOpenings

/-- Where b's extractor is the library's behind the key's code, the named extractor of
`innerCompiledVerifier_sound` is `keyCodeIndexExtractorOnTokens r`. -/
theorem compiledIndexExtractor_eq (b : SoundnessAnalysisData r)
    (hext : b.ext = (ZKCP.Special.extOf (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout))).digestKey r.keyCode) :
    compiledIndexExtractor b = keyCodeIndexExtractorOnTokens r := by
  unfold compiledIndexExtractor
  rw [hext]
  rfl

/-- **Soundness and opening-form binding for one extractor, which is named**: under the sixteen
hypotheses of Johnson/Top/InnerCompiledVerifier.lean, hext (b's extractor is the library's behind the key's
code) and the premises of `two_bindsWith_of_opens`. The library's `SoundAndBinding` begins
"there is an extractor"; the two clauses before it say which. -/
theorem two_soundAndBinding_of_opens (b : SoundnessAnalysisData r) (h : CompilerSoundnessConditionsWithMeaning b)
    (hext : b.ext = (ZKCP.Special.extOf (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout))).digestKey r.keyCode)
    (hinj : ZKCP.CodeIsOneToOne r.keyCode)
    (hcode : (ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).KeysHaveCodes r.keyCode)
    (hS : ∀ i, ((ZKCP.SpecialAny.oneOf (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))).C i).QueryBound tS)
    (ho : openingByCommitterMatchesExtractor r β) (hβ : ∀ tC tO, epsOpens β tS tC tO ≤ ε' (tC + tO)) :
    SoundForWith (innerSystem r) (keyCodeIndexExtractorOnTokens r) (innerSystem r).IsModelOutput (compiledSoundnessError b) ∧
      BindsWith (innerSystem r) (keyCodeIndexExtractorOnTokens r) ε' ∧
      SoundAndBinding (innerSystem r) fun t => max (compiledSoundnessError b t) (ε' t) := by
  have hs := innerCompiledVerifier_sound b h
  rw [compiledIndexExtractor_eq b hext] at hs
  have hb := two_bindsWith_of_opens hinj hcode hS ho hβ
  exact ⟨hs, hb, soundAndBinding_of_le (innerSystem r) _ _ _ _ hs hb (fun _ => le_max_left _ _)
    fun _ => le_max_right _ _⟩

/-- **`openingByCommitterMatchesExtractor` holds at every input with the committer `committerOverTypedOracles`**, under the wire's laws and
hdec. -/
theorem openingByCommitterMatchesExtractor_withCommitterOverTypedOracles (r : InnerCompilerInput) (hW : r.queryLayout.OKG)
    (hdec : ∀ i ρ s, r.protocol.decodeIndex (r.protocol.encodeIndex i ρ) (r.protocol.recOf i ρ s) = some i)
    (ri : Enum r.protocol.EncodingRandomness) (sl : Enum (ℕ → Bits)) (b₀ : r.LeafBody)
    (prove : r.Index × r.protocol.EncodingRandomness × (ℕ → Bits) → (b : List (r.Instance × Unit)) →
      Rom.OComp (typedOracleFamily 256 r.queryLayout.K (typedOracleCarrier r.protocol r.LeafBody r.offlineRoundSplits r.linkRoundSplits))
        (ZKCP.Gen.Slots (OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) b)) :
    openingByCommitterMatchesExtractor (r.withCommitterOverTypedOracles ri sl b₀ prove)
      fun tC tO => 2 * ((tC + (tO + committerQueryCount r.queryLayout r.seedQueries r.oracleCoding) + 1 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ 256 :=
  opens_committerOverTypedOracles r.queryLayout r.seedQueries (by norm_num) hW hdec r.oracleCoding ri sl b₀
    (schemeOverTypedOracles (r.withCommitterOverTypedOracles ri sl b₀ prove)) rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifier_withCommitterOverTypedOracles
#print axioms VerifiableInference.OnPublicFiles.two_bindsWith_of_opens
#print axioms VerifiableInference.OnPublicFiles.two_noTwoOpenings_of_opens
#print axioms VerifiableInference.OnPublicFiles.compiledIndexExtractor_eq
#print axioms VerifiableInference.OnPublicFiles.two_soundAndBinding_of_opens
#print axioms VerifiableInference.OnPublicFiles.openingByCommitterMatchesExtractor_withCommitterOverTypedOracles
