-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/CommitCodeAtInnerCompilerInput.lean: the hypothesis `CompilerSoundnessConditionStatements.commitment` (Johnson/Top/InnerCompiledVerifier.lean)
holds, at the library's extractor and cost, if no two keys have the same code; so it holds at a code
laid out as the commitment ID's string with the record's seeds in it, if its two maps are one to
one.

Why it is here. `CompilerSoundnessConditionStatements.commitment b` is one of the named hypotheses of the soundness theorems over
an `InnerCompilerInput`. It speaks of `r.keyCode`, the function that writes a verifier's key (a root and its
record) as a bit string; the commitment is the hash of that string. The library proves the
hypothesis for a code that is one to one (`Rec.commitmentBinds_of_code`,
Johnson/Top/FrontCommit.lean) and uses that proof in place at toy inputs (Johnson/Top/Toy/CompilerSoundnessConditionsAtSmallExample.lean
is one). This file states it for every `InnerCompilerInput`.

Main results.
`CompilerSoundnessConditionStatements.commitment_of_code`: for every input r and every b, three hypotheses give
  `CompilerSoundnessConditionStatements.commitment b`: no bit string is the code of two keys (`hinj`); the extractor `b.ext` is
  the library's (`keyCodeIndexExtractor r`); the cost `b.εId` is the library's (`commitmentErrorOfKeyCode`: (t + 2)² / 2^256,
  where t counts the committer's and the prover's queries together).
`CompilerSoundnessConditionStatements.commitment_idSeed`: the same with `hinj` replaced by three hypotheses: `r.keyCode` is
  `idCodeSeed S cfg []` (Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean), a string laid out as the format's rule
  R4.11 lays out the commitment ID's, with the record's seeds in it; and the two maps of S that
  write a record's answers and its seed as lists of field elements are one to one.
`idCodeSeed_hasCode`: every key has a code under `idCodeSeed S cfg []`, if cfg has 32 bytes, the six
  numbers of `S.shape` are below 2^64, all seeds are encoded with n elements and all answers with m,
  and 176 + 24 n + 24 m is at most 2^32 - 144.
`idCodeSeed_none_of_size`: at a cfg whose size is not 32 bytes no key has a code.
`idCodeSeed_fmt_of`: whatever code a key has under `idCodeSeed S cfg []` is the bits of the string
  of the format's hash call number 179, which is the commitment ID's (R4.11), on
  `Fmt.publishedBytes` (Fmt/Rules4.lean) at cfg, the table's name, the seed's elements, the answers
  and the empty last list.
`idCodeSeed_rule`: every function g on bit strings sends that code to `Fmt.publishedIDW` at the hash
  made from g, at the same five arguments.
`idCodeSeed_seed_ne`: if the two maps of S are one to one, two keys that differ in the seed alone
  get different values of the code, if the first has a code.
`idCodeSeed_twoCodes`: if the two maps of S are one to one, every key has a code and there are two
  seeds, there are two keys with the same root and answers and different seeds whose codes differ.
  It follows from "every key has a code" and "one to one", and a code that is defined at one key
  alone meets its conclusion too. It is a sanity check against the string without the seeds, not a
  second test of emptiness.
`oneToOne_none`, `noCode_none`, `noTwoCodes_none`, `CompilerSoundnessConditionStatements.commitment_of_noCode`: the code that
  gives no key a code is one to one, and `CompilerSoundnessConditionStatements.commitment b` holds there too, at the library's
  extractor and cost; no key has a code under it, and no two keys get different values.

Limits.
`CompilerSoundnessConditionStatements.commitment` is an implication. Its premise, index binding of the scheme whose verifier
holds the key itself, is not shown here for any input. It follows from the other named hypotheses
(`CompilerSoundnessConditions.binds`, Johnson/Top/InnerCompiledVerifier.lean), of which some are unproved at the two sizes.
`CompilerSoundnessConditionStatements.commitment` is a hypothesis of `innerCompiledVerifier_soundFor` and `innerCompiledVerifier_sound`
(Johnson/Top/InnerCompiledVerifier.lean) and of the theorems derived from them (`innerCompiledVerifierSoundFromDryRunAtFullSize`,
`innerCompiledVerifierSoundFromDryRunAtSmallSize`, Johnson/Flat/TwoSizes.lean, among them). `front_sound`
(Johnson/Top/FrontParts.lean) does not take it: it is about another input, and takes another
proposition (`HoleArmsCD.commitmentOO`). Nothing in this file proves a hypothesis of it.
"No two keys have the same code" is true of a code that gives no key a code (`oneToOne_none`). The
verifier behind the hash rejects a key without a code, so at such a code the hypothesis says
nothing. `idCodeSeed_hasCode` is the test against that. It is necessary and not sufficient: where
the verifier that holds the key accepts nothing, premise and conclusion of the hypothesis hold for
free, though every key has a code. No value is shown here at which that verifier accepts.
The digest cfg is a constant in `idCodeSeed S cfg []`. In the programs it is the hash of the public
files. Under a random hash function the scheme with a constant cfg is the programs' scheme only for
those functions whose digest of the public files is cfg. These are a share of 2^-256 of all
functions (by reading), less than the term (t + 2)² / 2^256 alone: a bound at a constant cfg says by
itself nothing of a scheme that computes cfg with the same hash function. Here cfg is a constant all
the same. The format's specification says that a model of the format must not fix it before the hash
function is chosen (docs/format/FORMAT.md, section 18, "Some public inputs are answers of the
oracle", part of R4.9): in that respect an `InnerCompilerInput` with this code is not a model of the format. A
key that holds the digest (`encSeed`, Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean) is the library's
alternative; the key of an `InnerCompilerInput` has no place for it. Nothing here tests cfg against any file.
S is arbitrary. Nothing relates the numbers in `S.shape` to the lengths or the order of the lists
that `S.seed` and `S.answers` write. The string is rule R4.11's only at an S where they fit
(Johnson/Flat/CommitCodeSizes.lean).
Nothing here says that `r.keyCode` is the string that a program hashes, or that a key's seed is the hash
function's seed at the key's root.
No input r, no S and no b is defined here.
This file proves nothing about the soundness of any program. It is used in proofs only; the verifier
program does not import it.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.InnerCompiledVerifier
import Johnson.TypedOracleCompiler.Top.IdSeedBytes
import OnBytes.Tie.IdKeySeedFmt

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes size_digToBytes oB)
open OnBytes.Tie (idBytesS idOkS idStrS idCodeS idAtS_eq)
open TypedOracleCompiler.VerifiableInference.Rec (IdSpellS idCodeSeed idCodeSeed_oneToOne)

/-- The library's extractor for the scheme whose verifier holds the hash of a key's code: it looks
for the key in the committer's query log. -/
def keyCodeIndexExtractor (r : InnerCompilerInput) : ZKCP.Extractor 256 r.Index r.Instance Unit (ZKCP.Digest 256)
    (KeyRoot 256 r.protocol × OfflineLinkOnlineProof 256 r.protocol r.offlineRoundSplits r.linkRoundSplits) :=
  (ZKCP.Special.extOf (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout))).digestKey r.keyCode

/-- The library's cost of the step from the key to the hash of its code: (t + 2)² / 2^256, where t
counts the committer's and the prover's queries together. -/
def commitmentErrorOfKeyCode : ℕ → ℝ≥0∞ := fun t => (((t + 2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ 256

/-- **If no bit string is the code of two keys, `CompilerSoundnessConditionStatements.commitment b` holds**, at the library's
extractor and cost. For every input r and every b. -/
theorem CompilerSoundnessConditionStatements.commitment_of_code {r : InnerCompilerInput} (b : SoundnessAnalysisData r)
    (hinj : ZKCP.CodeIsOneToOne r.keyCode) (hext : b.ext = keyCodeIndexExtractor r) (hε : b.εId = commitmentErrorOfKeyCode) :
    CompilerSoundnessConditionStatements.commitment b := by
  have h := Rec.commitmentBinds_of_code (schemeOverOneHashFunction r.oracleCoding (schemeOverTypedOracles r))
    (extractorOverOneHashFunction r.oracleCoding (indexExtractorAtRootAndOutOfDomainSample r.queryLayout)) r.keyCode hinj (HasRelaxedRelationWitness b) (soundnessBoundOverTypedOracles r.queryLayout b.εs)
  unfold CompilerSoundnessConditionStatements.commitment
  rw [hext, hε]
  exact h

/-- **`CompilerSoundnessConditionStatements.commitment b` where the code of a key is laid out as the commitment ID's string with
the record's seeds in it.** S: the tables' shape, and how a record's answers and its seed are
encoded as lists of field elements; any S whose two maps are one to one. cfg: the configuration's
digest, a constant. The statement is that of `commitmentBinds_seed`
(Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean) at r's scheme; the proof calls `idCodeSeed_oneToOne`. -/
theorem CompilerSoundnessConditionStatements.commitment_idSeed {r : InnerCompilerInput} (b : SoundnessAnalysisData r) (S : IdSpellS r.protocol)
    (hA : Function.Injective S.answers) (hS : Function.Injective S.seed) (cfg : ByteArray)
    (henc : r.keyCode = idCodeSeed S cfg []) (hext : b.ext = keyCodeIndexExtractor r) (hε : b.εId = commitmentErrorOfKeyCode) :
    CompilerSoundnessConditionStatements.commitment b :=
  CompilerSoundnessConditionStatements.commitment_of_code b (by rw [henc]; exact idCodeSeed_oneToOne S hA hS cfg []) hext hε

section
variable {I X : Type} {L : HolographicProtocol I X}

/-- **Every key has a code** under `idCodeSeed S cfg []`, under the hypotheses on sizes. n, m:
the numbers of field elements with which every seed and every list of answers is encoded. The proof
is that of `idOkS_inputIdS` and `encId_hasCode` (Johnson/TypedOracleCompiler/Top/IdSeedHasCode.lean), at a general
S. -/
theorem idCodeSeed_hasCode (S : IdSpellS L) (cfg : ByteArray) (hc : cfg.size = 32) (n m : ℕ)
    (hn : ∀ s, (S.seed s).length = n) (hm : ∀ a, (S.answers a).length = m)
    (h1 : S.shape.code.logN < 2 ^ 64) (h2 : S.shape.code.ell < 2 ^ 64)
    (h3 : S.shape.code.r < 2 ^ 64) (h4 : S.shape.v < 2 ^ 64) (h5 : S.shape.answers < 2 ^ 64)
    (h6 : S.shape.saltBytes < 2 ^ 64) (h7 : 176 + 24 * n + 24 * m ≤ 2 ^ 32 - 144)
    (k : KeyRoot 256 L) : ∃ code, idCodeSeed S cfg [] k = some code := by
  have hs : (idBytesS (S.keyAt cfg [] k)).size ≤ 2 ^ 32 - 144 := by
    rw [OnBytes.K.Arm.size_idBytesS _ rfl]
    show cfg.size + (8 + ((digToBytes k.cm).size + cfg.size + 48)) +
      (8 + 24 * (S.seed k.rcd.1).length) + (8 + 24 * (S.answers k.rcd.2).length) + 8 ≤ _
    rw [hc, size_digToBytes, hn, hm]
    omega
  have ok : idOkS (S.keyAt cfg [] k) = true := by
    unfold idOkS
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, hc⟩, size_digToBytes k.cm⟩, hs⟩,
      fun _ hb => absurd hb List.not_mem_nil⟩
  refine ⟨_root_.Run.bytesToBits (idStrS (S.keyAt cfg [] k)), ?_⟩
  show idCodeS (S.keyAt cfg [] k) = _
  unfold idCodeS
  rw [if_pos ok]

/-- At a cfg whose size is not 32 bytes no key has a code. -/
theorem idCodeSeed_none_of_size (S : IdSpellS L) (cfg : ByteArray) (h : cfg.size ≠ 32)
    (k : KeyRoot 256 L) : idCodeSeed S cfg [] k = none := by
  show idCodeS (S.keyAt cfg [] k) = none
  unfold idCodeS
  rw [if_neg]
  intro ok
  unfold idOkS at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  exact h ok.1.1.1.2

/-- **Whatever code a key has is the bits of the string of the format's hash call number 179 on
`Fmt.publishedBytes`** (Fmt/Rules4.lean, the format's rule R4.11), at cfg, the table's name (made
from the key's root, cfg and `S.shape`), the elements of the key's seed, the key's answers, and the
empty last list. For every seed. (A key has a code only at a cfg of 32 bytes.) The proof is that of
`encId_fmt_of` (Johnson/TypedOracleCompiler/Top/IdSeedFmt.lean), at a general S and a constant cfg. No theorem of
this library calls it. -/
theorem idCodeSeed_fmt_of (S : IdSpellS L) (cfg : ByteArray) (k : KeyRoot 256 L) (code : ZKCP.Str)
    (h : idCodeSeed S cfg [] k = some code) :
    code = _root_.Run.bytesToBits (_root_.Fmt.oStr 0 179 0 0 _root_.Fmt.zero32
      (_root_.Fmt.publishedBytes cfg
        (OnBytes.Key.nameOf S.shape cfg ⟨digToBytes k.cm, S.answers k.rcd.2⟩)
        ((S.seed k.rcd.1).map OnBytes.E.triple)
        ((S.answers k.rcd.2).map OnBytes.E.triple) [])) := by
  have e : idCodeSeed S cfg [] k = idCodeS (S.keyAt cfg [] k) := rfl
  rw [e] at h
  unfold idCodeS at h
  split at h
  · have h' := (Option.some.inj h).symm
    unfold idStrS at h'
    rw [OnBytes.Tie.idBytesS_fmt] at h'
    exact h'
  · cases h

/-- **Every function g on bit strings sends a key's code to `Fmt.publishedIDW` at the hash made from
g**, at the same five arguments, as 256 bits. Both sides are g at one string. The proof is that of
`encId_rule` (Johnson/TypedOracleCompiler/Top/IdSeedFmt.lean), at a general S and a constant cfg. No theorem of this
library calls it. -/
theorem idCodeSeed_rule (S : IdSpellS L) (cfg : ByteArray) (g : ZKCP.Oracle 256)
    (k : KeyRoot 256 L) (code : ZKCP.Str) (h : idCodeSeed S cfg [] k = some code) :
    g code = bytesToDig (_root_.Fmt.publishedIDW (m := Id) (_root_.Fmt.HO (oB g)) cfg
      (OnBytes.Key.nameOf S.shape cfg ⟨digToBytes k.cm, S.answers k.rcd.2⟩)
      ((S.seed k.rcd.1).map OnBytes.E.triple) ((S.answers k.rcd.2).map OnBytes.E.triple) []) := by
  have e : idCodeSeed S cfg [] k = idCodeS (S.keyAt cfg [] k) := rfl
  rw [e] at h
  unfold idCodeS at h
  split at h
  · rw [← Option.some.inj h]
    refine Eq.trans ?_ (congrArg bytesToDig (OnBytes.Tie.idAtS_fmt (oB g) (S.keyAt cfg [] k)))
    rw [idAtS_eq]
    exact (OnBytes.K.Arm.bytesToDig_digToBytes _).symm
  · cases h

/-- If the two maps of S are one to one, two keys that differ in the seed alone get different values
of the code, if the first has a code. (The code that gives no key a code fails the premise.) -/
theorem idCodeSeed_seed_ne (S : IdSpellS L) (hA : Function.Injective S.answers)
    (hS : Function.Injective S.seed) (cfg : ByteArray) (cm : Dig 256) (s s' : L.OutOfDomainSeed) (a : L.OutOfDomainAnswer)
    (hne : s ≠ s') (hk : ∃ c, idCodeSeed S cfg [] ⟨cm, (s, a)⟩ = some c) :
    idCodeSeed S cfg [] ⟨cm, (s, a)⟩ ≠ idCodeSeed S cfg [] ⟨cm, (s', a)⟩ := by
  intro e
  obtain ⟨c, h⟩ := hk
  have h' : idCodeSeed S cfg [] ⟨cm, (s', a)⟩ = some c := by rw [← e]; exact h
  have q := idCodeSeed_oneToOne S hA hS cfg [] _ _ c h h'
  exact hne (congrArg (fun k : KeyRoot 256 L => k.rcd.1) q)

/-- **There are two keys with the same root and the same answers, and different seeds, whose codes
differ**, if the two maps of S are one to one, every key has a code and there are two seeds. The
code that gives no key a code has no such pair (`noTwoCodes_none`). -/
theorem idCodeSeed_twoCodes (S : IdSpellS L) (hA : Function.Injective S.answers)
    (hS : Function.Injective S.seed) (cfg : ByteArray)
    (hcode : ∀ k, ∃ c, idCodeSeed S cfg [] k = some c) (cm : Dig 256) (a : L.OutOfDomainAnswer) (s s' : L.OutOfDomainSeed)
    (hne : s ≠ s') :
    ∃ k k' : KeyRoot 256 L, k.cm = k'.cm ∧ k.rcd.2 = k'.rcd.2 ∧ k.rcd.1 ≠ k'.rcd.1 ∧
      idCodeSeed S cfg [] k ≠ idCodeSeed S cfg [] k' :=
  ⟨⟨cm, (s, a)⟩, ⟨cm, (s', a)⟩, rfl, rfl, hne,
    idCodeSeed_seed_ne S hA hS cfg cm s s' a hne (hcode _)⟩

end

/-- A caution: the code that gives no key a code is one to one, so `hinj` alone says little. -/
theorem oneToOne_none (IVK : Type) :
    ZKCP.CodeIsOneToOne (fun _ : IVK => (none : Option ZKCP.Str)) :=
  fun _ _ _ h _ => by cases h

/-- Under it no key has a code. -/
theorem noCode_none (IVK : Type) (k : IVK) :
    ¬ ∃ code, (fun _ : IVK => (none : Option ZKCP.Str)) k = some code :=
  fun ⟨_, h⟩ => by cases h

/-- Under it no two keys get different values. -/
theorem noTwoCodes_none (IVK : Type) :
    ¬ ∃ k k' : IVK, (fun _ : IVK => (none : Option ZKCP.Str)) k ≠
      (fun _ : IVK => (none : Option ZKCP.Str)) k' :=
  fun ⟨_, _, h⟩ => h rfl

/-- A caution: at the code that gives no key a code, `CompilerSoundnessConditionStatements.commitment b` holds too. There the
verifier behind the hash rejects every key, so "the hypothesis on the commitment holds" says
nothing by itself: it has to be read together with "every key has a code". -/
theorem CompilerSoundnessConditionStatements.commitment_of_noCode {r : InnerCompilerInput} (b : SoundnessAnalysisData r)
    (henc : r.keyCode = fun _ => none) (hext : b.ext = keyCodeIndexExtractor r) (hε : b.εId = commitmentErrorOfKeyCode) :
    CompilerSoundnessConditionStatements.commitment b :=
  CompilerSoundnessConditionStatements.commitment_of_code b (by rw [henc]; exact oneToOne_none _) hext hε

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.commitment_of_code
#print axioms VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.commitment_idSeed
#print axioms VerifiableInference.OnPublicFiles.idCodeSeed_hasCode
#print axioms VerifiableInference.OnPublicFiles.idCodeSeed_none_of_size
#print axioms VerifiableInference.OnPublicFiles.idCodeSeed_fmt_of
#print axioms VerifiableInference.OnPublicFiles.idCodeSeed_rule
#print axioms VerifiableInference.OnPublicFiles.idCodeSeed_seed_ne
#print axioms VerifiableInference.OnPublicFiles.idCodeSeed_twoCodes
#print axioms VerifiableInference.OnPublicFiles.oneToOne_none
#print axioms VerifiableInference.OnPublicFiles.noCode_none
#print axioms VerifiableInference.OnPublicFiles.noTwoCodes_none
#print axioms VerifiableInference.OnPublicFiles.CompilerSoundnessConditionStatements.commitment_of_noCode
