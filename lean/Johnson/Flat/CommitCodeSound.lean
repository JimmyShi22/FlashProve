-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/CommitCodeSound.lean: the soundness theorems of Johnson/Flat/TwoSizes.lean at the
parameter record `T.withId cfg` (Johnson/Flat/CommitCodeSizes.lean), under three of their four named
hypotheses.

Why it is here. `innerCompiledVerifierSoundFromDryRunAtFullSize` and `innerCompiledVerifierSoundFromDryRunAtSmallSize` take four named hypotheses that are unproved:
`keySound`, `proofSound`, `commitment`, `sound`. In Johnson/Flat/CommitCodeSizes.lean `commitment`
is met at `T.withId cfg`, that is at T with five fields set: the code of a key, the extractor, the
cost (the second term of the bound), and two fields that the check of a stored table's seeds reads.
This file feeds that to the two theorems.

Main results (full size; the names with `Small` for `Full` are the same at the small size).
`LeftWithIdFull T`: the three hypotheses `keySound`, `proofSound`, `sound`, at T itself.
`keySound_withIdFull`, `proofSound_withIdFull`, `sound_withIdFull`: each of the three is the same
  proposition at `T.withId cfg` and at T. By definition: none of them reads one of the five fields.
`LeftWithIdFull.left`: so the three at T give all four at `T.withId cfg`, for every byte string cfg.
`innerCompiledVerifierSoundFromDryRunAtFullSize_withId`: under `LeftWithIdFull T` and the statement on codes `BCHKS46At GF GE`, the
  conclusion of `innerCompiledVerifierSoundFromDryRunAtFullSize` at `T.withId cfg`, for every cfg.
`innerCompiledVerifierSoundFromDryRunAtFullSize_withId_hasCode`: if cfg has 32 bytes, that conclusion together with "every key has a
  code under `(T.withId cfg).enc`". At a cfg whose size is not 32 bytes no key has a code
  (`noCode_withIdFull`), so the verifier rejects every proof (by reading: `verifyDigestKey`,
  ZKCP/DigestKey.lean) and `innerCompiledVerifierSoundFromDryRunAtFullSize_withId` holds trivially. So `innerCompiledVerifierSoundFromDryRunAtFullSize_withId_hasCode`
  is the form to cite.
`compiledSoundnessError_withIdFull`: the bound there is the bound's first term at T plus (t + 2)² /
  2^256. By definition. The first term depends on G through the number of the verifier's queries. No
  number is evaluated, and the bound is not shown to be below 1 at any value.
`soundThreeFull_req_withId`, `soundThreeFull_ref_withId` (full size alone): in
Johnson/Flat/ThreeFull.lean `sound` is proved at the claim `claimsReq` (by `meaningConditionFromDryRunAtFullSize_paid_req`,
Johnson/Flat/LedgerAtInnerCompilerInputReq.lean), under hypotheses that fix parameters (five; at the numbers
`numsRef` three); `keySound`, `proofSound`, `commitment` are left. At `T.withId cfg` its two
theorems hold under `keySound` and `proofSound` at T, these hypotheses and the statement on codes.
By that file's header, at other numbers than `numsRef` the first says nothing of the shipped files.
`soundThreeFull_ref_withId_hasCode`: if cfg has 32 bytes, the second together with "every key has a
  code": of the three, the form to cite. Johnson/Flat/ThreeAtFiles.lean states another form
  (`soundThreeFull_guarded`: s and G made of three public files,
  the test
  `guardsAtB Z = true` among the hypotheses); no form of it at `T.withId cfg` is stated here.

Limits.
How to count what this file gives. `commitment` holds at `T.withId cfg` because we chose five free
fields of the record (`enc`, `cfg`, `shape`, `ext`, `εId`), not because anything is proved of a
given record. In a count of the hypotheses of `innerCompiledVerifier_sound` (`CompilerSoundnessConditionsWithMeaning`,
Johnson/Top/InnerCompiledVerifier.lean; the count at the two sizes: the header of Johnson/Flat/TwoSizes.lean)
it is to be counted with `wires`, as holding by our own choice of values, and not with those that
are proved. The digest cfg, which `withId` writes into the code of a key (`enc`) and into the field
`cfg`, is a constant, fixed before the hash function is drawn. That is a fault: the format's
specification rules it out for a model of the format (below). This way of meeting `commitment` does
not survive a repair of that fault: if the description of the protocol (`InnerCompilerInput`) takes the
digest of the public files from the drawn hash function, the type of the key changes, the theorems
of this file do not apply, and `commitment` is open. What can meet it there is
`commitmentBinds_encSeed` (Johnson/TypedOracleCompiler/Top/IdKeySeedCode.lean). It is general: it holds for every
scheme whose key holds the public digests, at the code `encSeed`, the library's extractor and its
cost, under three premises on parameters. So there too the hypothesis would be met by setting `enc`,
`ext` and `εId`. No file of this library applies it.
The system, the extractor and the bound in the conclusion are those at `T.withId cfg`, not at T. The
fourth hypothesis is met by changing T, not proved of a given T. At other values of the five fields
nothing is shown here.
The count of three leaves out what the types of the parameters require. T holds an encoding of all
typed hash queries in one hash function (`T.m : OracleCoding`, Rom/Family.lean: one to one and onto all bit
strings), and A holds a law too (`A.mat_cut`). That `InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P` or
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P` has a member, at any A, E, G, P, is not shown in this library. If it has
none, every theorem of this file holds trivially.
`innerCompiledVerifierSoundFromDryRunAtFullSize`, `innerCompiledVerifierSoundFromDryRunAtSmallSize` and `soundThreeFull_req` are about `innerCompiledVerifier`, the verifier that
this library's compiler makes from a description of the protocol (`InnerCompilerInput`); lean/README.md calls
it verify(). What relates `innerCompiledVerifier` to the Lean verifier program is `exit_innerCompiledVerifier`
(Johnson/Top/TieInnerCompiledVerifier.lean), under hypotheses that are proved at no input.
The three hypotheses that stay are unproved. The statement on codes (`BCHKS46At GF GE`) stays a
hypothesis here, as in Johnson/Flat/TwoSizes.lean. The library proves it (`Cb.Gl.bchks46At`,
Cb/Bridge/GlCodesProved.lean) from the files under lean/ThirdParty/, adapted from
ArkLib and Mathlib (lean/LIMITS.md, L15). It is not the published theorem on
codes (lean/README.md, fact 1). `innerCompiledVerifierSoundFromDryRunAtFullSize_codes`, `innerCompiledVerifierSoundFromDryRunAtSmallSize_codes` and
`soundThreeFull_ref_codes` (Johnson/Flat/TwoSizesCodes.lean) would give the forms without it (not
stated here).
All limits in the header of Johnson/Flat/TwoSizes.lean hold here. Among them: no value of the
parameters is given, and none is shown to meet the three; where one of the two tests of
`GuardsPassFull` | `GuardsPassSmall` (Johnson/Flat/WireAt.lean) fails, a hypothesis on soundness
holds trivially (by reading, as the header of Johnson/Flat/TwoSizes.lean says: no theorem);
`proofSound` may be false at a G that nothing relates to the programs' plan; by that header, at the
small size `proofSound` cannot be met by the small example's protocol at the claim `claimsSmall`,
and is not expected to be met there at `claimsLedger` or `claimsReq`. If `T.build` returns nothing,
or rejects every output that is not the model's, `sound` holds whatever the relation is (the header
of Johnson/Top/InnerCompiledVerifier.lean).
All limits of Johnson/Flat/CommitCodeSizes.lean and Johnson/Top/CommitCodeAtInnerCompilerInput.lean hold here. Among
them: the digest cfg is a constant, which the format's specification rules out for a model of the
format (docs/format/FORMAT.md, section 18): the functions whose digest of the public files is cfg
are a share of 2^-256 of all functions (by reading), less than the term (t + 2)² / 2^256 of the
bound alone, so the bound here says by itself nothing of a scheme that computes cfg with the same
hash function; that the hash of the key's code is the commitment ID which the Lean verifier program
computes is the hypothesis `TieHoles.idHash` (Johnson/Top/TieInnerCompiledVerifier.lean),
not shown; no value is shown at which the verifier accepts.
All limits in the header of Johnson/Flat/ThreeFull.lean hold of `soundThreeFull_req_withId`,
`soundThreeFull_ref_withId` and `soundThreeFull_ref_withId_hasCode`. Among them: `sound` is proved
there in exchange for hypotheses that fix parameters, and what the claim means then depends on
`keySound` and `proofSound` at the claim `claimsReq`, which stay hypotheses; the table of scales s
is a parameter, and by that header the theorem says something at one s at most, which it does not
name; that the two numbers of `numsRef` are those of the full-size parameter file is not shown.
This file proves nothing about the soundness of any program. It is used in proofs only; the verifier
program does not import it.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.CommitCodeSizes
import Johnson.Flat.ThreeFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open Inst.Model
open Inst.Model.Layout (kRef hRef)

/-! ## The full size -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {G : FilesParameters X RecFull}
  {P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- The three named hypotheses that are left at this size once `commitment` is met by setting five
fields (`withId`): those of `RemainingSoundnessConditionsFromDryRunAtFullSize` without that field. They are stated at T itself. -/
structure LeftWithIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T)
  sound      : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T)

set_option maxRecDepth 20000 in
/-- By definition: `keySound` reads none of the five fields that `withId` sets. -/
theorem keySound_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)) ↔ CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T) := Iff.rfl

set_option maxRecDepth 20000 in
/-- By definition: `proofSound` reads none of the five fields that `withId` sets. -/
theorem proofSound_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)) ↔ CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T) :=
  Iff.rfl

set_option maxRecDepth 20000 in
/-- By definition: `sound` names `innerSystem`, but reads of it only the type of weights and the model
(`IsModelOutput`), so none of the five fields that `withId` sets. -/
theorem sound_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)) ↔ CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtFullSize T) := Iff.rfl

/-- The three at T give the four at `T.withId cfg`. -/
theorem LeftWithIdFull.left {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P} (h : LeftWithIdFull T) (cfg : ByteArray) :
    RemainingSoundnessConditionsFromDryRunAtFullSize (T.withId cfg) where
  keySound := (keySound_withIdFull T cfg).2 h.keySound
  proofSound := (proofSound_withIdFull T cfg).2 h.proofSound
  commitment := commitment_withIdFull T cfg
  sound := (sound_withIdFull T cfg).2 h.sound

/-- **The soundness theorem at the full size, at `T.withId cfg`, under three named hypotheses** and
the statement on codes (hypotheses of the theorem: Lean's list of axioms does not show them). For
every cfg; at a cfg whose size is not 32 bytes it holds trivially (see
`innerCompiledVerifierSoundFromDryRunAtFullSize_withId_hasCode`). -/
theorem innerCompiledVerifierSoundFromDryRunAtFullSize_withId (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P}
    (h : LeftWithIdFull T) (cfg : ByteArray) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg)))
      (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg))).IsModelOutput
      (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))) :=
  innerCompiledVerifierSoundFromDryRunAtFullSize hA (h.left cfg)

/-- **The same together with "every key has a code"**, at a cfg of 32 bytes: the form to cite. -/
theorem innerCompiledVerifierSoundFromDryRunAtFullSize_withId_hasCode (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P}
    (h : LeftWithIdFull T) (cfg : ByteArray) (hc : cfg.size = 32) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg)))
        (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)))
        (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg))).IsModelOutput
        (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))) ∧
      ∀ k, ∃ code, (T.withId cfg).enc k = some code :=
  ⟨innerCompiledVerifierSoundFromDryRunAtFullSize_withId hA h cfg, hasCode_withIdFull T cfg hc⟩

set_option maxRecDepth 20000 in
/-- By definition: the bound at `T.withId cfg` is the first term of the bound at T, plus
(t + 2)² / 2^256. -/
theorem compiledSoundnessError_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)) =
      fun t => soundnessBoundOverTypedOracles (innerCompilerInputFromDryRunAtFullSize T).queryLayout (soundnessAnalysisDataFromDryRunAtFullSize T).εs t 0 + commitmentErrorOfKeyCode t := rfl

end

/-! ## The full size, where `sound` is proved too -/

section
variable (N : MatrixNums) (s : Cm.Scales)
  (E : Coding (claimsReq (frS.toDecR frZ 402653181) N s)) (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **`soundThreeFull_req` (Johnson/Flat/ThreeFull.lean) at `T.withId cfg`, under two named
hypotheses**, `keySound` and `proofSound` at T, beside that theorem's five hypotheses that fix
parameters and the statement on codes. `withId` changes neither `T.build` nor `T.nextToken`. For
every cfg; at a cfg whose size is not 32 bytes it holds trivially. -/
theorem soundThreeFull_req_withId (hA : BCHKS46At GF GE) (lawful : s.Lawful) (hr : N.rows ≤ hRef)
    (hc : 2 ^ (N.kLo + (frS.toDecR frZ 402653181).v) ≤ 2 ^ kRef)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) N s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l)
    (hK : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T)) (hP : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T))
    (cfg : ByteArray) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg)))
      (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg))).IsModelOutput
      (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))) :=
  soundThreeFull_req N s E G P hA lawful hr hc (T.withId cfg) hb hn
    ⟨(keySound_withIdFull T cfg).2 hK, (proofSound_withIdFull T cfg).2 hP,
      commitment_withIdFull T cfg⟩

end

section
variable (s : Cm.Scales) (E : Coding (claimsReq (frS.toDecR frZ 402653181) numsRef s))
  (G : FilesParameters Flat.Req RecFull)
  (P : (threeProtocolsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) (relationsAndEncodingOfClaims _ E) G).Provers)

/-- **The same at the numbers of the reference shape**: the statement of `soundThreeFull_ref`
(Johnson/Flat/ThreeFull.lean) at `T.withId cfg`; the proof calls `soundThreeFull_req_withId`. The
two bounds on the numbers are no hypotheses there. For every cfg; at a cfg whose size is not 32
bytes it holds trivially (see `soundThreeFull_ref_withId_hasCode`). -/
theorem soundThreeFull_ref_withId (hA : BCHKS46At GF GE) (lawful : s.Lawful)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l)
    (hK : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T)) (hP : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T))
    (cfg : ByteArray) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg)))
      (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)))
      (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg))).IsModelOutput
      (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))) :=
  soundThreeFull_req_withId numsRef s E G P hA lawful numsRef_fits.1 numsRef_fits.2 T hb hn hK hP
    cfg

/-- **The same together with "every key has a code"**, at a cfg of 32 bytes: the form to cite. -/
theorem soundThreeFull_ref_withId_hasCode (hA : BCHKS46At GF GE) (lawful : s.Lawful)
    (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize (claimsReq (frS.toDecR frZ 402653181) numsRef s) E G P)
    (hb : ∀ x' a, T.build x' a = Flat.buildReq x' a)
    (hn : ∀ M l, T.nextToken M l = Flat.nextTok s M l)
    (hK : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtFullSize T)) (hP : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtFullSize T))
    (cfg : ByteArray) (h32 : cfg.size = 32) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg)))
        (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)))
        (innerSystem (innerCompilerInputFromDryRunAtFullSize (T.withId cfg))).IsModelOutput
        (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))) ∧
      ∀ k, ∃ code, (T.withId cfg).enc k = some code :=
  ⟨soundThreeFull_ref_withId s E G P hA lawful T hb hn hK hP cfg, hasCode_withIdFull T cfg h32⟩

end

/-! ## The small size -/

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {G : FilesParameters X RecSmall}
  {P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- The three named hypotheses that are left at this size once `commitment` is met by setting five
fields (`withId`): those of `RemainingSoundnessConditionsFromDryRunAtSmallSize` without that field. They are stated at T itself. Of the
three, `proofSound` cannot be met by the small example's protocol at the claim `claimsSmall`, and is
not expected to be met at `claimsLedger` or `claimsReq` (by reading, no theorem: the header of
Johnson/Flat/TwoSizes.lean). -/
structure LeftWithIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) : Prop where
  keySound   : CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtSmallSize T)
  proofSound : CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtSmallSize T)
  sound      : CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtSmallSize T)

set_option maxRecDepth 20000 in
/-- By definition: `keySound` reads none of the five fields that `withId` sets. -/
theorem keySound_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)) ↔ CompilerSoundnessConditionStatements.keySound (soundnessAnalysisDataFromDryRunAtSmallSize T) := Iff.rfl

set_option maxRecDepth 20000 in
/-- By definition: `proofSound` reads none of the five fields that `withId` sets. -/
theorem proofSound_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)) ↔ CompilerSoundnessConditionStatements.proofSound (soundnessAnalysisDataFromDryRunAtSmallSize T) :=
  Iff.rfl

set_option maxRecDepth 20000 in
/-- By definition: `sound` names `innerSystem`, but reads of it only the type of weights and the model
(`IsModelOutput`), so none of the five fields that `withId` sets. -/
theorem sound_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)) ↔ CompilerSoundnessConditionStatements.sound (soundnessAnalysisDataFromDryRunAtSmallSize T) := Iff.rfl

/-- The three at T give the four at `T.withId cfg`. -/
theorem LeftWithIdSmall.left {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P} (h : LeftWithIdSmall T)
    (cfg : ByteArray) : RemainingSoundnessConditionsFromDryRunAtSmallSize (T.withId cfg) where
  keySound := (keySound_withIdSmall T cfg).2 h.keySound
  proofSound := (proofSound_withIdSmall T cfg).2 h.proofSound
  commitment := commitment_withIdSmall T cfg
  sound := (sound_withIdSmall T cfg).2 h.sound

/-- **The soundness theorem at the small size, at `T.withId cfg`, under three named hypotheses** and
the statement on codes (hypotheses of the theorem: Lean's list of axioms does not show them). For
every cfg; at a cfg whose size is not 32 bytes it holds trivially (see
`innerCompiledVerifierSoundFromDryRunAtSmallSize_withId_hasCode`). On `proofSound` at this size: see `LeftWithIdSmall`. -/
theorem innerCompiledVerifierSoundFromDryRunAtSmallSize_withId (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P}
    (h : LeftWithIdSmall T) (cfg : ByteArray) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtSmallSize (T.withId cfg)))
      (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)))
      (innerSystem (innerCompilerInputFromDryRunAtSmallSize (T.withId cfg))).IsModelOutput
      (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg))) :=
  innerCompiledVerifierSoundFromDryRunAtSmallSize hA (h.left cfg)

/-- **The same together with "every key has a code"**, at a cfg of 32 bytes: the form to cite, with
the limit on `proofSound` at this size (see `LeftWithIdSmall`). -/
theorem innerCompiledVerifierSoundFromDryRunAtSmallSize_withId_hasCode (hA : BCHKS46At GF GE) {T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P}
    (h : LeftWithIdSmall T) (cfg : ByteArray) (hc : cfg.size = 32) :
    SoundForWith (innerSystem (innerCompilerInputFromDryRunAtSmallSize (T.withId cfg)))
        (compiledIndexExtractor (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)))
        (innerSystem (innerCompilerInputFromDryRunAtSmallSize (T.withId cfg))).IsModelOutput
        (compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg))) ∧
      ∀ k, ∃ code, (T.withId cfg).enc k = some code :=
  ⟨innerCompiledVerifierSoundFromDryRunAtSmallSize_withId hA h cfg, hasCode_withIdSmall T cfg hc⟩

set_option maxRecDepth 20000 in
/-- By definition: the bound at `T.withId cfg` is the first term of the bound at T, plus
(t + 2)² / 2^256. -/
theorem compiledSoundnessError_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    compiledSoundnessError (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)) =
      fun t => soundnessBoundOverTypedOracles (innerCompilerInputFromDryRunAtSmallSize T).queryLayout (soundnessAnalysisDataFromDryRunAtSmallSize T).εs t 0 + commitmentErrorOfKeyCode t := rfl

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.keySound_withIdFull
#print axioms VerifiableInference.OnPublicFiles.proofSound_withIdFull
#print axioms VerifiableInference.OnPublicFiles.sound_withIdFull
#print axioms VerifiableInference.OnPublicFiles.LeftWithIdFull.left
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtFullSize_withId
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtFullSize_withId_hasCode
#print axioms VerifiableInference.OnPublicFiles.compiledSoundnessError_withIdFull
#print axioms VerifiableInference.OnPublicFiles.soundThreeFull_req_withId
#print axioms VerifiableInference.OnPublicFiles.soundThreeFull_ref_withId
#print axioms VerifiableInference.OnPublicFiles.soundThreeFull_ref_withId_hasCode
#print axioms VerifiableInference.OnPublicFiles.keySound_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.proofSound_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.sound_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.LeftWithIdSmall.left
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtSmallSize_withId
#print axioms VerifiableInference.OnPublicFiles.innerCompiledVerifierSoundFromDryRunAtSmallSize_withId_hasCode
#print axioms VerifiableInference.OnPublicFiles.compiledSoundnessError_withIdSmall
