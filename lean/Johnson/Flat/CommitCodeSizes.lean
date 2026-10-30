-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/CommitCodeSizes.lean: at the two sizes of Johnson/Flat/TwoSizes.lean, the hypothesis
`CompilerSoundnessConditionStatements.commitment` holds once three free fields of the parameter record are set: the code of a key
(to the commitment ID's string with the record's seeds in it), the extractor and the cost.

Why it is here. Johnson/Flat/TwoSizes.lean leaves four named hypotheses open at each size;
`commitment` is one. There the code of a key (`T.enc`), the extractor (`T.ext`) and the cost
(`T.εId`) are free fields of the parameter record T. (T is a Lean structure of parameters; "a
record" below is a stored table's: seeds and answers.) This file sets these three, and two more so
that the check of a record's seeds reads the same digest and shape, and proves the hypothesis from
Johnson/Top/CommitCodeAtInnerCompilerInput.lean.

Main results (full size; the names ending in `Small` are the same at the small size).
`spellFull F P`: the tables' shape `recordGround.q.link.table`, and the library's two maps that
  write a record's answers (`spellAns`) and its seed (`spellSeed`) as lists of field elements. For
  every triple of protocols F over the full-size configuration: the record's type does not depend on
  F.
`spellFull_numbers`, `spellFull_lengths`: the shape's numbers v, cubeBits and answers are those of
  the two maps, and the two lists have the lengths that rules R4.10 and R4.11 require at that shape.
  The order of the elements (seed by seed the coordinates, then the factor; the answers by row) is
  by reading: OnBytes/K/IdSeedSpell.lean, OnBytes/K/IdTableSpell.lean.
`hasCode_spellFull`: if cfg has 32 bytes, every key has a code under
  `idCodeSeed (spellFull F P) cfg []`.
`twoCodes_spellFull`: if cfg has 32 bytes, there are two keys with the same root and answers and
  different seeds whose codes differ. It is a sanity check against the string without the seeds, not
  a second test of emptiness (Johnson/Top/CommitCodeAtInnerCompilerInput.lean).
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.withId T cfg`: T with five fields set. `enc` is that code. `ext` and `εId` are the
  library's extractor and cost. `cfg` and `shape` are two of the five fields of T that the check of
  a record's seeds reads (`t`, `cfg`, `shape`, `pl0`, `pl1`: `outOfDomainSampleQueryLayoutOfCode`, Johnson/Flat/SeedTwin.lean).
  They are set to `cfgL cfg` and to the bits of the six words of the same shape (`withIdFull_cfg`,
  `withIdFull_shape`: the definition, read back). `nameOf_shapeBytes`: the table's name inside a
  key's code is the root, then cfg, then these six words as bytes. That `cfgL cfg` holds cfg is so
  only at a cfg of 32 bytes (by reading). All other fields are T's.
`commitment_withIdFull`: `CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))`, for every T and every
  byte string cfg. No hypothesis. At a cfg whose size is not 32 bytes no key has a code
  (`noCode_withIdFull`) and the hypothesis holds trivially, since the verifier behind the hash
  rejects every proof: it says something only together with `hasCode_withIdFull`.
`hasCode_withIdFull`: if cfg has 32 bytes, every key has a code under `(T.withId cfg).enc`.
`commitment_and_codes_withIdFull`: the two together, at a cfg of 32 bytes.

Limits.
The hypothesis is met by setting free fields of T, not by proving something of a given T.
All limits of Johnson/Top/CommitCodeAtInnerCompilerInput.lean hold here: the hypothesis is an implication, and its
premise, index binding of the scheme whose verifier holds the key, is shown at neither size; cfg is
a constant, and nothing tests it against any file; nothing says that a program hashes this string.
All limits of Johnson/Flat/TwoSizes.lean hold here too. Among them: "at the two sizes" is true of
the entry file, the decoder and the depth of the stored tables alone (`G.k`, `G.c`, `G.block` are
parameters); and at the small size `proofSound` cannot be met by the small example's protocol at the
claim `claimsSmall` (by reading; that file's header).
That the hash of this code, at Lean's BLAKE2b, is the commitment ID that the Lean verifier program
computes for a table (`Key.commitmentId`, OnBytes/Key/Table.lean) is the named hypothesis
`TieHoles.idHash` (Johnson/Top/TieInnerCompiledVerifier.lean). It is not shown here.
Nothing here speaks of the C++ programs.
The proof of `CompilerSoundnessConditionStatements.commitment` here uses nothing of `T.cfg` or `T.shape`. (The hypothesis names
them, inside the verifier on both sides of its arrow.) So it holds as well where they are not the
code's (by `CompilerSoundnessConditionStatements.commitment_idSeed`; not stated at the two sizes). The other three fields that
the check of a record's seeds reads, and the encoding `m`, are T's: nothing here says that the seed
which the check derives is the format's (R4.8).
T is a parameter: `T.withId cfg` is made from a given T. `withId` must be applied last: its `ext` is
built from the `salt` and the `m` of the T that it is given and from the `enc` that it sets, so
after a later change of one of these three fields `commitment_withIdFull` does not apply. That
`InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P` or `InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P` has a member, at any A, E, G, P, is not shown
in this library (so Johnson/Flat/TwoSizes.lean's head too).
The six words of the shape in the string are those of a fixed set of parameters (`recordGround`,
`smallRecordGround`, OnBytes/Tie/EntryGrounds.lean; by that file's header the small one is made for
one small example's parameter file). `spellFull_numbers` relates v, cubeBits and answers to the two
maps. Nothing here relates the other words to the sizes of Johnson/Flat/TwoSizes.lean, `saltBytes`
to `T.salt`, or the shape to what the planner gives at a parameter file.
"Every key has a code" tests the code alone. Where `T.num` rejects every number, or a guard of
Johnson/Flat/WireAt.lean fails, the verifier accepts nothing; then the hypothesis,
`hasCode_withIdFull` and `twoCodes_spellFull` all hold and say nothing. No value is shown here at
which it accepts.
Setting `T.ext` and `T.εId` fixes the extractor and one term of the bound in the theorems of
Johnson/Flat/TwoSizes.lean. The extractor finds a key by choice among the committer's queries: it is
no program.
The other three hypotheses of Johnson/Flat/TwoSizes.lean stay hypotheses, and they are then required
at `T.withId cfg`, not at T. No theorem here states `innerCompiledVerifierSoundFromDryRunAtFullSize` or `innerCompiledVerifierSoundFromDryRunAtSmallSize` under these
three alone.
This file proves nothing about the soundness of any program. It is used in proofs only; the verifier
program does not import it.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Top.CommitCodeAtInnerCompilerInput
import Johnson.Flat.TwoSizes
import Johnson.TypedOracleCompiler.Top.IdSeedHasCode
import OnBytes.K.Left.SibLetters
import OnBytes.TypedOracleCompiler.Run.SeedVals
import OnBytes.K.SeedPort

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.OnPublicFiles
open Rom ZKCP Hiop Prob Cb Cb.Ood OnBytes.Flat OnBytes.Slice
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Tie (recordGround smallRecordGround)
open OnBytes.K.IdTable (spellAns spellSeed spellAns_inj spellSeed_inj spellAns_length
  spellSeed_length)
open OnBytes.K.Arm (room_recordGround room_smallRecordGround)
open TypedOracleCompiler.Run.SeedVals (cfgL shapeBits shapeBytes)
open TypedOracleCompiler.VerifiableInference.Rec (IdSpellS idCodeSeed)

/-! ## A table's name -/

/-- A table's name is its root, then the digest, then the six words of the shape as bytes: the bytes
whose bits `shapeBits` is. For every shape. It is `OnBytes.K.nameOf_rest`, with `shapeBytes`. -/
theorem nameOf_shapeBytes (sh : OnBytes.Params.IndexShape) (cfg : ByteArray)
    (t : OnBytes.Params.TableName) :
    OnBytes.Key.nameOf sh cfg t =
      t.root ++ (cfg ++ shapeBytes sh.code.logN sh.code.ell sh.code.r sh.v sh.answers
        sh.saltBytes) := by
  rw [OnBytes.K.nameOf_rest]
  unfold OnBytes.K.restOf shapeBytes
  simp only [ByteArray.append_assoc]

/-! ## Two seeds -/

/-- A seed with one point, all of whose lg coordinates are 0, and the factor 1. -/
def seedZeros (lg : ℕ) : Fin 1 → (Fin lg → GE) × NZ := fun _ => (fun _ => 0, ⟨1, one_ne_zero⟩)

/-- The same with all coordinates 1. -/
def seedOnes (lg : ℕ) : Fin 1 → (Fin lg → GE) × NZ := fun _ => (fun _ => 1, ⟨1, one_ne_zero⟩)

/-- The two differ, if a point has a coordinate. -/
theorem seedZeros_ne_seedOnes (lg : ℕ) (h : 0 < lg) : seedZeros lg ≠ seedOnes lg := fun e =>
  zero_ne_one (α := GE) (congrFun (congrArg Prod.fst (congrFun e 0)) ⟨0, h⟩)

/-! ## The full size -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A} (F : OnBytes.Flat.Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)

/-- The tables' shape at the full size, and how a record's answers and its seed are encoded. -/
def spellFull : IdSpellS (F.withProvers P) where
  shape := recordGround.q.link.table
  answers := spellAns frS.P.v 1
  seed := spellSeed 29 1

/-- The shape's three numbers are those of the two maps. -/
theorem spellFull_numbers : (spellFull F P).shape.v = frS.P.v ∧
    (spellFull F P).shape.cubeBits = 29 ∧ (spellFull F P).shape.answers = 1 :=
  OnBytes.K.Left.numbers_full

set_option maxRecDepth 20000 in
/-- The two lists have the lengths that the format's rules R4.10 and R4.11 require at the shape:
answers times (cubeBits + 1) elements for the seeds, and 2^v times answers for the answers. -/
theorem spellFull_lengths (s : (F.withProvers P).OutOfDomainSeed) (a : (F.withProvers P).OutOfDomainAnswer) :
    ((spellFull F P).seed s).length =
        (spellFull F P).shape.answers * ((spellFull F P).shape.cubeBits + 1) ∧
      ((spellFull F P).answers a).length =
        2 ^ (spellFull F P).shape.v * (spellFull F P).shape.answers := by
  obtain ⟨hv, hb, ha⟩ := spellFull_numbers F P
  rw [hv, hb, ha]
  exact ⟨spellSeed_length 29 1 s, spellAns_length frS.P.v 1 a⟩

set_option maxRecDepth 20000 in
/-- **Every key has a code**, if cfg has 32 bytes. (The hash's input (R4.11) has 176 + 24 · 30 +
24 · 2^v bytes; the theorem does not state the number.) The bound on the length is evaluated in
Lean's kernel. -/
theorem hasCode_spellFull (cfg : ByteArray) (hc : cfg.size = 32) (k : KeyRoot 256 (F.withProvers P)) :
    ∃ code, idCodeSeed (spellFull F P) cfg [] k = some code := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := room_recordGround
  exact idCodeSeed_hasCode (spellFull F P) cfg hc (1 * (29 + 1)) (2 ^ frS.P.v * 1)
    (spellSeed_length 29 1) (spellAns_length frS.P.v 1) h1 h2 h3 h4 h5 h6 (by decide +kernel) k

set_option maxRecDepth 20000 in
/-- **There are two keys with the same root and answers and different seeds whose codes differ**, if
cfg has 32 bytes. The two: the root of 256 zero bits, all answers 0, the seeds `seedZeros 29` and
`seedOnes 29`. -/
theorem twoCodes_spellFull (cfg : ByteArray) (hc : cfg.size = 32) :
    ∃ k k' : KeyRoot 256 (F.withProvers P), k.cm = k'.cm ∧ k.rcd.2 = k'.rcd.2 ∧ k.rcd.1 ≠ k'.rcd.1 ∧
      idCodeSeed (spellFull F P) cfg [] k ≠ idCodeSeed (spellFull F P) cfg [] k' :=
  idCodeSeed_twoCodes (spellFull F P) (spellAns_inj frS.P.v 1) (spellSeed_inj 29 1) cfg
    (hasCode_spellFull F P cfg hc) (fun _ => false)
    (show (Fin frS.P.v → Bool) × Fin 1 → GE from fun _ => 0) (seedZeros 29) (seedOnes 29)
    (seedZeros_ne_seedOnes 29 (by decide))

end

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X} {E : Coding A} {G : FilesParameters X RecFull}
  {P : (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- T with the commitment ID's string, the record's seeds in it, as the code of a key, and with
`cfgL cfg` and the bits of the same shape's six words in two of the five fields that the check of a
record's seeds reads. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.withCode (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P :=
  { T with
    enc := idCodeSeed (spellFull (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P) cfg []
    cfg := cfgL cfg
    shape := shapeBits recordGround.q.link.table.code.logN recordGround.q.link.table.code.ell
      recordGround.q.link.table.code.r recordGround.q.link.table.v
      recordGround.q.link.table.answers recordGround.q.link.table.saltBytes }

/-- T with these three, the library's extractor and the library's cost. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize.withId (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P :=
  { T.withCode cfg with
    ext := keyCodeIndexExtractor (innerCompilerInputFromDryRunAtFullSize (T.withCode cfg))
    εId := commitmentErrorOfKeyCode }

/-- By definition: the field `cfg` is `cfgL cfg`, the first 256 bits of the cfg that the code
holds. -/
theorem withIdFull_cfg (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    (T.withId cfg).cfg = cfgL cfg := rfl

/-- By definition: the field `shape` is the bits of the six words of the shape that the code
holds. -/
theorem withIdFull_shape (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    (T.withId cfg).shape = shapeBits recordGround.q.link.table.code.logN
      recordGround.q.link.table.code.ell recordGround.q.link.table.code.r
      recordGround.q.link.table.v recordGround.q.link.table.answers
      recordGround.q.link.table.saltBytes := rfl

set_option maxRecDepth 20000 in
/-- **The hypothesis on the commitment at the full size**, met by setting five fields of T. For
every cfg; at a cfg whose size is not 32 bytes it holds trivially (see `hasCode_withIdFull`). -/
theorem commitment_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)) :=
  CompilerSoundnessConditionStatements.commitment_idSeed (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg))
    (spellFull (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P) (spellAns_inj frS.P.v 1) (spellSeed_inj 29 1) cfg
    rfl rfl rfl

set_option maxRecDepth 20000 in
/-- **Every key has a code there**, if cfg has 32 bytes. -/
theorem hasCode_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) (hc : cfg.size = 32)
    (k : KeyRoot 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P)) :
    ∃ code, (T.withId cfg).enc k = some code :=
  hasCode_spellFull (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P cfg hc k

set_option maxRecDepth 20000 in
/-- At a cfg whose size is not 32 bytes no key has a code there. -/
theorem noCode_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray) (h : cfg.size ≠ 32)
    (k : KeyRoot 256 ((threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G).withProvers P)) : (T.withId cfg).enc k = none :=
  idCodeSeed_none_of_size (spellFull (threeProtocolsFromDryRunAtFullSize A (relationsAndEncodingOfClaims A E) G) P) cfg h k

/-- **The two together**, at a cfg of 32 bytes: the hypothesis holds, and every key has a code. -/
theorem commitment_and_codes_withIdFull (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtFullSize A E G P) (cfg : ByteArray)
    (hc : cfg.size = 32) :
    CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtFullSize (T.withId cfg)) ∧
      ∀ k, ∃ code, (T.withId cfg).enc k = some code :=
  ⟨commitment_withIdFull T cfg, hasCode_withIdFull T cfg hc⟩

end

/-! ## The small size -/

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X}
  {R : (srS.toDecR srZ 524285).RelationsAndEncoding A} (F : OnBytes.Flat.Files (DecR.configurationOfStoredTable A R)) (P : F.Provers)

/-- The tables' shape at the small size, and how a record's answers and its seed are encoded. -/
def spellSmall : IdSpellS (F.withProvers P) where
  shape := smallRecordGround.q.link.table
  answers := spellAns srS.P.v 1
  seed := spellSeed 19 1

/-- The shape's three numbers are those of the two maps. -/
theorem spellSmall_numbers : (spellSmall F P).shape.v = srS.P.v ∧
    (spellSmall F P).shape.cubeBits = 19 ∧ (spellSmall F P).shape.answers = 1 :=
  OnBytes.K.Left.numbers_small

set_option maxRecDepth 20000 in
/-- The two lists have the lengths that the format's rules R4.10 and R4.11 require at the shape:
answers times (cubeBits + 1) elements for the seeds, and 2^v times answers for the answers. -/
theorem spellSmall_lengths (s : (F.withProvers P).OutOfDomainSeed) (a : (F.withProvers P).OutOfDomainAnswer) :
    ((spellSmall F P).seed s).length =
        (spellSmall F P).shape.answers * ((spellSmall F P).shape.cubeBits + 1) ∧
      ((spellSmall F P).answers a).length =
        2 ^ (spellSmall F P).shape.v * (spellSmall F P).shape.answers := by
  obtain ⟨hv, hb, ha⟩ := spellSmall_numbers F P
  rw [hv, hb, ha]
  exact ⟨spellSeed_length 19 1 s, spellAns_length srS.P.v 1 a⟩

set_option maxRecDepth 20000 in
/-- **Every key has a code**, if cfg has 32 bytes. (The hash's input (R4.11) has 176 + 24 · 20 +
24 · 2^v bytes; the theorem does not state the number.) The bound on the length is evaluated in
Lean's kernel. -/
theorem hasCode_spellSmall (cfg : ByteArray) (hc : cfg.size = 32) (k : KeyRoot 256 (F.withProvers P)) :
    ∃ code, idCodeSeed (spellSmall F P) cfg [] k = some code := by
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := room_smallRecordGround
  exact idCodeSeed_hasCode (spellSmall F P) cfg hc (1 * (19 + 1)) (2 ^ srS.P.v * 1)
    (spellSeed_length 19 1) (spellAns_length srS.P.v 1) h1 h2 h3 h4 h5 h6 (by decide +kernel) k

set_option maxRecDepth 20000 in
/-- **There are two keys with the same root and answers and different seeds whose codes differ**, if
cfg has 32 bytes. The two: the root of 256 zero bits, all answers 0, the seeds `seedZeros 19` and
`seedOnes 19`. -/
theorem twoCodes_spellSmall (cfg : ByteArray) (hc : cfg.size = 32) :
    ∃ k k' : KeyRoot 256 (F.withProvers P), k.cm = k'.cm ∧ k.rcd.2 = k'.rcd.2 ∧ k.rcd.1 ≠ k'.rcd.1 ∧
      idCodeSeed (spellSmall F P) cfg [] k ≠ idCodeSeed (spellSmall F P) cfg [] k' :=
  idCodeSeed_twoCodes (spellSmall F P) (spellAns_inj srS.P.v 1) (spellSeed_inj 19 1) cfg
    (hasCode_spellSmall F P cfg hc) (fun _ => false)
    (show (Fin srS.P.v → Bool) × Fin 1 → GE from fun _ => 0) (seedZeros 19) (seedOnes 19)
    (seedZeros_ne_seedOnes 19 (by decide))

end

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {E : Coding A} {G : FilesParameters X RecSmall}
  {P : (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).Provers}

/-- T with the commitment ID's string, the record's seeds in it, as the code of a key, and with
`cfgL cfg` and the bits of the same shape's six words in two of the five fields that the check of a
record's seeds reads. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.withCode (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P :=
  { T with
    enc := idCodeSeed (spellSmall (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P) cfg []
    cfg := cfgL cfg
    shape := shapeBits smallRecordGround.q.link.table.code.logN
      smallRecordGround.q.link.table.code.ell smallRecordGround.q.link.table.code.r
      smallRecordGround.q.link.table.v smallRecordGround.q.link.table.answers
      smallRecordGround.q.link.table.saltBytes }

/-- T with these three, the library's extractor and the library's cost. -/
def InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize.withId (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P :=
  { T.withCode cfg with
    ext := keyCodeIndexExtractor (innerCompilerInputFromDryRunAtSmallSize (T.withCode cfg))
    εId := commitmentErrorOfKeyCode }

/-- By definition: the field `cfg` is `cfgL cfg`, the first 256 bits of the cfg that the code
holds. -/
theorem withIdSmall_cfg (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    (T.withId cfg).cfg = cfgL cfg := rfl

/-- By definition: the field `shape` is the bits of the six words of the shape that the code
holds. -/
theorem withIdSmall_shape (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    (T.withId cfg).shape = shapeBits smallRecordGround.q.link.table.code.logN
      smallRecordGround.q.link.table.code.ell smallRecordGround.q.link.table.code.r
      smallRecordGround.q.link.table.v smallRecordGround.q.link.table.answers
      smallRecordGround.q.link.table.saltBytes := rfl

set_option maxRecDepth 20000 in
/-- **The hypothesis on the commitment at the small size**, met by setting five fields of T. For
every cfg; at a cfg whose size is not 32 bytes it holds trivially (see `hasCode_withIdSmall`). -/
theorem commitment_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) :
    CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)) :=
  CompilerSoundnessConditionStatements.commitment_idSeed (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg))
    (spellSmall (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P) (spellAns_inj srS.P.v 1) (spellSeed_inj 19 1) cfg
    rfl rfl rfl

set_option maxRecDepth 20000 in
/-- **Every key has a code there**, if cfg has 32 bytes. -/
theorem hasCode_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) (hc : cfg.size = 32)
    (k : KeyRoot 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P)) :
    ∃ code, (T.withId cfg).enc k = some code :=
  hasCode_spellSmall (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P cfg hc k

set_option maxRecDepth 20000 in
/-- At a cfg whose size is not 32 bytes no key has a code there. -/
theorem noCode_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray) (h : cfg.size ≠ 32)
    (k : KeyRoot 256 ((threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G).withProvers P)) : (T.withId cfg).enc k = none :=
  idCodeSeed_none_of_size (spellSmall (threeProtocolsFromDryRunAtSmallSize A (relationsAndEncodingOfClaims A E) G) P) cfg h k

/-- **The two together**, at a cfg of 32 bytes: the hypothesis holds, and every key has a code. -/
theorem commitment_and_codes_withIdSmall (T : InnerCompilerInputAndAnalysisFieldsFromDryRunAtSmallSize A E G P) (cfg : ByteArray)
    (hc : cfg.size = 32) :
    CompilerSoundnessConditionStatements.commitment (soundnessAnalysisDataFromDryRunAtSmallSize (T.withId cfg)) ∧
      ∀ k, ∃ code, (T.withId cfg).enc k = some code :=
  ⟨commitment_withIdSmall T cfg, hasCode_withIdSmall T cfg hc⟩

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.nameOf_shapeBytes
#print axioms VerifiableInference.OnPublicFiles.seedZeros_ne_seedOnes
#print axioms VerifiableInference.OnPublicFiles.spellFull_numbers
#print axioms VerifiableInference.OnPublicFiles.hasCode_spellFull
#print axioms VerifiableInference.OnPublicFiles.twoCodes_spellFull
#print axioms VerifiableInference.OnPublicFiles.commitment_withIdFull
#print axioms VerifiableInference.OnPublicFiles.hasCode_withIdFull
#print axioms VerifiableInference.OnPublicFiles.noCode_withIdFull
#print axioms VerifiableInference.OnPublicFiles.commitment_and_codes_withIdFull
#print axioms VerifiableInference.OnPublicFiles.spellFull_lengths
#print axioms VerifiableInference.OnPublicFiles.withIdFull_cfg
#print axioms VerifiableInference.OnPublicFiles.withIdFull_shape
#print axioms VerifiableInference.OnPublicFiles.spellSmall_numbers
#print axioms VerifiableInference.OnPublicFiles.hasCode_spellSmall
#print axioms VerifiableInference.OnPublicFiles.twoCodes_spellSmall
#print axioms VerifiableInference.OnPublicFiles.commitment_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.hasCode_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.noCode_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.commitment_and_codes_withIdSmall
#print axioms VerifiableInference.OnPublicFiles.spellSmall_lengths
#print axioms VerifiableInference.OnPublicFiles.withIdSmall_cfg
#print axioms VerifiableInference.OnPublicFiles.withIdSmall_shape
