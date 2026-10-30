-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/SeedTwin.lean: the wire of the record of the second form of the compiler with a record
(`OutOfDomainSampleQueryLayout`, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean) as a written value, with what that compiler asks of it:
no two records are written alike; all records are written with one number of digests; the seed's
law.

Definitions and theorems. First for any object with records L, then at the object of five
sub-protocols over the configuration of the entry's link (`DecR.configurationOfStoredTable`, OnBytes/Slice/ConfOf.lean, at
the decoder of OnBytes/Flat/EntryValue.lean's theorems), at the full size and at the small example.

Main names.
 `outOfDomainSampleQueryLayoutOfCode L Bd aT aL t cfg shape pl0 pl1 num seed rc`: the wire. Written here: a record, read by `rc`
   as a record in plain letters, goes to the list `codeP` (OnBytes/Flat/RecordCode.lean).
   Arguments, of which nothing is asked: the tag `t` of the seeds' queries; what a table's name
   holds behind the root (`cfg`, `shape`); the two queries' plain parts; `num`; the map `seed`.
 `outOfDomainSampleQueryLayoutOfCode_ok`: `OutOfDomainSampleQueryLayout.OK`, if `rc` is one to one. `outOfDomainSampleQueryLayoutOfCode_law`: the law is the hypothesis, read.
 `outOfDomainSampleQueryLayoutOfCodeAtFullSize`, `outOfDomainSampleQueryLayoutOfCodeAtSmallSize`: at `S.lhr`, for any five sub-protocols S over the configuration and any
   number K of digests that is at least the number that the seeds' draws need: the seed is
   `recSeedK` (OnBytes/Flat/RecordSeed.lean); a record is read as it stands.
 `outOfDomainSampleQueryLayoutOfCodeAtFullSize_ok`, `outOfDomainSampleQueryLayoutOfCodeAtFullSize_law`; `outOfDomainSampleQueryLayoutOfCodeAtSmallSize_ok`, `outOfDomainSampleQueryLayoutOfCodeAtSmallSize_law`: nothing is assumed; the law at
   2^-128.

Limits: those of OnBytes/Flat/RecordCode.lean and OnBytes/Flat/EntryRecord.lean. `cfg` and
`shape` are not laid here: that they are what a program's name of a table holds is not said. That a
program hashes the list `codeP` is not said.

-/
import Johnson.TypedOracleCompiler.RecCompile.Seeds
import OnBytes.Flat.RecordCode
import OnBytes.Flat.RecordSeed
import Hiop.RecBuild

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace TypedOracleCompiler.Compile.Batch.Cms
open _root_.Compile TypedOracleCompiler.Iop Rom Prob Hiop
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open OnBytes.Slice OnBytes.Flat

section
variable {I X : Type} (L : HolographicProtocol I X) (Bd : Type) (aT : RoundSplits L.offline.shape) (aL : RoundSplits L.link.shape)
  {K v lg s : ℕ} (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier L Bd aT aL) t) (annOf (typedOracleCarrier L Bd aT aL) t))
  (num : ℕ → Plains L.onlineBatch.loc.shape → Bool)
  (seed : (Fin K → Dig 256) → L.OutOfDomainSeed) (rc : L.Rec → RecP NZ v lg s) (decS : DecidableEq L.OutOfDomainSeed)

/-- The wire of the record, its code written. -/
def outOfDomainSampleQueryLayoutOfCode : OutOfDomainSampleQueryLayout 256 K L Bd aT aL where
  t := t
  cfg := cfg
  shape := shape
  pl0 := pl0
  pl1 := pl1
  seed := seed
  code := fun r => codeP (fun β : NZ => β.val) (rc r)
  num := num
  decS := decS

/-- No two records are written alike, if no two are read alike; all are written with one number of
digests. -/
theorem outOfDomainSampleQueryLayoutOfCode_ok (h : Function.Injective rc) :
    (outOfDomainSampleQueryLayoutOfCode L Bd aT aL t cfg shape pl0 pl1 num seed rc decS).OK :=
  ⟨(codeP_inj _ Subtype.val_injective).comp h,
    fun r r' => (codeP_length _ (rc r)).trans (codeP_length _ (rc r')).symm⟩

/-- The seed's law, read. -/
theorem outOfDomainSampleQueryLayoutOfCode_law (κ : ℝ≥0∞)
    (h : ∀ y, pr (unif (Fin K → Dig 256)) {a | L.hasCollisionAt y (seed a)} ≤ κ) :
    (outOfDomainSampleQueryLayoutOfCode L Bd aT aL t cfg shape pl0 pl1 num seed rc decS).Law κ := h

end

/-! ## At the two sizes -/

section
variable {X : Type} {A : (frS.toDecR frZ 402653181).Claims X}
  {R : (frS.toDecR frZ 402653181).RelationsAndEncoding A}
  (S : SubsR (DecR.configurationOfStoredTable A R)) (Bd : Type) (aT : RoundSplits S.lhr.offline.shape)
  (aL : RoundSplits S.lhr.link.shape) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier S.lhr Bd aT aL) t) (annOf (typedOracleCarrier S.lhr Bd aT aL) t))
  (num : ℕ → Plains S.lhr.onlineBatch.loc.shape → Bool)
  (K : ℕ) (h : (seedBS recLg recS).b ≤ K) (decS : DecidableEq S.lhr.OutOfDomainSeed)

/-- The wire of the record at the full size. -/
def outOfDomainSampleQueryLayoutOfCodeAtFullSize : OutOfDomainSampleQueryLayout 256 K S.lhr Bd aT aL :=
  outOfDomainSampleQueryLayoutOfCode S.lhr Bd aT aL (v := frS.P.v) (lg := 29) (s := 1) t cfg shape pl0 pl1 num
    (recSeedK recT recLg recS K h) id decS

/-- No two records are written alike; all with one number of digests. -/
theorem outOfDomainSampleQueryLayoutOfCodeAtFullSize_ok : (outOfDomainSampleQueryLayoutOfCodeAtFullSize S Bd aT aL t cfg shape pl0 pl1 num K h decS).OK :=
  outOfDomainSampleQueryLayoutOfCode_ok _ _ _ _ _ _ _ _ _ _ _ _ _ Function.injective_id

/-- The seed's law at 2^-128. -/
theorem outOfDomainSampleQueryLayoutOfCodeAtFullSize_law :
    (outOfDomainSampleQueryLayoutOfCodeAtFullSize S Bd aT aL t cfg shape pl0 pl1 num K h decS).Law (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entryFull_seedLawK A R K h y

end

section
variable {X : Type} {A : (srS.toDecR srZ 524285).Claims X} {R : (srS.toDecR srZ 524285).RelationsAndEncoding A}
  (S : SubsR (DecR.configurationOfStoredTable A R)) (Bd : Type) (aT : RoundSplits S.lhr.offline.shape)
  (aL : RoundSplits S.lhr.link.shape) (t : Tag) (cfg : List (Dig 256)) (shape : Bits)
  (pl0 pl1 : PlainPart (shapeOf (typedOracleCarrier S.lhr Bd aT aL) t) (annOf (typedOracleCarrier S.lhr Bd aT aL) t))
  (num : ℕ → Plains S.lhr.onlineBatch.loc.shape → Bool)
  (K : ℕ) (h : (seedBS 19 1).b ≤ K) (decS : DecidableEq S.lhr.OutOfDomainSeed)

/-- The wire of the record at the small example. -/
def outOfDomainSampleQueryLayoutOfCodeAtSmallSize : OutOfDomainSampleQueryLayout 256 K S.lhr Bd aT aL :=
  outOfDomainSampleQueryLayoutOfCode S.lhr Bd aT aL (v := srS.P.v) (lg := 19) (s := 1) t cfg shape pl0 pl1 num
    (recSeedK srT 19 1 K h) id decS

/-- No two records are written alike; all with one number of digests. -/
theorem outOfDomainSampleQueryLayoutOfCodeAtSmallSize_ok : (outOfDomainSampleQueryLayoutOfCodeAtSmallSize S Bd aT aL t cfg shape pl0 pl1 num K h decS).OK :=
  outOfDomainSampleQueryLayoutOfCode_ok _ _ _ _ _ _ _ _ _ _ _ _ _ Function.injective_id

/-- The seed's law at 2^-128. -/
theorem outOfDomainSampleQueryLayoutOfCodeAtSmallSize_law :
    (outOfDomainSampleQueryLayoutOfCodeAtSmallSize S Bd aT aL t cfg shape pl0 pl1 num K h decS).Law (((2 : ℝ≥0∞)⁻¹) ^ 128) :=
  outOfDomainSampleQueryLayoutOfCode_law _ _ _ _ _ _ _ _ _ _ _ _ _ _ fun y => entrySmall_seedLawK A R K h y

end

end TypedOracleCompiler.Compile.Batch.Cms

#print axioms TypedOracleCompiler.Compile.Batch.Cms.outOfDomainSampleQueryLayoutOfCode_ok
#print axioms TypedOracleCompiler.Compile.Batch.Cms.outOfDomainSampleQueryLayoutOfCodeAtFullSize_ok
#print axioms TypedOracleCompiler.Compile.Batch.Cms.outOfDomainSampleQueryLayoutOfCodeAtFullSize_law
#print axioms TypedOracleCompiler.Compile.Batch.Cms.outOfDomainSampleQueryLayoutOfCodeAtSmallSize_ok
#print axioms TypedOracleCompiler.Compile.Batch.Cms.outOfDomainSampleQueryLayoutOfCodeAtSmallSize_law
