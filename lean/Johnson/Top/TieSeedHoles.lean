-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieSeedHoles.lean: the seed's test of the compiled verifier with records (`outOfDomainSeedIs`,
Johnson/TypedOracleCompiler/RecCompile/Seeds.lean), run at typed oracle functions g, says yes at a table's root and
at the typed form of the seeds that the program `verify-on-bytes` draws at the table's name.

This is what the two seeds' fields of the tie for the entry file ask (`EntryPart.seed0`,
`EntryPart.seed1`, OnBytes/K/Parts.lean), at a reading of a table as a record whose seed is the
typed form of the program's own seeds.

Main names:
  `SeedsOK W S g f cfg sh toSeed`: what is asked of the wires W and S and of g, at a field f, a
    digest cfg of the public files and a shape sh of the tables: (spelt) g answers the two typed
    queries as the format's oracle answers at the two written strings, with cfg and sh's six words
    behind the root in a table's name; (wire) the wire's seed is `toSeed` of the program's own draws
    on the digests, in f, at sh; (room) an answer has digests enough.
  `seed_name`: the test says yes at the root of a table with a root of 32 bytes and at `toSeed` of
    `seedsAtName` at the table's name (OnBytes/K/SeedBytes.lean).
  `seed_program`: so it says yes at `toSeed l`, if the program's own `recordSeeds` returns l at the
    table's name; for a digest of 32 bytes.

Limits: `SeedsOK` is a hypothesis here. (spelt) is a theorem at a coding that takes the seeds' code
in: Johnson/Top/TieSeedSpelt.lean. (wire) and (room) are matters of how the wire is written. Nothing
on how seeds are distributed; nothing on soundness (index binding included), opening-form binding,
no two openings, correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.K.SeedPort
import Johnson.Top.TieSeedPort

set_option autoImplicit false

namespace OnBytes.K

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes bitsToBytes)

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)

/-- What is asked of the wires and of the typed oracle functions. -/
structure SeedsOK (g : Fam (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL))) (f : Fmt.Fld) (cfg : ByteArray)
    (sh : Params.IndexShape) (toSeed : List (List E × E) → L.OutOfDomainSeed) : Prop where
  /-- the typed oracle functions answer the two queries as the format's oracle answers at the two
  written strings -/
  spelt : SeedSpelt W S g (restOf sh cfg)
  /-- the wire's seed is the typed form of the program's own draws on the first digests -/
  wire : ∀ a, S.seed a = toSeed (seedsOfDigs f sh.cubeBits sh.answers a)
  /-- the digests of an answer are enough -/
  room : nBlocks sh.cubeBits sh.answers ≤ W.K

variable {W S} {g : Fam (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL))} {f : Fmt.Fld} {cfg : ByteArray}
  {sh : Params.IndexShape} {toSeed : List (List E × E) → L.OutOfDomainSeed}

/-- The test says yes at a table's root and at the typed form of the draws at the table's name. -/
theorem seed_name (H : SeedsOK W S g f cfg sh toSeed) (t : Params.TableName)
    (ht : t.root.size = 32) :
    (outOfDomainSeedIs W S (bytesToDig t.root)
      (toSeed (seedsAtName f (Key.nameOf sh cfg t) sh.cubeBits sh.answers))).det g = true := by
  have h := seedIs_port W S g _ H.spelt f _ _ toSeed H.room H.wire (bytesToDig t.root)
  rw [_root_.Run.TieTree.dig_bytes t.root ht, ← nameOf_rest] at h
  exact h

/-- **The test says yes at the typed form of the program's own seeds.** -/
theorem seed_program (H : SeedsOK W S g f cfg sh toSeed) (t : Params.TableName)
    (ht : t.root.size = 32) (hc : cfg.size = 32) (l : List (List E × E))
    (hl : recordSeeds f (Key.nameOf sh cfg t) sh.cubeBits sh.answers = some l) :
    (outOfDomainSeedIs W S (bytesToDig t.root) (toSeed l)).det g = true := by
  have hn : (Key.nameOf sh cfg t).size + 56 ≤ 2 ^ 32 - 144 := by
    rw [size_nameOf, ht, hc]
    decide
  rw [recordSeeds_blocks f _ _ _ hn] at hl
  rw [← Option.some.inj hl]
  exact seed_name H t ht

end OnBytes.K
