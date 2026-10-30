-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/TieSeedPort.lean: what ties the seed's test of the compiled verifier with records, two
nested typed queries (`outOfDomainSeedIs`, Johnson/TypedOracleCompiler/RecCompile/Seeds.lean), to the seeds that the program
`verify-on-bytes` draws (OnBytes/K/SeedBytes.lean).

A definition of a property; theorems.
Main names:
  `ansAt W S g q`: the answer of typed oracle functions at a chain query under the wire's tag.
  `seedIs_det`: the run of `outOfDomainSeedIs` at typed oracle functions g says yes at s exactly if s is the
    wire's seed of the second answer's digests.
  `SeedSpelt W S g rest`: g answers the two queries as the format's oracle answers at the two
    written strings: the chain value of the first answer at the root cm is the oracle's answer at
    `seedFirst` of the name "cm's bytes, then rest"; digest k of the second answer, at a chain value
    v of 256 bits, is its answer at `seedStr` of v's bytes and k + 1.
  `seedIs_port`: under `SeedSpelt`, if the wire's seed is `toSeed` of the program's own draws on the
    digests (`seedsOfDigs`), and the program fetches at most K blocks: the run of `outOfDomainSeedIs` at g says
    yes at `toSeed` of `seedsAtName` at that name. By `recordSeeds_blocks` that is `toSeed` of what
    the program's `recordSeeds` returns at the name.

Limits: `SeedSpelt` is a hypothesis on g here. That `rest` is what the first query's head spells
(`OutOfDomainSampleQueryLayout.cfg`, `OutOfDomainSampleQueryLayout.shape`) is not asked: it is a matter of who makes g. Nothing on how seeds are
distributed; nothing on soundness (index binding included), opening-form binding, no two openings,
correctness of extraction or whatever else names a committer or a prover.

-/
import OnBytes.K.SeedBytes
import Johnson.TypedOracleCompiler.RecCompile.Seeds

set_option autoImplicit false

namespace OnBytes.K

open _root_.Compile TypedOracleCompiler.Iop Rom TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run (bytesToDig digToBytes bitsToBytes)

variable {I X : Type} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape} {aL : RoundSplits L.link.shape}
  (W : QueryLayout 256 (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout 256 W.K L Bd aT aL)

/-- The answer of typed oracle functions at a chain query under the wire's tag. -/
def ansAt (g : Fam (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL)))
    (q : FbIn 256 (typedOracleCarrier L Bd aT aL) S.t) : FsAns 256 W.K :=
  g (OracleName.fb S.t) q

/-- The run at typed oracle functions, written out. -/
theorem seedIs_det (g : Fam (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL))) (cm : Dig 256) (s : L.OutOfDomainSeed) :
    (outOfDomainSeedIs W S cm s).det g = true ↔
      S.seed (ansAt W S g (seedQ1 W S (link (ansAt W S g (seedQ0 W S cm))))).1 = s := by
  have e : ∀ (p : Prop) (i : Decidable p), @decide p i = true ↔ p :=
    fun p i => @decide_eq_true_iff p i
  unfold outOfDomainSeedIs
  simp only [OComp.det_bind]
  exact e _ _

/-- The typed oracle functions answer the two queries as the format's oracle answers at the two
written strings. rest: what stands behind the root in a table's name. -/
structure SeedSpelt (g : Fam (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL))) (rest : ByteArray) : Prop where
  /-- the chain value of the first answer -/
  first : ∀ cm, (ansAt W S g (seedQ0 W S cm)).2 =
    bytesToDig (Fmt.oracle (seedFirst (digToBytes cm ++ rest)))
  /-- the digests of the second answer -/
  round : ∀ v : Bits, v.length = 256 → ∀ k, (ansAt W S g (seedQ1 W S v)).1 k =
    bytesToDig (Fmt.oracle (seedStr (bitsToBytes v) (k.val + 1)))

/-- **The run says yes at the program's seeds.** -/
theorem seedIs_port (g : Fam (typedOracleFamily 256 W.K (typedOracleCarrier L Bd aT aL))) (rest : ByteArray)
    (H : SeedSpelt W S g rest) (f : Fmt.Fld) (bits count : ℕ)
    (toSeed : List (List E × E) → L.OutOfDomainSeed) (hK : nBlocks bits count ≤ W.K)
    (hs : ∀ a, S.seed a = toSeed (seedsOfDigs f bits count a)) (cm : Dig 256) :
    (outOfDomainSeedIs W S cm (toSeed (seedsAtName f (digToBytes cm ++ rest) bits count))).det g = true := by
  have ha : (ansAt W S g (seedQ1 W S (link (ansAt W S g (seedQ0 W S cm))))).1 =
      seedDigs (digToBytes cm ++ rest) W.K := by
    funext k
    rw [H.round _ (by show (List.ofFn _).length = 256; exact List.length_ofFn)]
    show bytesToDig (Fmt.oracle (seedStr (digToBytes (ansAt W S g (seedQ0 W S cm)).2)
      (k.val + 1))) = _
    rw [H.first, _root_.Run.TieTree.dig_bytes _ (Fmt.size_oracle _)]
    rfl
  rw [seedIs_det, hs, ha, seedsOfDigs_seedDigs f _ bits count W.K hK]

end OnBytes.K
