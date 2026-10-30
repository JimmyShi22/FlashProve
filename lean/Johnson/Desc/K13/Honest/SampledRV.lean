-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Honest/SampledRV.lean: WHAT A LIST OF ROUNDS SAMPLED, AS THE PROGRAMS' ELEMENTS;
and that neither it nor `mergeDraws` (PileDefs.lean of this folder) reads a round's digest. One
definition, and statements with their proofs. It stands on PileDefs.lean and the library alone.

A sub-protocol's step hands its decision the rounds without their digests (`noDigest`, `Block.step`:
Johnson/Desc/Block.lean). A law that is asked of the fold speaks of the rounds as they are. Kin in
the library: `noDigest_elems` (Johnson/Desc/Sound/PieceYes.lean), `flatOf_noDigest`, `zip_noDigest`
(Johnson/Top/H0/MergeLaw/Out.lean).
Main names:
  `sampledRV rs`: for each round, the elements that it sampled. `sampledRV_noDigest`,
    `sampledRV_drop`: it does not read the digest; it goes through `drop`.
  `mergeDraws_noDigest`: **`mergeDraws` at the challenges of rounds without their digests is
    `mergeDraws` at the challenges of the rounds as they are.**

What is not claimed. Nothing on soundness, completeness or hiding.

-/
import Johnson.Desc.K13.Honest.PileDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Honest
open OnBytes
open VerifiableInference.Desc (noDigest)

/-- For each round, the elements that it sampled. -/
def sampledRV (rs : List Fmt.RoundView) : List (List E) := rs.map fun r => r.drawn.elems.map E.ofTriple

/-- The step's own erasure of a round's digest leaves them. -/
theorem sampledRV_noDigest (rs : List Fmt.RoundView) : sampledRV (rs.map noDigest) = sampledRV rs := by
  unfold sampledRV
  rw [List.map_map]
  rfl

/-- It goes through `drop`. -/
theorem sampledRV_drop (rs : List Fmt.RoundView) (n : Nat) :
    sampledRV (rs.drop n) = (sampledRV rs).drop n := by
  unfold sampledRV
  rw [List.map_drop]

/-- **`mergeDraws` does not read a round's digest.** -/
theorem mergeDraws_noDigest (lk : Nat) (l : List Fmt.RoundView) :
    mergeDraws lk ((l.map noDigest).map (·.drawn)) = mergeDraws lk (l.map (·.drawn)) := by
  unfold mergeDraws
  simp only [List.length_map, List.all_map, List.flatMap_map, List.map_map]
  rfl

end VerifiableInference.Desc.K13.Honest

#print axioms VerifiableInference.Desc.K13.Honest.sampledRV_noDigest
#print axioms VerifiableInference.Desc.K13.Honest.sampledRV_drop
#print axioms VerifiableInference.Desc.K13.Honest.mergeDraws_noDigest
