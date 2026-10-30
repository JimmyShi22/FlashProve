-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StepL.lean: the step from `argBKE` (Compile/Batch/StarKE.lean) to the scheme with the
lazy prover, as a `Carry` (Rom/Carry.lean), with lemmas on its committer and its cache. (Words of
this library: lean/GLOSSARY.md.)

`argPL` (Compile/Batch/SeedLazyDefs.lean): isk = (i, seed, for each copy the root and one level ℓ of
its Merkle tree); for a batch the prover recomputes, of the sampled copy, the randomness of the
encoding and the blocks of 2^ℓ leaves that hold a shown position. By Compile/Batch/SeedLazy.lean it
has the output distributions of `argP` (Compile/Batch/StarS.lean), so the three properties carry
over to it, with the same bounds (`isZKCPArgWith_lazyGr`).

  `carryL`   whatever extractor, simulator and bounds (α, ε, ζ) `argBKE` has, `argPL` has the same
             extractor and simulator with α + b, ε, ζ(t, n) + b + t / (number of seeds): the added
             error terms of `carryS` (Compile/Batch/StepS.lean), and nothing for the cache and the
             lazy prover

Difference from the implementation that this step removes: the difference in what is stored (Lean:
whole trees; the implementation: one level of each copy's tree, columns recomputed). After this step
there is none in what is stored for a copy and in which leaves of its tree are recomputed. What
remains of it:
* the implementation also stores one level of the tree of the first encoding (its "anchor"), which
  only its committer reads; Lean's cache has no entry for it;
* Lean derives a block once for each read position in it, and again for each slot that reads it; the
  implementation makes a shown column once;
* after a stored value that does not match, the implementation also ends the service; Lean's P is
  one call for one batch;
* formats: how the stored digests are written to files.

With proof-of-work bits. `carryLGr`: the same statement under `W.OKG` (Iop/BatchWire.lean). `carryS`
requires of the wire record only that there are 2^depthReq slots, so it holds for a wire record with
proof-of-work bits as well.

Hypotheses. `W.OK`, or `W.OKG` (used: `slots`, `fits`, `extB`), and ℓ ≤ W.depth, beside those of
`carryS` (σ.o = `OracleName.other`, σ.bias bk.w = 0, b bounds the bias along every path of C).

Notation: `argBKE`: the compiled scheme with the entries in the verification key and no query or
tree for an empty slot (Compile/Batch/StarKE.lean); α, ε, ζ: arguments of `IsZKCPArgWith`
(ZKCP/Gen.lean), whose three fields are the three properties: α stands in `completeness`, ε in
`indexBinding`, ζ in `indexPrivacy`; in ζ(t, n), t bounds the queries of `Vt ivk`, n counts batches
(`PrivacyFor`, ZKCP/Gen.lean); `bk`: a `CoinPlan`: how a uniform sample is made from small ones
(Rom/Blocks.lean); `σ`: a `SeedOracle`: an auxiliary oracle, used as a source of coins
(Rom/SpecDerive.lean); `no`: a function of the copy's number and the batch: "no proof" (the head of
Compile/Batch/SeedCache.lean).

Limits: what the heads of Compile/Batch/StepS.lean and Compile/Batch/SeedLazy.lean list as not said
is not said here either. No statement on running time, memory (but for the number of digests in the
cache: `digests_cacheL`) or numbers of queries. A `Carry` is an implication: it says nothing unless
something is known about `argBKE`. Perfect completeness is not carried over by a `Carry`; it carries
over from `argP` to `argPL` by `isZKCPArgWith_lazy` (Compile/Batch/SeedLazy.lean), which is an
equivalence with the same bounds.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedLazy
import Compile.Batch.StepS

noncomputable section

open Rom Iop ZKCP
open scoped ENNReal

namespace Compile.Batch
namespace Seed

open Compile.Seed (blocksStd)

variable {I X PP : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)

/-- The step (S) of Compile/Batch/StepS.lean and the lazy prover (hypotheses below): the committer's
coins come from one seed; the prover keeps one level of each copy's tree and recomputes, of the
sampled copy, the randomness of the encoding and the blocks of 2^ℓ leaves that hold a position that
it shows. The rounds may have proof-of-work bits. -/
theorem carryLGr (R : Gen.RelPair I X Unit PP) (B : ℕ) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (b : ℝ≥0∞) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (hW : W.OKG)
    (hℓ : ℓ ≤ W.depth) (hσ : σ.o = OracleName.other) (hw : σ.bias bk.w = 0)
    (hb : ∀ i, (C W WP p i).pathBiasB bk ≤ b) :
    Carry R B (argBKE W WP p) (argPL W WP p bk σ ℓ no) b
      (fun t _ => b + (t : ℝ≥0∞) / (σ.sd + 1 : ℕ)) := fun E Sim α ε ζ h =>
  (isZKCPArgWith_lazyGr WP p bk σ hW hℓ no R B E Sim _ _ _).1
    (carryS W WP p R B bk σ b hW.slots hσ hw hb E Sim α ε ζ h)

/-- `carryLGr` for a wire record without proof-of-work bits (`W.OK`) -/
theorem carryL (R : Gen.RelPair I X Unit PP) (B : ℕ) (bk : CoinPlan)
    (σ : SeedOracle (spec lam W.K L)) (b : ℝ≥0∞) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (hW : W.OK) (hℓ : ℓ ≤ W.depth)
    (hσ : σ.o = OracleName.other) (hw : σ.bias bk.w = 0) (hb : ∀ i, (C W WP p i).pathBiasB bk ≤ b) :
    Carry R B (argBKE W WP p) (argPL W WP p bk σ ℓ no) b
      (fun t _ => b + (t : ℝ≥0∞) / (σ.sd + 1 : ℕ)) :=
  carryLGr W WP p R B bk σ b ℓ no hW.toG hℓ hσ hw hb




/-- the committer of `argPL` is that of the scheme with the stored level (`argCache`,
Compile/Batch/SeedCache.lean) -/
theorem argPL_C (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (own : Bool) (ℓ : ℕ)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) :
    (argPL W WP p bk σ ℓ no).C = (argCache WP p bk σ (faceKE W WP p) own ℓ no).C := rfl

/-- For ℓ ≤ W.depth, the size of the cache that the committer returns: an entry for each of the M +
1 copies; each entry is a root and 2 ^ (depth - ℓ) digests. -/
theorem size_cacheL (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (i : I)
    (g : Fam (spec lam W.K L)) (key : IVKK lam L × ((I × Fin (σ.sd + 1)) × Ca lam))
    (hkey : key ∈ (((argPL W WP p bk σ ℓ no).C i).runEager g).support) :
    key.2.2.length = p.M + 1 ∧ ∀ e ∈ key.2.2, e.2.length = 2 ^ (W.depth - ℓ) :=
  size_cache WP p bk σ (faceKE W WP p) true hℓ no i g key hkey

/-- For ℓ ≤ W.depth, the number of digests kept: (M + 1) (1 + 2 ^ (depth - ℓ)). -/
theorem digests_cacheL (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) {ℓ : ℕ} (hℓ : ℓ ≤ W.depth)
    (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b) (i : I)
    (g : Fam (spec lam W.K L)) (key : IVKK lam L × ((I × Fin (σ.sd + 1)) × Ca lam))
    (hkey : key ∈ (((argPL W WP p bk σ ℓ no).C i).runEager g).support) :
    (key.2.2.map fun e => 1 + e.2.length).sum = (p.M + 1) * (1 + 2 ^ (W.depth - ℓ)) :=
  digests_cache WP p bk σ (faceKE W WP p) true hℓ no i g key hkey

end Seed
end Compile.Batch
