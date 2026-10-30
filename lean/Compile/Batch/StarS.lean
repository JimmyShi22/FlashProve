-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/StarS.lean: the compiled scheme with the entries in the verification key, no query and
no tree for an empty slot, and isk = (i, seed). Definitions only, with three lemmas that unfold them
(`argP_C`, `argP_P`, `argP_V`). (Words of this library: lean/GLOSSARY.md.)

`argP`: the transformation of Compile/Batch/SeedStar.lean applied to `argBKE`
(Compile/Batch/StarKE.lean), through its record `faceKE` (Compile/Batch/SeedFace.lean):
* C samples one seed, runs the committer of `argBKE` with every sample made from small ones (bk) and
  these derived from the seed through the oracle of σ, publishes ivk, and keeps (i, seed). (bk: a
  `CoinPlan`: how a uniform sample is made from small ones, Rom/Blocks.lean. σ: a `SeedOracle`: an
  auxiliary oracle, used as a source of coins, Rom/SpecDerive.lean.)
* P, for each batch:
  - a uniform copy with a fresh coin;
  - the `Node` of that copy, derived again under the seed;
  - a sampled placement (uniform if `WP.perm` has `Enum.OK`, Iop/Wire.lean);
  - one execution of `proveBU`, with fresh coins, every proof-of-work attempt being a query to the
    Fiat-Shamir oracle of its protocol (Compile/Batch/RealQ.lean: eraseR c vs = realQ (erase c vs):
    fb t is queried in place of every ghost name fbw t k);
  - a proof is (number of the copy, piB).
* V is the verifier of `argBK`.

Differences from the implementation that it removes: fresh coins of C kept in isk; whole `Node`s
kept in isk. Limits and the added error terms: the headers of Compile/Batch/SeedStar.lean and
Compile/Batch/StepS.lean.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Compile.Batch.SeedFace

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X} (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
  (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L))

/-- The scheme `argSeed` at the record `faceKE`. -/
def argP : Gen.Arg (spec lam W.K L) I X Unit (IVKK lam L) (I × Fin (σ.sd + 1)) (PrfK lam L) :=
  Seed.argSeed WP p (Seed.faceKE W WP p) bk σ

theorem argP_C (i : I) :
    (argP W WP p bk σ).C i =
      .sample σ.sd fun s =>
        ((((C W WP p i).bind fun o => .pure ((o.1, linksOf (keyOf o.2.1)), o.2)).blocks bk).derive
              σ s 0).bind
            fun out => .pure (out.1, (i, s)) := rfl

theorem argP_P (k : I × Fin (σ.sd + 1)) (b : List (X × Unit)) : (argP W WP p bk σ).P k b =
    .sample p.M fun j =>
    (((erase (nodeP' W WP p k.1) []).blocks bk).derive
        σ k.2 (Seed.off W WP p bk.m j.val)).bind fun a =>
    (eraseR (Seed.batOf WP (Seed.runBU W WP p) k.1 j.val (some a.1) b) a.2).bind
      fun o => .pure o.1 := rfl

theorem argP_V : (argP W WP p bk σ).V = (argBK W WP p).V := rfl

end Compile.Batch
