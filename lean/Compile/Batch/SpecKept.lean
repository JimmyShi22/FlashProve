-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/SpecKept.lean: a bound, on every path, on the honest Fiat-Shamir queries without the
failed proof-of-work attempts that are not the last. Definitions and statements. Nothing is proved
here. The proofs: Compile/Batch/Kept.lean. (Words of this library: lean/GLOSSARY.md.)

Why. (1) A step on the way to one hash function that makes a state for a Fiat-Shamir query
(Rom/StateFirst.lean) has added error terms in which the number of such queries of the honest
committer and prover occurs.
(2) After a Fiat-Shamir answer is split after its first hash block (Rom/SpecCut.lean;
Compile/Batch/CutFit.lean) a state is made only where the rest of an answer is asked for: not for a
failed attempt that is not the last.
(3) The sums that the library has for the weights 0 of a failed attempt that is not the last and 1
of any other (Compile/Batch/OneCallCostPL.lean: cPLW .. 0 (fun _ _ => 1)) also count trees, openings
and coins, because their parts without a search come from the counts for the non-adaptive choice of
hash blocks.

  `wKept`, `kPU`, `kProve1`, `kCB`   see their doc comments
  `kSlot`, `kShared`   by the recursion of `cSlotW`, `cSharedW` (Compile/Batch/OneCallCostR.lean),
                       with 1 for a search and nothing else. They depend on the kinds of the rounds
                       only: not on the wire record

The statements, all for the worst case over the oracle and the coins (Rom/SpecOverOneA.lean:
`CostBoundV`: the weight of a query may depend on its answer).
  `Spec.keptP`   if `W.OKG` and σ.o = `OracleName.other`: for every key and batch b the lazy prover of
                 `prunedK W p (argPL ..)` has weight at most `kPU L b.length`. No tree, no opening,
                 no coin, no failed attempt but a last one is counted; no hypothesis on the key or
                 on what a verifier reads (beside `ProtocolQueryLayout.OKG.opens`, a part of `W.OKG`).
                 `Spec.keptC`: the same for its committer: at most `kCB L p`

Limits. Nothing about V. Nothing about the split or about states: that, under the hypotheses there,
`wKept` is at least the weight in which these steps count is in Compile/Batch/KeptCut.lean. No
numeral.
-/
import Compile.Batch.SpecOneCall
import Compile.Batch.SeedLazyDefs

noncomputable section

namespace Compile.Batch
open Iop Rom ZKCP
open Compile.Batch.Need (PhK)

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- The weight: at `fb t`, 0 for a failed attempt that is not the last, else 1; at every other
oracle 0. -/
def wKept (W : QueryLayout lam L) : (o : OracleName) → domOf lam L o → rngOf lam W.K o → ℕ
  | .fb t, q, r => if failsAt W t q r.1 = true then 0 else 1
  | _, _, _ => 0

/-- the searches of one slot with a request, in the rounds that are left: one for each local round
-/
def kSlot : (s : Shape) → RoundSplits s → PhK → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), ph =>
      match a.kind, ph with
      | .lo, ph => 1 + kSlot s A ph.afterLo
      | .sh, .loc => kSlot s A .shr
      | .sh, ph => kSlot s A ph

/-- the shared searches: one for the joining round and for each of the shared rounds after it up to
the next local round -/
def kShared : (s : Shape) → RoundSplits s → PhK → ℕ
  | [], _, _ => 0
  | _ :: s, (a, A), ph =>
      match a.kind, ph with
      | .lo, ph => kShared s A ph.afterLo
      | .sh, .loc => 1 + kShared s A .shr
      | .sh, .shr => 1 + kShared s A .shr
      | .sh, ph => kShared s A ph

/-- one execution with one slot -/
def kProve1 {Y : Type} {E : ExtSpec} (Q : BatchInteractiveOracleProof Y E) : ℕ :=
  kShared Q.loc.shape Q.ann .first + kSlot Q.loc.shape Q.ann .first

/-- one batch with n requests -/
def kPU (L : BatchProtocol I X) (n : ℕ) : ℕ :=
  kShared L.onlineBatch.loc.shape L.onlineBatch.ann .first + n * kSlot L.onlineBatch.loc.shape L.onlineBatch.ann .first

/-- the committer -/
def kCB (L : BatchProtocol I X) (p : Params) : ℕ :=
  kProve1 (BatchInteractiveOracleProof.ofProto L.offline) + (p.M + 1) * kProve1 (BatchInteractiveOracleProof.ofProto L.link)

namespace Spec

/-- The lazy prover (hypotheses below). -/
def keptP : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ)
      (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b),
    W.OKG → σ.o = OracleName.other →
    ∀ kc b,
      ((prunedK W p (Seed.argPL W WP p bk σ ℓ no)).P kc b).CostBoundV (wKept W) (kPU L b.length)

/-- The committer (hypotheses below). -/
def keptC : Prop :=
  ∀ (I X : Type) (lam : ℕ) (L : BatchProtocol I X) (W : QueryLayout lam L) (WP : WireBP L) (p : Params)
      (bk : CoinPlan) (σ : SeedOracle (spec lam W.K L)) (ℓ : ℕ)
      (no : (j : ℕ) → (b : List (X × Unit)) → Gen.Slots (PrfK lam L) b),
    W.OKG → σ.o = OracleName.other →
    ∀ i, ((prunedK W p (Seed.argPL W WP p bk σ ℓ no)).C i).CostBoundV (wKept W) (kCB L p)

/-- Sanity statement: at most one for each round, in the shared chain and in each slot. -/
def keptLe : Prop :=
  ∀ (I X : Type) (L : BatchProtocol I X) (p : Params) (n : ℕ),
    kPU L n ≤ (n + 1) * L.onlineBatch.loc.shape.length ∧
    kCB L p ≤ L.offline.shape.length + (p.M + 1) * L.link.shape.length

end Spec

end Compile.Batch
