-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/Counts.lean: upper bounds on the numbers of oracle queries of the honest side of the
compiled scheme (setup and n batches). Definitions (the oracles: `OracleName`, Compile/Batch/Oracles.lean;
words of this library: lean/GLOSSARY.md).

All numbers are explicit, and coarse:
* in every round both trees are counted (the shared one, and one for each slot), whatever the kind
  of the round and whether or not the component has a tree (`has0`, `hasJ`, Iop/BatchWire.lean): a
  component without a tree is counted with the 2^d of its depth field;
* a tree of depth d counts 2^d leaves and 2^d inner nodes;
* ordinary and marked queries to an oracle are counted together, so that m (t + e + m) ≤ c (t + c),
  where e is the number of ordinary and m of marked queries, t is the number of the adversary's
  queries and c the count below (for `Disc.Spec.sumB`, Compile/Batch/SpecDiscipline.lean).

Rounds with proof-of-work bits: `xFbG` counts every attempt, `more` + 1 for each search.

Notation: `leaf`, `node`: the Merkle trees over prover messages and over encodings of the index;
`rleaf`, `rnode`: the request tree, a Merkle tree over the slots of one batch; `fb t`: Fiat-Shamir
for the protocol t (the three oracles: t is `test`, `link` or `onl`: `Tag`, Compile/Oracles.lean);
`g t`: in the joining round (the first shared round after the local ones), the slot value;
`fbw t k`: the analysis's oracles: proof-of-work attempt k + 1 is written as a query to `fbw t k`
(all: the head of Compile/Batch/Oracles.lean).

Limits: this file does not define the hash terms of the compiled scheme. The hash terms
(`Spec.sumB`, Compile/Batch/SpecDiscipline.lean) include a term for the node oracle (the inner nodes
of the trees over prover messages are marked queries, Compile/Batch/TokTree.lean).
-/
import Compile.Batch.Star
import Compile.Spec

noncomputable section

namespace Compile.Batch
open Iop
open scoped ENNReal

variable {I X : Type} {lam : ℕ} {L : BatchProtocol I X}

/-- leaves (and, as a bound, inner nodes) of all trees of one execution with Ns slots -/
def cTrees {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ → ℕ
  | [], _, _, _ => 0
  | _ :: s, (_, A), (w, W), Ns => Ns * 2 ^ w.depthJ + 2 ^ w.depth0 + cTrees s A W Ns

variable (W : QueryLayout lam L) (p : Params)

/-- queries to the leaf oracle, and likewise to the node oracle: the M + 2 trees over encoded
indices, Test, the M + 1 Links, n batches of maxBatchSize slots -/
def xTree (n : ℕ) : ℕ :=
  (p.leaves + 1) * 2 ^ W.depth + cTrees L.offline.shape _ W.T.sh 1 +
    p.leaves * cTrees L.link.shape _ W.Lk.sh 1 + n * cTrees L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh L.maxBatchSize

/-- Fiat-Shamir queries, to the three oracles together: in each round at most one for each slot and
one shared -/
def xFb (n : ℕ) : ℕ :=
  2 * L.offline.shape.length + p.leaves * (2 * L.link.shape.length) +
    n * ((L.maxBatchSize + 1) * L.onlineBatch.loc.shape.length)

/-- queries to g; likewise to the leaf oracle and to the node oracle of request trees -/
def xReq (L : BatchProtocol I X) (n : ℕ) : ℕ := n * L.maxBatchSize

/-! ## Rounds with proof-of-work bits (Iop/BatchWire.lean: GrW): every attempt is counted, at the
worst case -/

variable {W p}

/-- at most this many attempts for one Fiat-Shamir query: 1 without proof-of-work bits -/
def triesOf {C P : Type} : Option (GrW C P) → ℕ
  | none => 1
  | some g => g.more + 1

/-- at most this many attempts after the first: 0 without proof-of-work bits -/
def moreOf {C P : Type} : Option (GrW C P) → ℕ
  | none => 0
  | some g => g.more

/-- Fiat-Shamir queries of one execution with Ns slots, all attempts counted, at most: in each round
the attempts of each slot and the shared attempts (coarse, as xFb: both are counted whatever the
kind of the round) -/
def cFb {K : ℕ} (Ns : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => Ns * triesOf w.grJ + triesOf w.gr0 + cFb Ns s A W

/-- queries to the ghost name fbw t k, that is, attempts number k + 1 (from 0), of one execution
with Ns slots, at most: one for each search that may have more than k + 1 attempts -/
def cTry {K : ℕ} (k Ns : ℕ) : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) =>
    Ns * (if k < moreOf w.grJ then 1 else 0) + (if k < moreOf w.gr0 then 1 else 0) + cTry k Ns s A W

/-- no search of the list of rounds has more than maxMore + 1 attempts -/
def maxMore {K : ℕ} : (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ℕ
  | [], _, _ => 0
  | _ :: s, (_, A), (w, W) => max (max (moreOf w.grJ) (moreOf w.gr0)) (maxMore s A W)

variable (W p)

/-- no search of the scheme has more than maxMoreB W + 1 attempts -/
def maxMoreB : ℕ :=
  max (maxMore L.offline.shape _ W.T.sh)
    (max (maxMore L.link.shape _ W.Lk.sh) (maxMore L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh))

/-- Fiat-Shamir queries of setup and n batches, to the three oracles and all their ghost names
together -/
def xFbG (n : ℕ) : ℕ :=
  cFb 1 L.offline.shape _ W.T.sh + p.leaves * cFb 1 L.link.shape _ W.Lk.sh +
    n * cFb L.maxBatchSize L.onlineBatch.loc.shape L.onlineBatch.ann W.B.sh

end Compile.Batch
