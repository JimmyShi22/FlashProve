-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Face/CompleteAsIOP.lean: what it means that a prover is complete as an interactive
oracle proof (IOP), before any hash. Definitions only: nothing is proved here.

If this holds: on every index and request in the relation, the verifiers of the protocol's three
parts accept the honest prover, but for chance α.

 1. The protocol has three parts. Offline: the proof in the key file, on the committed encoding of
    the index. Link: from a further encoding of the index to the first. Online: the proof for a
    request, on that further encoding.
 2. Each encoding has an out-of-domain sample: the verifier picks a seed, and the protocol says what
    the honest answers at that seed are.
 3. The verifiers are the protocol's: the same challenges and the same verdict of which its
    soundness speaks.
 4. A prover is all three parts together, each with random coins of its own.
 5. The verifier rejects unless all the proof-of-work bits in its challenges are 0, so nearly every
    uniform challenge is rejected. The compiled prover searches for a nonce until these bits are 0,
    so in a proof only challenges that pass ever occur.
 6. So this statement speaks of the challenges that pass: uniform among them, whatever the nonces.
 7. A run fails if the prover aborts, or if the verifier, reading the encoding, rejects it.
 8. Complete as an IOP with error α means: for every index and request in the relation, every
    encoding, seed and copy's number, each part fails rarely, over the prover's coins and the
    challenges together, and the three parts' chances of failing add up to at most α.
 9. One thing more is asked, since the compiled verifier tests it and the IOP's does not: a
    request's messages hold the number of the copy.
10. This is for one request a proof.

Names. Lines 5 and 6: WorkBits, WorkBitsFaithful, chanceAtPassing. Line 7: FailsAt. Line 8:
CompleteIOP. All three parts as one game: WholeRunComplete. The words are in Hiop/CompleteCore.lean.
L, of the library's type HolographicProtocol, holds the parts: L.offline offline, L.link, L.onlineBatch.loc online; L.encodeIndex the
encoding, L.recOf the seed with its honest answers. A prover is a value of HonestProvers L. Rho is a
list of challenges, InteractiveOracleProof.accept the verdict. In the clauses i is an index, x a request, r an
encoding's randomness, e a seed, n a copy's number, c a coin.

What this file does not fix: the relation. Our values are in E2E/CompleteAsIOPAtTheTerm.lean.
-/
import Hiop.CompleteCore
import Johnson.Face.Protocol

set_option autoImplicit false

noncomputable section

open scoped ENNReal

namespace VerifiableInference.Compilation
open Prob
open _root_.Iop

variable {Index Instance : Type}

/-! ## 1. The three parts -/

/-- **Completeness of the prover, part by part, with each error named.** copyNumberIn: does this
part of a request's plain messages hold this copy's number? Relation: the pairs of an index and a
request of which this speaks. -/
structure CompleteInParts (L : HolographicProtocol Index Instance) (prover : HonestProvers L) (work : PartsWork L)
    (copyNumberIn : ℕ → Plains L.onlineBatch.loc.shape → Bool) (Relation : Index → Instance → Prop)
    (offlineError linkError onlineError : ℝ≥0∞) : Prop where
  /-- The offline run fails rarely, at every encoding and seed of an index of the relation. -/
  offlineAccepted : ∀ i x r e, Relation i x →
    FailsRarely prover.offlineProver work.offline (L.encodeIndex i r) (i, r, e) (L.recOf i r e) offlineError
  /-- So does the link's, between any two encodings of that index. -/
  linkAccepted : ∀ i x r e r' e', Relation i x →
    FailsRarely prover.linkProver work.link (L.encodeIndex i r, L.encodeIndex i r') (i, (r, e), (r', e'))
      (L.recOf i r e, L.recOf i r' e') linkError
  /-- So does the online run, on any encoding, under any copy's number. -/
  onlineAccepted : ∀ i x r e n, Relation i x →
    FailsRarely prover.onlineProver work.online (L.encodeIndex i r) (i, r, e, n) (x, L.recOf i r e) onlineError
  /-- A request's run sends the copy's number that the prover was handed, at all challenges and
  nonces. -/
  sendsCopyNumber : ∀ i x r e n (c : prover.onlineProver.Coin) (τ : Tr L.onlineBatch.loc.shape), Relation i x →
    work.online.sameButForNonces
      ((prover.onlineProver.strat (i, r, e, n) (x, L.recOf i r e) c).run τ.rho).1 τ →
    copyNumberIn n τ.plains = true

/-- **THE DEFINITION: the prover is complete as an IOP, with error α.** -/
def CompleteIOP (L : HolographicProtocol Index Instance) (prover : HonestProvers L) (work : PartsWork L)
    (copyNumberIn : ℕ → Plains L.onlineBatch.loc.shape → Bool) (Relation : Index → Instance → Prop)
    (α : ℝ≥0∞) : Prop :=
  work.Faithful ∧
    ∃ offlineError linkError onlineError : ℝ≥0∞,
      offlineError + linkError + onlineError ≤ α ∧
        CompleteInParts L prover work copyNumberIn Relation offlineError linkError onlineError

/-! ## 2. The three as one game -/

/-- All that a whole run draws: two seeds; the challenges of the three parts; the prover's coins. -/
abbrev WholeDraw (L : HolographicProtocol Index Instance) (prover : HonestProvers L) : Type :=
  (L.OutOfDomainSeed × L.OutOfDomainSeed) × (Rho L.offline.shape × Rho L.link.shape × Rho L.onlineBatch.loc.shape) ×
    (prover.offlineProver.Coin × prover.linkProver.Coin × prover.onlineProver.Coin)

/-- **The whole run fails**: on the index i, the request x, the randomness r₁ and r₂ of the first
encoding and of the further one, and the copy's number n, the offline, link or online run fails at
its challenges with the work bits set to 0. -/
def WholeRunFails (L : HolographicProtocol Index Instance) (prover : HonestProvers L) (work : PartsWork L) (i : Index)
    (x : Instance) (r₁ r₂ : L.EncodingRandomness) (n : ℕ) : WholeDraw L prover → Prop
  | ((e₁, e₂), (ρOffline, ρLink, ρOnline), (cOffline, cLink, cOnline)) =>
    FailsAt prover.offlineProver work.offline (L.encodeIndex i r₁) (i, r₁, e₁) (L.recOf i r₁ e₁) cOffline
        (work.offline.cleared ρOffline) ∨
      FailsAt prover.linkProver work.link (L.encodeIndex i r₁, L.encodeIndex i r₂) (i, (r₁, e₁), (r₂, e₂))
        (L.recOf i r₁ e₁, L.recOf i r₂ e₂) cLink (work.link.cleared ρLink) ∨
      FailsAt prover.onlineProver work.online (L.encodeIndex i r₂) (i, r₂, e₂, n) (x, L.recOf i r₂ e₂) cOnline
        (work.online.cleared ρOnline)

/-- **Completeness as one game**: the work bits are faithful, and for every index and request in the
relation, over uniform seeds, the challenges that pass and the prover's uniform coins, the whole run
fails with chance at most α. -/
def WholeRunComplete (L : HolographicProtocol Index Instance) (prover : HonestProvers L) (work : PartsWork L)
    (Relation : Index → Instance → Prop) (α : ℝ≥0∞) : Prop :=
  work.Faithful ∧ ∀ i x, Relation i x → ∀ (r₁ r₂ : L.EncodingRandomness) (n : ℕ),
    pr (unif (WholeDraw L prover)) {d | WholeRunFails L prover work i x r₁ r₂ n d} ≤ α

/-- States that the definition gives the game, for every protocol and prover: a union bound. -/
def CompleteGivesWholeRun : Prop :=
  ∀ {Index Instance : Type} (L : HolographicProtocol Index Instance) (prover : HonestProvers L) (work : PartsWork L)
    (copyNumberIn : ℕ → Plains L.onlineBatch.loc.shape → Bool) (Relation : Index → Instance → Prop)
    (α : ℝ≥0∞),
    CompleteIOP L prover work copyNumberIn Relation α → WholeRunComplete L prover work Relation α

end VerifiableInference.Compilation
