-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/All/Count.lean: HOW MANY TYPED QUERIES THE PROVER OF A WHOLE REQUEST ASKS AT MOST, ON
EVERY PATH (OComp.QueryBound, Rom/OComp.lean): two whole trees, four queries for the two seeds, and
the three compiled runs.

Main names.
  allN   the number.
  queryBound_committerTreeKeptByProver, queryBound_seedsO, queryBound_allY, queryBound_allX, queryBound_proveA.

Limits. AN UPPER BOUND, with the looseness of Johnson/Prover/Law/Count.lean. TYPED queries: what a
typed query costs in calls of one hash function is not in this number: under the library's coding a
Fiat-Shamir query costs one call for each digest of its answer, so every try of a nonce counts W.K +
1 calls. The committer's count is not here. The caps enter as they stand: a capped search counts all
its tries.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.All.Defs
import Johnson.Prover.Law.Count

set_option autoImplicit false

namespace OnBytes.Prover
open _root_.Compile TypedOracleCompiler.Iop TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Compile.Batch.Cms Rom
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout

variable {I X : Type} {lam : ℕ} {L : HolographicProtocol I X} {Bd : Type} {aT : RoundSplits L.offline.shape}
  {aL : RoundSplits L.link.shape} {Kap : Type}

variable (W : QueryLayout lam (typedOracleCarrier L Bd aT aL)) (S : OutOfDomainSampleQueryLayout lam W.K L Bd aT aL)
  (cA : L.OutOfDomainAnswer → List (Dig lam)) (r₀ : L.Rec) (b₀ : Bd) (st : Strats L Kap)
  (capT capL capB : ℕ → ℕ)

/-- The number: two trees, two seeds, three runs. -/
def allN (d : Draw lam L Bd aT aL Kap) : ℕ :=
  2 * 2 ^ W.depth + (2 + (2 * 2 ^ W.depth + (2 +
    (chainN L.offline.shape aT (wTC W).sh capT 0 d.coT.path.length +
      (chainN L.link.shape aL (wLC W).sh capL 0 d.coL.path.length +
        (chainN L.onlineBatch.loc.shape L.onlineBatch.ann (wBC W).sh capB 0 d.coB.path.length + 0))))))

theorem queryBound_committerTreeKeptByProver (y : Fin L.wordLength → L.Symbol) (salt : ℕ → Bits) :
    (committerTreeKeptByProver W b₀ y salt).QueryBound (2 * 2 ^ W.depth) := queryBound_treeO _ _

theorem queryBound_seedsO (cm : Dig lam) : (seedsO W S cm).QueryBound 2 := fun _ _ => trivial

theorem queryBound_allY (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allY W S cA r₀ b₀ st capT capL capB isk x d).QueryBound (allN W capT capL capB d) :=
  (queryBound_committerTreeKeptByProver W b₀ _ _).bind fun _ => (queryBound_seedsO W S _).bind fun _ =>
    (queryBound_committerTreeKeptByProver W b₀ _ _).bind fun _ => (queryBound_seedsO W S _).bind fun _ =>
      (queryBound_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ =>
        (queryBound_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ =>
          (queryBound_proveX _ _ _ _ _ _ _ _ _ _ _ _ _).bind fun _ => trivial

theorem queryBound_allX (isk : I × L.EncodingRandomness × (ℕ → Bits)) (x : X) (d : Draw lam L Bd aT aL Kap) :
    (allX W S cA r₀ b₀ st capT capL capB isk x d).QueryBound (allN W capT capL capB d) := by
  have h : ((allY W S cA r₀ b₀ st capT capL capB isk x d).bind fun y =>
      (OComp.pure (pack isk.1 d y) : TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) _)).QueryBound
        (allN W capT capL capB d + 0) :=
    OComp.QueryBound.bind (queryBound_allY W S cA r₀ b₀ st capT capL capB isk x d) fun _ => trivial
  exact h

/-- The prover with its coins: at a number that bounds allN at all that it may draw. -/
theorem queryBound_proveA (dr : Enum (Draw lam L Bd aT aL Kap)) (π₀ : OfflineLinkOnlineProof lam L aT aL) (N : ℕ)
    (hN : ∀ a, allN W capT capL capB (dr.e a) ≤ N) (isk : I × L.EncodingRandomness × (ℕ → Bits)) :
    ∀ b : List (X × Unit), (proveA W S cA r₀ b₀ st capT capL capB dr π₀ isk b).QueryBound N
  | [] => trivial
  | [(x, _)] => fun a => by
    have h : ((allX W S cA r₀ b₀ st capT capL capB isk x (dr.e a)).bind fun u =>
        (OComp.pure ⟨[(u.toOption.map Prod.fst).getD π₀], rfl⟩ :
          TypedOracleComputation lam W.K (typedOracleCarrier L Bd aT aL) (ZKCP.Gen.Slots (OfflineLinkOnlineProof lam L aT aL) [(x,
                                                           ())]))).QueryBound
          (allN W capT capL capB (dr.e a) + 0) :=
      OComp.QueryBound.bind (queryBound_allX W S cA r₀ b₀ st capT capL capB isk x (dr.e a))
        fun _ => trivial
    exact h.mono (hN a)
  | _ :: _ :: _ => trivial

end OnBytes.Prover
