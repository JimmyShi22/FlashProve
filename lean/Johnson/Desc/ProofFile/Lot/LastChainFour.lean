-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Lot/LastChainFour.lean: the proof file's last chain, as its lot lays it
(Johnson/Desc/ProofFile/Lot/LastChain.lean: `secondSeatOf`), has just the four blocks, in order:
K14's second part, the taken trees' sources, K12's own block, the chain's end. Theorems, each by
unfolding; two abbreviations.

Why: Johnson/Desc/Third/Law/FourBlocks.lean.

OBJECT. `(secondSeatOf Z N).chain.blocksInOrder`: the list of the lot's own value.
USER. Whoever carries a law that is typed at the chain's state to the description's value; the row
"the one block without a round that can vanish unseen" of the proof file's list of open rows.
LETTERS. Z, N: free.

IS IT EMPTY? No: there is no premise. `secondSeat_of` has one: that the plan gives the places'
numbers; where it does not, `secondSeat` returns nothing and the description cannot be made.

Main names.
  `lastPar Z`, `lastOwn N`: names for two terms of the lot's text: the chain's public parameters and
    K12's block behind its door. That they are the lot's own is part of `secondSeatOf_chain`.
  `secondSeatOf_chain`: the lot's chain is `lastChainWithOwnTest (lastPar Z) (lastOwn N)`.
  `secondSeatOf_flat`, `secondSeatOf_sources`, `secondSeatOf_names`: the list; its block number 1;
    the four names.
  `secondSeat_of`: whatever `secondSeat Z` returns is `secondSeatOf Z N` at the plan's own numbers.

Limits. A LOCK ON A TEXT, NO GUARD AT A RUN. Of the lot, not of a whole description's value: that
the description's last chain is this lot's is the fold's. Nothing on soundness or on hiding.
-/
import Johnson.Desc.ProofFile.Lot.LastChain
import Johnson.Desc.Third.Law.FourBlocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Third
open ProofFile
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.Third (S₃ P₁₄ lastChainWithOwnTest batchLinearConstraintsSecondPart takenSources ownAt end₃)

/-- The chain's public parameters, as the lot's text makes them. -/
abbrev lastPar (Z : Pub) : P₁₄ :=
  VerifiableInference.Desc.Third.p₁₄Z Z.p.chains.made.sized.proof.set
    Z.p.chains.made.sized.proof.codes Z.p.chains.made.sized.proof.batch

/-- K12's block behind its door, as the lot's text makes it. -/
abbrev lastOwn (N : H2U.Places4) : Block S₃ Unit :=
  VerifiableInference.Desc.K12.Seat.onOwn
    (VerifiableInference.Desc.K12.proximityTestKind VerifiableInference.Desc.K12.guardedProximityTestParts
      (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W))

variable (Z : Pub) (N : H2U.Places4)

theorem secondSeatOf_chain :
    ((secondSeatOf Z N).chain : Chain S₃ Unit) = lastChainWithOwnTest (lastPar Z) (lastOwn N) := rfl

/-- **The lot's flat list is these four, in order.** -/
theorem secondSeatOf_flat :
    ((secondSeatOf Z N).chain.blocksInOrder : List (Block S₃ Unit)) =
      [batchLinearConstraintsSecondPart (lastPar Z), takenSources (lastOwn N), ownAt (lastOwn N),
        end₃ [batchLinearConstraintsSecondPart (lastPar Z), takenSources (lastOwn N), ownAt (lastOwn N)]].map
        fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := rfl

/-- The lot's block number 1 is "the taken trees' sources", at the lot's own block of K12. -/
theorem secondSeatOf_sources :
    ∃ b : Block S₃ Unit, ((secondSeatOf Z N).chain.blocksInOrder : List (Block S₃ Unit))[1]? = some b ∧
      b.decide = (takenSources (lastOwn N)).decide ∧ b.name = "the taken trees' sources" ∧
      b.rounds = [] :=
  ⟨_, rfl, rfl, rfl, rfl⟩

theorem secondSeatOf_names :
    ((secondSeatOf Z N).chain.blocksInOrder : List (Block S₃ Unit)).map (·.name) =
      ["K14, second part", "the taken trees' sources", (lastOwn N).name, "the end of chain 3"] :=
  rfl

/-- Whatever `secondSeat` returns is the lot at the plan's own numbers. -/
theorem secondSeat_of (B : SecondSeat) (h : secondSeat Z = some B) :
    ∃ N, H2U.placesOfMade Z.made = .ok N ∧ B = secondSeatOf Z N := by
  unfold secondSeat at h
  split at h
  · rename_i N hN
    exact ⟨N, hN, (Option.some.inj h).symm⟩
  · cases h

end P2Third
