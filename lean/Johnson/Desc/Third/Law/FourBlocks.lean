-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Third/Law/FourBlocks.lean: the last chain's flat list is these four blocks, in this
order: K14's second part, the taken trees' sources, the own proximity test, the chain's end.
Theorems, each by unfolding; no definition.

Why. "The taken trees' sources" (Johnson/Desc/Third/TakenSources.lean) has no round and hands the
record on as it is. If it were left out of the chain's list, no test on the plan that a decision
asks and no later block would notice: the tests on the plan compare rounds, and nothing later reads
what it lays, since it lays nothing. What would be lost is the tie of the own test's declared
sources "taken c n" to the trees of the record's book. No byte of a prover and no caller can leave
it out: only a hand that turns the text of `lastChainWithOwnTest` (Johnson/Desc/Third/Chain.lean). These
theorems go red under such a hand.

OBJECT. `(lastChainWithOwnTest p own).blocksInOrder`: the list that a file's description runs.
USER. Johnson/Desc/ProofFile/Lot/LastChainFour.lean (the proof file's lot). For the key file the
like is stated over its own description (Johnson/RunOne/KeyCut23.lean: second_flat).
LETTERS. p, own, the type of claims: free.

IS IT EMPTY? No: there is no premise.

Main names.
  `second₃TiedEnd_flat`: the list, whole: each of the four as `Chain.blocksInOrder` lays a block outside a
    link: its test on the plan asks besides that the block is bare.
  `second₃TiedEnd_sources`: the block number 1 decides as `takenSources own`, bears its name and has
    no round.
  `second₃TiedEnd_names`: the four names.

Limits. A LOCK ON A TEXT, NO GUARD AT A RUN: nothing here is asked by a decision. Which block `own`
is is the caller's. Nothing on what the four blocks do. Nothing on soundness or on hiding.
-/
import Johnson.Desc.Third.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Third.Law

variable {Cl : Type} (p : P₁₄) (own : Block S₃ Cl)

/-- **The last chain's flat list is these four, in order.** -/
theorem second₃TiedEnd_flat :
    (lastChainWithOwnTest p own).blocksInOrder =
      [batchLinearConstraintsSecondPart p, takenSources own, ownAt own,
        end₃ [batchLinearConstraintsSecondPart p, takenSources own, ownAt own]].map
        fun b => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } := rfl

theorem second₃TiedEnd_length : (lastChainWithOwnTest p own).blocksInOrder.length = 4 := rfl

/-- The block number 1 is "the taken trees' sources". -/
theorem second₃TiedEnd_sources :
    ∃ b, (lastChainWithOwnTest p own).blocksInOrder[1]? = some b ∧ b.decide = (takenSources own).decide ∧
      b.name = "the taken trees' sources" ∧ b.rounds = [] :=
  ⟨_, rfl, rfl, rfl, rfl⟩

theorem second₃TiedEnd_names :
    (lastChainWithOwnTest p own).blocksInOrder.map (·.name) =
      ["K14, second part", "the taken trees' sources", own.name, "the end of chain 3"] := rfl

end VerifiableInference.Desc.Third.Law
