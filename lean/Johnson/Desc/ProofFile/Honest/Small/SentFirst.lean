-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/SentFirst.lean: WHICH ROUND OF A CHAIN SENDS A MEMBER's TREES:
TWO GENERAL LAWS: NO KIND IS NAMED IN THEM. Statements and proofs. PUBLIC: on lists of declared
rounds and on a chain's list of sub-protocols: no coin, no witness, no input, no thread.

  sender_behind   the round that sends a tree, behind a stretch of rounds: on lists of rounds
  trees_sent_first   where every sub-protocol of the chain lists as many oracle messages as its
                rounds count roots (Listed, Honest/Small/FixedSent.lean): a member's trees that its
                first round states are sent in that round: the premise hoff of ownTreesAt_by_play
                (Honest/Small/OwnTreesByPlay.lean) at off := 0, for every kind whose trees go out in
                its member's first round

WHY IT LIES HERE. hoff is wanted at every kind, and the first law lay in a file of the kind K1 that
no other kind's files can import.

By rootsSum_cons, treesTo_roots, decls_split (Honest/Small/FixedSent.lean), declsTo_succ
(Honest/Thread/MadeLaw.lean).

Limits. Of a member's FIRST round alone: a kind whose trees go out later pays hoff by sender_behind
itself. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Small.FixedSent
import Johnson.Desc.ProofFile.Honest.Thread.MadeLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Block sendRound)

variable {S Cl : Type}

/-- The round that sends a tree, behind a stretch of rounds. -/
theorem sender_behind : ∀ (l₁ l₂ : List Fmt.DeclaredRound) (j : Nat),
    sendRound (l₁ ++ l₂) (rootsSum l₁ + j) = (sendRound l₂ j).map (· + l₁.length)
  | [], l₂, j => by
    have e : rootsSum [] = 0 := rfl
    rw [e, Nat.zero_add, List.nil_append]
    cases sendRound l₂ j <;> rfl
  | r :: l₁, l₂, j => by
    rw [List.cons_append, rootsSum_cons]
    have e : sendRound (r :: (l₁ ++ l₂)) (r.entry.roots + rootsSum l₁ + j) =
        (sendRound (l₁ ++ l₂) (rootsSum l₁ + j)).map (· + 1) := by
      conv_lhs => unfold sendRound
      rw [if_neg (by omega), show r.entry.roots + rootsSum l₁ + j - r.entry.roots =
        rootsSum l₁ + j from by omega]
    rw [e, sender_behind l₁ l₂ j]
    cases sendRound l₂ j with
    | none => rfl
    | some i =>
      show some (i + l₁.length + 1) = some (i + (l₁.length + 1))
      rfl

/-- **Where every sub-protocol of the chain is Listed, a member's trees that its first round states
are sent in that round.** -/
theorem trees_sent_first (bs : List (Block S Cl)) (hsh : ∀ x ∈ bs, Listed x) {b : Nat}
    {blk : Block S Cl} (hblk : bs[b]? = some blk) {r₀ : Fmt.DeclaredRound} {rs : List Fmt.DeclaredRound}
    (hr : blk.rounds = r₀ :: rs) {j : Nat} (hj : j < r₀.entry.roots) :
    sentIn (bs.flatMap (·.rounds)) (treesTo bs b + j) = roundsTo bs b + 0 := by
  unfold sentIn
  rw [decls_split bs (b + 1), declsTo_succ hblk, List.append_assoc, treesTo_roots bs hsh b,
    sender_behind, hr, List.cons_append]
  unfold sendRound
  rw [if_pos hj]
  show 0 + (declsTo bs b).length = roundsTo bs b + 0
  rw [Nat.zero_add, Nat.add_zero]
  rfl

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.sender_behind
#print axioms ProofFile.Honest.Small.trees_sent_first
