-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Law/Skel/SkelLists.lean: THE ROUNDS' COLUMN, BY A TABLE OF LISTS: beside the
windows of SkelTiles.lean, a second form of "what holds of a block's name and rounds": the block has
no round, or its rounds are the list that a table T gives at its name. Definitions, statements and
proofs.
  `Lst T n r`     r is empty, or r is T n. `lst_nil`: true of no round, at every name: so the laws
                  of SkelRounds.lean and SkelRoundsParts.lean, which are general in Q, hold at it
  `flat_lists`    from `Lst` at every block: the rounds in a row are, skeleton by skeleton, nothing
                  where the skeleton counts no round, else T at its name
  `lists_are`     and so they are D, where that list on the skeletons is D: one closed fact
Limits. That a block's rounds are T's list at its name is a premise: it is the content. Nothing on
soundness.

-/
import Johnson.Desc.ProofFile.Law.Skel.SkelTiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Sk
open VerifiableInference.Desc

variable {S Cl : Type}

/-- r is empty, or r is T n. -/
def Lst (T : String → List Fmt.DeclaredRound) (n : String) (r : List Fmt.DeclaredRound) : Prop :=
  r = [] ∨ r = T n

theorem lst_nil (T : String → List Fmt.DeclaredRound) (n : String) : Lst T n [] := Or.inl rfl

theorem flat_lists {T : String → List Fmt.DeclaredRound} {bs : List (Block S Cl)}
    (h : ∀ b ∈ bs, Lst T b.name b.rounds) :
    bs.flatMap (·.rounds) =
      (bs.map skel).flatMap fun k => if k.nRounds = 0 then [] else T k.name := by
  rw [List.flatMap_map]
  refine flatMap_congr_mem fun b hb => ?_
  show b.rounds = if b.rounds.length = 0 then [] else T b.name
  by_cases h0 : b.rounds.length = 0
  · rw [if_pos h0]
    exact List.eq_nil_of_length_eq_zero h0
  · rw [if_neg h0]
    rcases h b hb with e | e
    · rw [e] at h0
      exact absurd rfl h0
    · exact e

theorem lists_are {T : String → List Fmt.DeclaredRound} {D : List Fmt.DeclaredRound}
    {bs : List (Block S Cl)} {ks : List Skel} (h : ∀ b ∈ bs, Lst T b.name b.rounds)
    (hk : bs.map skel = ks)
    (hD : (ks.flatMap fun k => if k.nRounds = 0 then [] else T k.name) = D) :
    bs.flatMap (·.rounds) = D := by
  rw [flat_lists h, hk, hD]

end ProofFile.Sk

#print axioms ProofFile.Sk.lst_nil
#print axioms ProofFile.Sk.flat_lists
#print axioms ProofFile.Sk.lists_are
