-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/Members.lean: NOT a law on a part or on a distribution:
CONDITIONAL where it says so: three small lemmas on how a side's row is cut into members
(`membersOf`, Honest/Side.lean).

  `mem_of_membersOf`   a round of a member that is cut out of a list of rounds is a round of that
                       list
  `mem_rounds_of_member`   a round of a member of a side is a round of the side's block, with its
                           oracle messages
  `member_roots_of_shaped`   CONDITIONAL: at a side whose block passes the plan's test on shapes
                             (`Block.shaped`), a member's round with no oracle message has an entry
                             that counts no root

So a caller of `roots_of_shaped` (Honest/Small/Field.lean) at a member of its row need not show that
the round lies among the block's rounds. It still owes: the block is shaped; u is a member; r is a
round of u; r has no oracle message.

The frame's terms that are used here (part, side, row, member and the like): the head of
Honest/Small/Field.lean. All names stand in the namespace ProofFile.Honest.Small: a caller opens it.

Limits. Nothing on bytes that are left over behind a round's items: the format's `Round.ok`
(Fmt/Rules8.lean) refuses these; no statement here speaks of that test. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Small
open VerifiableInference.Desc (Oracle)

variable {S Cl V W X Pb : Type}

/-- A round of a member that is cut out of a list of rounds is a round of that list. -/
theorem mem_of_membersOf : ∀ (row : List (Part V W X × Sim Pb)) (j : Nat)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (u : Member V W X Pb), u ∈ membersOf row j rs →
    ∀ r ∈ u.rounds, r ∈ rs
  | [], _, _, _, h, _, _ => absurd h (List.not_mem_nil)
  | x :: l, j, rs, u, h, r, hr => by
    rcases List.mem_cons.1 h with rfl | h'
    · exact List.mem_of_mem_take hr
    · exact List.mem_of_mem_drop (mem_of_membersOf l (j + 1) _ u h' r hr)

/-- A round of a member is a round of the side's block, with its oracle messages. -/
theorem mem_rounds_of_member {σ : Side S Cl V W X Pb} {u : Member V W X Pb} (hu : u ∈ σ.members)
    {r : Fmt.DeclaredRound × List Oracle} (hr : r ∈ u.rounds) :
    r ∈ σ.block.rounds.zip σ.block.oracles :=
  mem_of_membersOf σ.row 0 _ u hu r hr

/-- CONDITIONAL. At a shaped block a member's round with no oracle message counts no root. -/
theorem member_roots_of_shaped {σ : Side S Cl V W X Pb} (hb : σ.block.shaped = true)
    {u : Member V W X Pb} (hu : u ∈ σ.members) {r : Fmt.DeclaredRound × List Oracle}
    (hr : r ∈ u.rounds) (h : r.2 = []) : r.1.entry.roots = 0 :=
  roots_of_shaped hb (mem_rounds_of_member hu hr) h

end ProofFile.Honest.Small

#print axioms ProofFile.Honest.Small.mem_of_membersOf
#print axioms ProofFile.Honest.Small.mem_rounds_of_member
#print axioms ProofFile.Honest.Small.member_roots_of_shaped
