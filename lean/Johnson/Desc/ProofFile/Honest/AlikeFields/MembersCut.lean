-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AlikeFields/MembersCut.lean: two rows whose parts have the same counts
of moves, one by one, are cut into members with the same numbers and the same declared rounds
(`membersOf`, Honest/Side.lean). Free of any kind of sub-protocol. Two theorems; no definition.

Written with the lookups (K3), on the shelf that the frame named for files
that are free of any kind.

What is shown.
  `members_cut`: the two lists of members, each member mapped to its number and its rounds, are one
    list. The two rows may pass on values of two types.
  `member_cut`: at two sides with one sub-protocol whose rows are so cut: each member of the second
    has a member of the first with its number and its rounds.

Why. `membersOf` reads of a part its count of moves alone. So a sentence on the members' numbers and
declared rounds goes over from the one side to the other.

Limits. Nothing on the parts, their moves or the simulators beside them.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.AlikeFields
open VerifiableInference.Desc (Oracle)

variable {S Cl V W X X' Pb : Type}

/-- **Rows that are cut alike have members with the same numbers and rounds**, in order. -/
theorem members_cut : ∀ (row : List (Part V W X × Sim Pb)) (row' : List (Part V W X' × Sim Pb)),
    row.map (·.1.moves.length) = row'.map (·.1.moves.length) →
    ∀ (j : Nat) (rs : List (Fmt.DeclaredRound × List Oracle)),
      (membersOf row j rs).map (fun u => (u.number, u.rounds)) =
        (membersOf row' j rs).map fun u => (u.number, u.rounds)
  | [], [], _, _, _ => rfl
  | [], _ :: _, h, _, _ => nomatch h
  | _ :: _, [], h, _, _ => nomatch h
  | x :: l, x' :: l', h, j, rs => by
    have h' : x.1.moves.length :: l.map (·.1.moves.length) =
        x'.1.moves.length :: l'.map (·.1.moves.length) := h
    obtain ⟨h1, h2⟩ := List.cons.inj h'
    simp only [membersOf, List.map_cons]
    rw [h1, members_cut l l' h2 (j + 1) _]

/-- Conditional on hb and hc: each member of the second side has a member of the first with its
number and its rounds. -/
theorem member_cut (σ : Side S Cl V W X Pb) (σ' : Side S Cl V W X' Pb) (hb : σ'.block = σ.block)
    (hc : σ.row.map (·.1.moves.length) = σ'.row.map (·.1.moves.length)) (u' : Member V W X' Pb)
    (hu' : u' ∈ σ'.members) : ∃ u ∈ σ.members, u.number = u'.number ∧ u.rounds = u'.rounds := by
  unfold Side.members at hu'
  rw [hb] at hu'
  have hm : (u'.number, u'.rounds) ∈
      (membersOf σ'.row 0 (σ.block.rounds.zip σ.block.oracles)).map
        fun u => (u.number, u.rounds) := List.mem_map.2 ⟨u', hu', rfl⟩
  rw [← members_cut σ.row σ'.row hc 0 _] at hm
  obtain ⟨u, hu, eu⟩ := List.mem_map.1 hm
  exact ⟨u, hu, congrArg Prod.fst eu, congrArg Prod.snd eu⟩

end ProofFile.Honest.AlikeFields

#print axioms ProofFile.Honest.AlikeFields.members_cut
#print axioms ProofFile.Honest.AlikeFields.member_cut
