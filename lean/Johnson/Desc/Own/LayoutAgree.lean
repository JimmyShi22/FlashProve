-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Own/LayoutAgree.lean: the layout of a group that is a named part of the description
(Johnson/Desc/Own/Layout.lean) is the program's, at all arguments.

Statements and proofs. No block imports this file.
Main names:
  `blockBits_agrees`: the sizes that Statement.layout (OnBytes/Iop/Ground.lean) lays are
    `blockBits`.
  `layoutMade_eq`: layoutMade S g = S.layout g.
  `layout_of_group`: where the statement has the group G at the number g, S.layout g is
    some (layoutOf S G).
  `layoutMade_some`: a layout is made just where the group is there, and it is then layoutOf of that
    group.
  `layoutMade_isSome`, `layoutMade_none`: layoutMade returns a layout where layoutCan says yes, and
    nothing where it says no.
Limits: No soundness is claimed, and nothing is said on hiding.
Every theorem of this file is proved outright; what each rests on is printed at the file's end.

-/
import Johnson.Desc.Own.Layout
import Johnson.Desc.Own.RowsAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem blockBits_agrees (S : OnBytes.Statement) (G : OnBytes.Group) (part : OnBytes.Part) :
    ((Array.range G.members.size).map fun i =>
      let o := G.members.getD i OnBytes.noId
      if S.has o part && !(part == .main && G.kept.getD i false) then some (S.rowBits o part)
      else none) = blockBits S G part := by
  unfold blockBits
  simp only [tableThere_agrees]

theorem layoutMade_eq (S : OnBytes.Statement) (g : Nat) : layoutMade S g = S.layout g := by
  unfold layoutMade OnBytes.Statement.layout
  congr 1
  funext G
  unfold layoutOf
  simp only [blockBits_agrees]

/-- Where the group is there, the program's layout is layoutOf of that group. -/
theorem layout_of_group {S : OnBytes.Statement} {g : Nat} {G : OnBytes.Group}
    (h : S.groups[g]? = some G) : S.layout g = some (layoutOf S G) := by
  rw [← layoutMade_eq]
  unfold layoutMade
  rw [h]
  rfl

theorem layoutMade_some {S : OnBytes.Statement} {g : Nat} {L : OnBytes.GroupLayout} :
    layoutMade S g = some L ↔ ∃ G, S.groups[g]? = some G ∧ L = layoutOf S G := by
  unfold layoutMade
  constructor
  · intro h
    obtain ⟨G, hG, rfl⟩ := Option.map_eq_some_iff.1 h
    exact ⟨G, hG, rfl⟩
  · rintro ⟨G, hG, rfl⟩
    rw [hG]
    rfl

theorem layoutMade_isSome (S : OnBytes.Statement) (g : Nat) :
    (layoutMade S g).isSome = layoutCan S g := by
  unfold layoutMade layoutCan
  by_cases h : g < S.groups.size
  · rw [Array.getElem?_eq_getElem h, decide_eq_true h]
    rfl
  · rw [Array.getElem?_eq_none (Nat.le_of_not_lt h), decide_eq_false h]
    rfl

theorem layoutMade_none (S : OnBytes.Statement) (g : Nat) :
    layoutMade S g = none ↔ layoutCan S g = false := by
  rw [← layoutMade_isSome]
  cases layoutMade S g <;> simp

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.layoutMade_eq
#print axioms VerifiableInference.Desc.Own.layout_of_group
#print axioms VerifiableInference.Desc.Own.layoutMade_some
#print axioms VerifiableInference.Desc.Own.layoutMade_isSome
#print axioms VerifiableInference.Desc.Own.layoutMade_none
