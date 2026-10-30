-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/LayBegun.lean: the beginning of a proximity test on a group (`begun`,
OnBytes/Slice/BlkBegin.lean) leaves the group's layout as it was. Statements and proofs.

The closing of a link makes the group's layout at the statement in front, then marks the group's
test as begun, and batches the group's rows at the statement behind that mark. The laws of
LayBlocks.lean to LayTables.lean, beside this file, speak of a layout and of the statement at which
it is made. So that they can be spent at the statement behind the mark:
  `has_of_shape`, `begun_has`: the mark turns no table's being there.
  `closeLedgers_groups'`, `begun_group`: the group behind the mark: marked, without open rows;
    members, marks of kept members and codes as before.
  `begun_sizes`: the sizes that the layout is made of are as before.
  `begun_layout`: `(begun S g G).layout g = S.layout g`.
It rests on the library's `closeLedgers_shape`, `closeLedgers_codes` and `begun_rowBits`
(OnBytes/Slice/BlkStLaws.lean).

Limits. Of the group g alone. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.LayTables
import OnBytes.Slice.BlkStLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.LayLaw
open OnBytes.Slice

/-- Two statements whose oracle messages have the same shapes say the same on which tables are
there. -/
theorem has_of_shape (S T : Statement) (o : Nat) (part : Part)
    (h : (T.oracles[o]?).map (·.shape) = (S.oracles[o]?).map (·.shape)) :
    T.has o part = S.has o part := by
  unfold Statement.has
  cases h1 : T.oracles[o]? with
  | none =>
    cases h2 : S.oracles[o]? with
    | none => rfl
    | some y => rw [h1, h2] at h; cases h
  | some x =>
    cases h2 : S.oracles[o]? with
    | none => rw [h1, h2] at h; cases h
    | some y =>
      rw [h1, h2] at h
      have e : x.shape = y.shape := Option.some.inj h
      dsimp only
      rw [e]

theorem begun_has (S : Statement) (g : Nat) (G : Group) (o : Nat) (part : Part) :
    (begun S g G).has o part = S.has o part :=
  has_of_shape S _ o part (closeLedgers_shape G.members.toList S o)

theorem closeLedgers_groups' : ∀ (l : List Nat) (S : Statement),
    (closeLedgers S l).groups = S.groups
  | [], _ => rfl
  | _ :: l, _ => closeLedgers_groups' l _

/-- The group behind the beginning of its test: marked, without open rows. -/
theorem begun_group (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    (begun S g G).groups[g]? = some { G with inRun := true, rows := #[] } := by
  show ((closeLedgers S G.members.toList).groups.modify g _)[g]? = _
  rw [closeLedgers_groups', Array.getElem?_modify, if_pos rfl, hG]
  rfl

theorem begun_sizes (S : Statement) (g : Nat) (G : Group) (part : Part) :
    laySizes (begun S g G) { G with inRun := true, rows := #[] } part = laySizes S G part := by
  unfold laySizes
  simp only [begun_has, begun_rowBits]

/-- **THE BEGINNING OF A TEST LEAVES THE GROUP's LAYOUT AS IT WAS.** -/
theorem begun_layout (S : Statement) (g : Nat) (G : Group) (hG : S.groups[g]? = some G) :
    (begun S g G).layout g = S.layout g := by
  rw [layout_eq S g G hG, layout_eq _ g _ (begun_group S g G hG), begun_sizes, begun_sizes]
  have hc : (begun S g G).codes = S.codes := closeLedgers_codes _ _
  rw [hc]

end OnBytes.LayLaw

#print axioms OnBytes.LayLaw.begun_layout
