-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/GsDef.lean: A LIGHT FILE, OVER THE LIBRARY's STATEMENT ALONE
(OnBytes/Iop/Ground.lean): the relation «as many groups, and at every number the same members and
kept members» between two statements, which the code switch's condition asks of whatever stands
between two switches; and that one row more on one group's list of open rows keeps it. Cut out of
GsAt.lean, which imports it: so that every kind's files can call these in their own build. Not a
letter of a statement turns.

What is said.
  `GS St St'`. `GS.refl`, `GS.trans`, `gs_of_eq`. `gs_push`: a statement whose groups are another's
    with one row pushed on one group's list stands in GS to it.

Limits. A definition and small rules. The rows of a group may grow: GS does not read them. Nothing
on soundness.

-/
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes

/-- **As many groups; at every number the same members and kept members.** -/
def GS (St St' : Statement) : Prop :=
  St'.groups.size = St.groups.size ∧
    ∀ g : Nat, (St'.groups[g]?).map (fun G : Group => (G.members, G.kept)) =
      (St.groups[g]?).map (fun G : Group => (G.members, G.kept))

theorem GS.refl (St : Statement) : GS St St := ⟨rfl, fun _ => rfl⟩

theorem gs_of_eq {St St' : Statement} (h : St' = St) : GS St St' := h ▸ GS.refl St

theorem GS.trans {A B C : Statement} (h : GS A B) (h' : GS B C) : GS A C :=
  ⟨h'.1.trans h.1, fun g => (h'.2 g).trans (h.2 g)⟩

/-- One row more on one group's list. -/
theorem gs_push (St St' : Statement) (g : Nat) (row : OnBytes.Row)
    (h : St'.groups = St.groups.modify g fun G => { G with rows := G.rows.push row }) :
    GS St St' := by
  refine ⟨by rw [h, Array.size_modify], fun j => ?_⟩
  rw [h, Array.getElem?_modify]
  by_cases e : g = j
  · rw [if_pos e]
    cases St.groups[j]? <;> rfl
  · rw [if_neg e]

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.GS.trans
#print axioms VerifiableInference.Desc.LinkJoin.gs_push
