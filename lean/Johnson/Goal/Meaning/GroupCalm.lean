-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/GroupCalm.lean: DEFINITIONS AND SMALL TOOLS for "who is a member of which group
of the statement, and with which flag": what the code switching reads of the group that the last
closing has folded (switchKept, OnBytes/Iop/Cs.lean: the members whose flag "kept" is true).

  GS S S': the statement S' has as many groups as S, and each group has the same members with the
    same flags. Reflexive, transitive. What a step keeps that neither makes a group nor joins a
    message to one.
  keptOf m k: the entries of m whose flag in k is true, in order. switchKept_eq: switchKept r is
    keptOf of r's layout's two arrays.
  keptOf_append, keptOf_false: over two arrays laid one behind the other; over flags that are all
    false.
  flagsKept sh l, flagsOwn sh l: the flags that the plan's shape gives: to the kept copies that the
    switch into group l sends (the target's "kept again"), and to link l's own messages, in the
    order of the shape's list (life > 0).
  GroupIs sh l kb own G: the group G has just these members, in this order: the switch's main
    message (none at link 0), the kept copies kb, the link's own messages own; with the flags false,
    flagsKept, and flagsOwn as far as own goes.
Not claimed: that any step keeps GS, or that any group is so.
-/
import Johnson.Goal.Meaning.K2Share.FrontNotices

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.K2

open OnBytes OnBytes.Model
open OnBytes.Params (ReqShape)
open VerifiableInference.Desc.First

/-- As many groups; each with the same members and the same flags. -/
def GS (S S' : Statement) : Prop :=
  S'.groups.size = S.groups.size ∧
    ∀ g : Nat, (S'.groups[g]?).map (fun G : Group => (G.members, G.kept)) =
      (S.groups[g]?).map (fun G : Group => (G.members, G.kept))

theorem gs_refl (S : Statement) : GS S S := ⟨rfl, fun _ => rfl⟩

theorem gs_trans {A B C : Statement} (h : GS A B) (k : GS B C) : GS A C :=
  ⟨k.1.trans h.1, fun g => (k.2 g).trans (h.2 g)⟩

/-- The entries whose flag is true, in order. -/
def keptOf (m : Array Nat) (k : Array Bool) : Array Nat := ((m.zip k).filter (·.2)).map (·.1)

theorem switchKept_eq (r : SingleRows) :
    switchKept r = keptOf r.layout.members r.layout.kept := rfl

/-- The flags of the kept copies that the switch into group l sends. -/
def flagsKept (sh : ReqShape) (l : Nat) : Array Bool := (K2.targetAt sh l).kept.map (·.keptAgain)

/-- The flags of link l's own messages, in the order of the shape's list. -/
def flagsOwn (sh : ReqShape) (l : Nat) : Array Bool :=
  (((sh.link[l]?).map (·.messages)).getD []).toArray.map fun m => decide (0 < m.life)

/-- **The group of link l, as the frame's two lists say it.** -/
def GroupIs (sh : ReqShape) (l : Nat) (kb own : Array Nat) (G : Group) : Prop :=
  ∃ pre : Array Nat, pre.size = (if l = 0 then 0 else 1) ∧
    G.members = pre ++ kb ++ own ∧
    G.kept = pre.map (fun _ => false) ++ flagsKept sh l ++ (flagsOwn sh l).extract 0 own.size ∧
    kb.size = (flagsKept sh l).size ∧ own.size ≤ (flagsOwn sh l).size

theorem keptOf_toList (m : Array Nat) (k : Array Bool) :
    (keptOf m k).toList = ((m.toList.zip k.toList).filter (·.2)).map (·.1) := by
  simp [keptOf]

theorem keptOf_append {a b : Array Nat} {ka kb : Array Bool} (h : a.size = ka.size) :
    keptOf (a ++ b) (ka ++ kb) = keptOf a ka ++ keptOf b kb := by
  apply Array.toList_inj.1
  rw [Array.toList_append, keptOf_toList, keptOf_toList, keptOf_toList, Array.toList_append,
    Array.toList_append, List.zip_append (by simpa using h), List.filter_append, List.map_append]

theorem keptOf_false (a : Array Nat) : keptOf a (a.map fun _ => false) = #[] := by
  apply Array.toList_inj.1
  rw [keptOf_toList]
  have e : (a.toList.zip (a.map fun _ => false).toList).filter (·.2) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    have k := (List.of_mem_zip hx).2
    simp only [Array.toList_map, List.mem_map] at k
    obtain ⟨_, -, e⟩ := k
    simp [← e]
  rw [e]
  rfl

/-- **The kept members of such a group.** -/
theorem GroupIs.kept {sh : ReqShape} {l : Nat} {kb own : Array Nat} {G : Group}
    (h : GroupIs sh l kb own G) :
    keptOf G.members G.kept =
      keptOf kb (flagsKept sh l) ++ keptOf own ((flagsOwn sh l).extract 0 own.size) := by
  obtain ⟨pre, -, e1, e2, e3, -⟩ := h
  rw [e1, e2, keptOf_append (by simp [e3]), keptOf_append (by simp), keptOf_false,
    Array.empty_append]

#print axioms keptOf_append
#print axioms GroupIs.kept

end Meaning.K2
