-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GroupsStay.lean: A YES OF THE CLOSING OF A LINK (KIND K10) LEAVES THE
NUMBER OF THE STATEMENT's GROUPS AND EVERY GROUP's MEMBERS AND FLAGS; AND THE CLAIM THAT IT HANDS ON
BEARS THE CLOSED GROUP's OWN MEMBERS AND FLAGS IN ITS LAYOUT. Statements and proofs.

Why. The code switch behind a closing reads, off the claim that the closing hands on, which members
of the closed group were joined as kept (`rows.layout.members`, `rows.layout.kept`). Other files
walk the first chain with one relation between two statements: as many groups, and at every number
the same members and the same flags. That relation is wanted of each kind along its own yes.
  `memK`, `behind_pairs`, `behind_count`; `closing_groups`: `closing P S g mask rs = .ok (out, S')`:
    S' has as many groups as S; at every number g' the group's pair (members, kept) is as it was.
  `closing_layout`: and there is the group G at g in S with out.layout.members = G.members and
    out.layout.kept = G.kept.
  `closeFrame_groups`: BOTH along a yes of `closeFrame` (the frame's closing: what K10's
    sub-protocol decides by): the groups' number and pairs; and the frame's rows behind (x.1.rows)
    bear, in their layout, the members and flags of the group at the frame's number
    (`closeFrame_lays`, Lays.lean).
Limits. On the statement's groups and the claim's layout alone. That the group's members and flags
are what the plan says is not here. Nothing on soundness.



-/
import Johnson.Desc.First.Close.Law.StBehind
import Johnson.Desc.First.Close.Law.Whole
import Johnson.Desc.First.Close.Law.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice

/-- The pair that is asked to stay. -/
abbrev memK (G : Group) : Array Nat × Array Bool := (G.members, G.kept)

theorem behind_pairs (S : Statement) (g : Nat) (G : Group) (id : Nat)
    (hG : S.groups[g]? = some G) (g' : Nat) :
    ((spent (begun S g G) id).groups[g']?).map memK = (S.groups[g']?).map memK := by
  by_cases e : g' = g
  · subst e
    rw [behind_group S g' G id hG, hG]
    rfl
  · rw [behind_group_ne S g G id g' e]

theorem behind_count (S : Statement) (g : Nat) (G : Group) (id : Nat) :
    (spent (begun S g G) id).groups.size = S.groups.size := by
  rw [behind_groups]
  unfold begun
  simp only [Array.size_modify]
  exact congrArg Array.size (OnBytes.Means.closeLedgers_groups G.members.toList S)

/-- **A yes of the closing leaves the groups' number, members and flags.** -/
theorem closing_groups {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    S'.groups.size = S.groups.size ∧
      ∀ g' : Nat, (S'.groups[g']?).map memK = (S.groups[g']?).map memK := by
  obtain ⟨G, id, -, hG, rfl⟩ := closing_st h
  exact ⟨behind_count S g G id, behind_pairs S g G id hG⟩

/-- **The claim that it hands on bears the closed group's members and flags.** -/
theorem closing_layout {P : Plan} {S S' : Statement} {g : Nat} {mask : Option Nat}
    {rs : List Fmt.RoundView} {out : SingleRows} (h : closing P S g mask rs = .ok (out, S')) :
    ∃ G, S.groups[g]? = some G ∧ out.layout.members = G.members ∧ out.layout.kept = G.kept := by
  obtain ⟨G, x, row, lay, m, rB, rE, rR, sum, eps, qs, gs, -, -, hG, -, -, hL, -, -, -, -, -, -,
    -, -, e⟩ := closing_inv2 h
  have hb : (begun S g G).groups[g]? = some { G with inRun := true, rows := #[] } :=
    behind_group S g G 0 hG
  unfold Statement.layout at hL
  rw [hb] at hL
  obtain rfl := Option.some.inj hL
  subst e
  exact ⟨G, hG, rfl, rfl⟩

/-- **The same along a yes of the frame's closing.** -/
theorem closeFrame_groups {owed : Option Nat} {f : ReqFrame} {S : Statement}
    {es : List Fmt.Entry} {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : closeFrame owed f S es rs = .ok x) :
    x.2.groups.size = S.groups.size ∧
      (∀ g' : Nat, (x.2.groups[g']?).map memK = (S.groups[g']?).map memK) ∧
      ∃ G, S.groups[f.group]? = some G ∧ x.1.rows.layout.members = G.members ∧
        x.1.rows.layout.kept = G.kept := by
  obtain ⟨Gr, rows, -, hc, e⟩ := closeFrame_lays (f' := x.1) (S' := x.2) h
  obtain ⟨G, hG, m1, m2⟩ := closing_layout hc
  refine ⟨(closing_groups hc).1, (closing_groups hc).2, G, hG, ?_, ?_⟩
  · rw [e]; exact m1
  · rw [e]; exact m2

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closeFrame_groups
#print axioms VerifiableInference.Desc.First.Close.closing_groups
#print axioms VerifiableInference.Desc.First.Close.closing_layout
