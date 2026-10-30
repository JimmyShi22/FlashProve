-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyFenceB.lean: THE FENCE ON THE ROWS' CONTENT (SampleIn | OpenIn, Johnson/RunOne/KeyHanded.lean; Means.RowIn, Johnson/Desc/Means/Says.lean) AS BOOLS, so that a run can show the two Prop clauses of the table's promise (KeyRows1At.free₁) met at a state; AND THE TIE: the Bool's yes GIVES the Prop.
  sampleInB S o up · openInB S g bare   (up | bare: controls: at 0 | false they are the fence): OVER rowInB | rowInB_iff (KeyHanded.lean)
  sampleIn_of_B · openIn_of_B   **PROVED**
Nothing on soundness.
-/
import Johnson.RunOne.KeyHanded

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes

/-- up: a control: the one-member group names the message that much higher. -/
def sampleInB (S : Statement) (o up : Nat) : Bool := (S.oracles[o]?).all fun y => y.sampleRows.toList.all fun r => rowInB S { code := 0, members := #[o + up] } r

theorem sampleIn_of_B (S : Statement) (o : Nat) (h : sampleInB S o 0 = true) : SampleIn S o := by
  intro y hy r hr
  unfold sampleInB at h
  rw [hy] at h
  exact (rowInB_iff S _ r).1 (List.all_eq_true.1 h r hr)

/-- bare: a control: the group's members struck. -/
def openInB (S : Statement) (g : Nat) (bare : Bool) : Bool := (S.groups[g]?).all fun G => G.rows.toList.all fun r => rowInB S (if bare then { G with members := #[] } else G) r

theorem openIn_of_B (S : Statement) (g : Nat) (h : openInB S g false = true) : OpenIn S g := by
  intro G hG r hr
  unfold openInB at h
  rw [hG] at h
  exact (rowInB_iff S G r).1 (List.all_eq_true.1 h r hr)

/-- Means.GroupOk's five clauses as one Bool (the tie: KeyFenceOrder.lean). -/
def groupOkB (S : Statement) (G : Group) : Bool :=
  decide G.members.toList.Nodup && (G.members.toList.all fun o => decide (o < S.oracles.size)) && G.kept.size == G.members.size &&
    (G.members.toList.all fun o => (S.oracles[o]?).all fun x => (x.shape.mainRows == 0 || x.shape.code == G.code) && (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode))

/-- Means.InOrder as one Bool: every group in order, every open row RowIn at its group, every sample row on its own message. bare: a control: every group's members struck. -/
def inOrderB (S : Statement) (bare : Bool) : Bool :=
  ((List.range S.groups.size).all fun g => (S.groups[g]?).all fun G => groupOkB S G && G.rows.toList.all fun r => rowInB S (if bare then { G with members := #[] } else G) r) &&
    (List.range S.oracles.size).all fun o => sampleInB S o 0

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.sampleIn_of_B
#print axioms Johnson.RunOne.KeyRows23.openIn_of_B
