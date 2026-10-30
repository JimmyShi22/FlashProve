-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K14/Law/LedgerMembersTrees.lean: share_seamed's htree2 | htree5 AT THE MEMBERS OF
Johnson/Desc/K14/Law/LedgerMembersAt.lean: each member's tree is one of the trees that its sending's
first written round tells. From two equations on the sending's piece (its base; how many trees its
first round tells) and the layout's own law (a message's tree lies among the layout's shapes).

  htree_two       at "send o_u": every member of memK2 sits at o_u's seat (the mask's made member
                  too).
  htree_five      at "send o_omega": o_omega's and o_sp's seats.
What is not claimed. No soundness; no level.

-/
import Johnson.Desc.K14.Law.LedgerMembersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open VerifiableInference.Desc.K1 (shapesOf shapeAt sampledAt)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open Desc.K14.Law.Fence

variable (Q : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (lo : ℕ) (rad2 rad5 : ℕ → ℕ)

theorem htree_two (hlU : layTrees Q.codes sentU = some layU) (hU : 0 < sentU.size) (base2 T : ℕ)
    (hb : base2 = lo) (hT : T = layU.shapes.size) :
    ∀ k, ∃ j, ((memK2 Q sentU layU layO lo rad2 rad5 k).1.seat
      (memK2 Q sentU layU layO lo rad2 rad5 k).2).1 = base2 + j ∧ j < T := by
  intro k
  refine ⟨layU.tree.getD 0 0, ?_, by rw [hT]; exact OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlU hU⟩
  rw [hb]
  unfold memK2
  by_cases h : k.val = 0
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    rfl

theorem htree_five (hS : Q.S.sharedSplitNeeded = true)
    (hlO : layTrees Q.codes (withOmega Q.S) = some layO) (base5 T : ℕ)
    (hb : base5 = lo + layU.shapes.size) (hT : T = layO.shapes.size) :
    ∀ k, ∃ j, ((memK5 Q layU layO lo rad2 rad5 k).1.seat
      (memK5 Q layU layO lo rad2 rad5 k).2).1 = base5 + j ∧ j < T := by
  have hsz := sizeOmega Q.S hS
  have hlen : (shapesOf (parO Q)).length = 2 := by
    rw [(lengths Q #[]).2, hsz]
  intro k
  obtain ⟨kv, hkv⟩ := k
  rw [hb, hT]
  unfold memK5
  by_cases h : kv = 0
  · subst h
    exact ⟨layO.tree.getD 0 0, by rw [if_pos rfl]; rfl,
      OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO (by rw [hsz]; decide)⟩
  · obtain rfl : kv = 1 := by omega
    exact ⟨layO.tree.getD 1 0, by rw [if_neg Nat.one_ne_zero]; rfl,
      OnBytes.Tie.Pv.Keeps.Fit.lay_lt hlO (by rw [hsz]; decide)⟩

end Desc.K14.Law

#print axioms Desc.K14.Law.htree_two
#print axioms Desc.K14.Law.htree_five
