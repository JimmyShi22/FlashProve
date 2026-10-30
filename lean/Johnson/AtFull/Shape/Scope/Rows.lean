-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/Rows.lean: THE FOURTEEN PLACES OF A LINK, FROM THE SORTS' LAWS, IN THE FORM
THAT steps_rel (Scope/Join.lean) ASKS. A joining; nothing is evaluated.

* link_rel: at every link below 24 and every place: the even links' places by LayerCells.lean, the
  plain places by PlainCells.lean, the attention links' lookups by AttLookSteps.lean, their own
  rounds by AttSorts.lean, their reads by ReadsAtt.lean, their batching by BatchAtt.lean, behind the
  batching by AttEnds.lean.
* cells_rel: all 358 members, with the head's link by HeadLink.lean and ReadsSorts.lean, the front
  and the five behind by PlainCells.lean.

Limits. X and X₀ are what publicOfO returns at some files and at the stored ones, and meet SameRead.
Nothing on soundness, completeness or hiding.
-/
import Johnson.AtFull.Shape.Scope.LayerCells
import Johnson.AtFull.Shape.Scope.PlainCells
import Johnson.AtFull.Shape.Scope.AttLookSteps
import Johnson.AtFull.Shape.Scope.AttEnds
import Johnson.AtFull.Shape.Scope.AttSorts
import Johnson.AtFull.Shape.Scope.ReadsAtt
import Johnson.AtFull.Shape.Scope.ReadsSorts
import Johnson.AtFull.Shape.Scope.HeadLink
import Johnson.AtFull.Shape.Scope.BatchAtt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.Scope
open OnBytes OnBytes.Model
open VerifiableInference.PlanWritten (publicOfO)

variable {X X₀ : Verify.Public}

/-- **THE PLACES OF A LINK.** -/
theorem link_rel (S : SameRead X X₀) {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : publicOfO OnBytes.secondHashFunction pol KL lay = .ok X)
    (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (l j : Nat) (hl : l < 24) (hj : j < 14) :
    CellRel X X₀ (14 * l + j + 1) ((TabL.linkRow (LW X) l).at j) ((TabL.linkRow (LW X₀) l).at j) := by
  rcases Nat.mod_two_eq_zero_or_one l with he | ho
  · match j, hj with
    | 0, _ => exact laid_rel hl
    | 1, _ => exact first_rel S hl
    | 2, _ => exact lookCalls_rel he hl S h₀
    | 3, _ => exact own_rel he hl S
    | 4, _ => exact reads_rel he hl S
    | 5, _ => exact draw_rel S hl
    | 6, _ => exact digits_rel S hl
    | 7, _ => exact lookDigits_rel he hl S h₀
    | 8, _ => exact batch_rel he hl S
    | 9, _ => exact behind_rel he hl S
    | 10, _ => exact equation_rel hl
    | 11, _ => exact close_rel hl
    | 12, _ => exact shut_rel hl
    | 13, _ => exact cleared_rel S l
  · match j, hj with
    | 0, _ => exact laid_rel hl
    | 1, _ => exact first_rel S hl
    | 2, _ => exact lookCalls_cell S hl ho
    | 3, _ => exact own_cell_att S hl ho
    | 4, _ => exact reads_att_rel S hl ho
    | 5, _ => exact draw_rel S hl
    | 6, _ => exact digits_rel S hl
    | 7, _ => exact lookDigits_cell S hl ho
    | 8, _ => exact batch_att_rel S hX h₀ hl ho
    | 9, _ => exact Ends.behind_att_rel S hl ho
    | 10, _ => exact equation_rel hl
    | 11, _ => exact close_rel hl
    | 12, _ => exact shut_rel hl
    | 13, _ => exact cleared_rel S l

/-- **ALL 358 MEMBERS.** -/
theorem cells_rel (S : SameRead X X₀) {pol KL : ByteArray} {lay : Option ByteArray}
    (hX : publicOfO OnBytes.secondHashFunction pol KL lay = .ok X)
    (h₀ : publicOfO OnBytes.secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok X₀)
    (n : Nat) (hn : n < 358) :
    CellRel X X₀ n (TabL.cells (LW X) n) (TabL.cells (LW X₀) n) :=
  steps_rel front_rel (link_rel S hX h₀)
    (head_rel S (step_of_return h₀) (reads_head_first S)) (back_rel S) n hn

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.link_rel
#print axioms Johnson.AtFull.Shape.Scope.cells_rel
