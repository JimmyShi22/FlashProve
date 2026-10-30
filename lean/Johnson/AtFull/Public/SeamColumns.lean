-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/SeamColumns.lean: AT THE FULL SIZE THE MATRICES OF EACH ATTENTION's PLAN's
SMALLNESS TEST HAVE 10248 COLUMNS IN ALL (HTailF2.foldColumns, OnBytes/Model/Tail.lean). Small
laws; nothing is evaluated here.

  `columns_of_small`: where smallSize tl is the written smallA
    (Johnson/AtFull/Rows/ArmsOfFields.lean), tl.foldColumns = 10248: one projection.
  `seam_columns_of_B`: where the test attB (Johnson/AtFull/Public/AtWitnesses.lean) accepts an array
    of attention's plans, each MEMBER of it has that sum (the array has twelve members, and the
    test speaks of the member at each g below 12).
  **`seam_columns_at`**: under OpensAt and Makers: each member of the witnesses' attention's plans
    has that sum: from the closed fact arms_W (Johnson/AtFull/Public/ArmsAtMakers.lean).
  **`seam_columns_of_arms`**: GENERAL IN X: profile 4 · twelve groups · armsB X = true
    (Johnson/LPFE1R/RowsAtArms.lean) · twelve attention's plans ⊢ each member of X.A has that sum.
    These four premises are conjuncts of publicOfO_zFull_all's conclusion
    (Johnson/AtFull/Public/AtX0All.lean: PubFull's p4 and groups · armsB · the size): so it speaks
    of that X₀ without another walk of the join.

Limits. OpensAt and Makers are premises, as in AtWitnesses.lean. The full size, at the stored free
numbers alone: nothing in the goals' scope. 10248 is the written smallA's; whence that is, is its
file's to say. Nothing on soundness.

-/
import Johnson.AtFull.Public.ArmsAtMakers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Public

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Road.K4.Trial.AttL2 (AOf)
open VerifiableInference.Desc.LinkJoin (Arm armsB arm_at armOf armAtW)
open _root_.AtFull.Rows (lookA ownA smallA armOf_two attArm attArm_of written_attention)

/-- One projection. -/
theorem columns_of_small {tl : HTailF2} (h : smallSize tl = smallA) : tl.foldColumns = 10248 :=
  congrArg Params.SmallSize.columns h

/-- Each member of an array that attB accepts. -/
theorem seam_columns_of_B {A : Array Attention.Plan} (h : attB A = true) :
    ∀ a ∈ A, a.seam.tl.foldColumns = 10248 := by
  obtain ⟨sA, hA⟩ := att_of_B h
  intro a ha
  obtain ⟨i, hi, e⟩ := Array.mem_iff_getElem.1 ha
  obtain ⟨a', e0, -, -, e3, -⟩ := hA i (by omega)
  rw [Array.getElem?_eq_getElem hi, e] at e0
  obtain rfl : a = a' := Option.some.inj e0
  exact columns_of_small e3

variable {y : Layer.Lay} {sc : Layer.Scales} {wsLay : WsLay} {rope : Array Nat}
  {l : List Attention.Line} {ps : List Attention.Plan} {layers : Layer.Pub}
  {G : Array Layer.HPlan2} {seenA : Array SubPlan}

/-- **Each member of the witnesses' attention's plans**, under OpensAt and Makers. -/
theorem seam_columns_at (O : OpensAt y) (M : Makers y sc wsLay rope l ps layers G seenA) :
    ∀ a ∈ AOf ps.toArray seenA, a.seam.tl.foldColumns = 10248 := by
  have h := at_witnesses O M arms_W
  rw [Bool.and_eq_true] at h
  exact seam_columns_of_B h.2

/-- **Each member of X.A, at every public part X of profile 4 with twelve groups, the written arms
and twelve attention's plans.** -/
theorem seam_columns_of_arms {X : Public} (h4 : X.p4 = true) (hN : X.NGr = 12)
    (ha : armsB X = true) (hA : X.A.size = 12) : ∀ a ∈ X.A, a.seam.tl.foldColumns = 10248 := by
  intro a hm
  obtain ⟨g, hg, e⟩ := Array.mem_iff_getElem.1 hm
  have hg' : g < 12 := by omega
  have e0 : X.A[g]? = some a := by rw [Array.getElem?_eq_getElem hg, e]
  have h1 := arm_at ha (2 * g + 1) (by omega)
  rw [armOf_two h4, hN, if_neg (fun h => by have := beq_iff_eq.1 h; omega),
    if_neg (fun h => by have := beq_iff_eq.1 h; omega),
    show (2 * g + 1) / 2 = g by omega, attArm_of e0 rfl rfl rfl,
    ← written_attention g hg'] at h1
  exact columns_of_small (Arm.attention.inj h1).2.2

end Johnson.AtFull.Public

#print axioms Johnson.AtFull.Public.columns_of_small
#print axioms Johnson.AtFull.Public.seam_columns_of_B
#print axioms Johnson.AtFull.Public.seam_columns_at
#print axioms Johnson.AtFull.Public.seam_columns_of_arms
