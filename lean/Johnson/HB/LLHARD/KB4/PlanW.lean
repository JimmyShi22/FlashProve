-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/PlanW.lean: the closed description WK passes the tests on the plan; and a key
file's description that has WK's chains, plans and depth, and passes its own test on the file,
passes them too.

Main names.
  WK_planOk: WK.planOk = true: the fifteen conjuncts, each from its own file (CBlocks, CDecl,
  CPlaces, CBefore, CBook, CSent), put together by the law FileDescription.planOk_of_parts
  (Johnson/AtFull/ProofPlan/PlanOkOfParts.lean). WK's fileOk is the literal true, and so is the own
  test of its shared chain's front block: neither is shown by WK_planOk.
  alike_of: PlanAlike WK (Key.descriptionFromSource X N P) (Johnson/AtFull/ProofPlan/PlanAlike.lean), from ChainPins,
  the declared rounds, the shared chain's shape as read back, and the description's own test on the
  file.
  planOk_of_fileOk: so (Key.descriptionFromSource X N P).planOk = true from these.
Limits. THE TEST ON THE FILE (fileOk: 63 named clauses and openedInBlocks) IS A PREMISE HERE. The
equations are premises. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.Frame
import Johnson.HB.LLHARD.KB4.CBlocks
import Johnson.HB.LLHARD.KB4.CDecl
import Johnson.HB.LLHARD.KB4.CPlaces
import Johnson.HB.LLHARD.KB4.CBefore
import Johnson.HB.LLHARD.KB4.CBook
import Johnson.HB.LLHARD.KB4.CSent
import Johnson.HB.LLHARD.KB8.Row
import Johnson.AtFull.ProofPlan.PlanAlike
import Johnson.AtFull.ProofPlan.PlanOkOfParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Lk6.AtPlan (keyFull)
open Johnson.KB8 (declKeyFull)

/-- **The closed description passes the tests on the plan**, with its fileOk and its shared chain's
front's own test set to the literal true. -/
theorem WK_planOk : WK.planOk = true :=
  FileDescription.planOk_of_parts WK rfl WK_first WK_shared WK_second WK_eq₁ WK_eq₂ WK_eq₃ WK_depth
    WK_labels WK_places WK_before WK_book WK_reads WK_sent WK_seal

variable {X : Source} {N : H2U.PlaceNums} {P : LaterPlaces}

theorem alike_of (h : ChainPins X N P) (hD : X.Y.D = declKeyFull)
    (hl : X.Y.k.shared.lin = keyFull.once.shape) (hf : (descriptionFromSource X N P).fileOk = true) :
    PlanAlike WK (descriptionFromSource X N P) where
  fileOk := fun _ => hf
  plans := hD.symm
  depth := (Johnson.KB8.r8'_of_lin N P hl).symm
  first := by rw [first_of h]; exact alike₂_refl _
  shared := by rw [shared_of h]; exact alike₂_refl _
  second := by rw [second_of h]; exact alike₂_refl _

/-- **The tests on the plan, from the test on the file.** -/
theorem planOk_of_fileOk (h : ChainPins X N P) (hD : X.Y.D = declKeyFull)
    (hl : X.Y.k.shared.lin = keyFull.once.shape) (hf : (descriptionFromSource X N P).fileOk = true) :
    (descriptionFromSource X N P).planOk = true :=
  FileDescription.planOk_alike₂ (alike_of h hD hl hf) WK_planOk

end Johnson.KB4

#print axioms Johnson.KB4.WK_planOk
#print axioms Johnson.KB4.alike_of
#print axioms Johnson.KB4.planOk_of_fileOk
