-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CDecl.lean: conjuncts 5 to 9 and 13 of the tests on the plan at WK: the
blocks' rounds in a row are the plans; every stored part that is opened has the depth 32; labelsOk;
readsOk. The last three by evaluations in Lean's kernel at the written declared rounds, each with a
negative test.
Limits. At the closed description WK (WK.lean) and the written declared rounds alone. That a key
file's description passes the test at any public files is another file's, under named equations.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK
import Johnson.HB.LLHARD.KB4.AtDecl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

theorem WK_eq₁ : (WK.roundsDeclaredByBlocks.1 == WK.plans.1) = true := by
  rw [WK_decl₁]
  exact beq_self_eq_true _

theorem WK_eq₂ : (WK.roundsDeclaredByBlocks.2.1 == WK.plans.2.1) = true := by
  rw [WK_decl₂]
  exact beq_self_eq_true _

theorem WK_eq₃ : (WK.roundsDeclaredByBlocks.2.2 == WK.plans.2.2) = true := by
  rw [WK_decl₃]
  exact beq_self_eq_true _

set_option maxRecDepth 1000000 in
theorem depth_full : depthAt declKeyFull 32 = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem depth_bent : depthAt declKeyFull 31 = false := by decide +kernel

theorem WK_depth : ((WK.roundsDeclaredByBlocks.1 ++ WK.roundsDeclaredByBlocks.2.1 ++ WK.roundsDeclaredByBlocks.2.2).all
    (fun r => r.stored.all (·.sh.a == WK.tableDepth))) = true := by
  rw [WK_decl]
  exact depth_full

set_option maxRecDepth 1000000 in
theorem labels_full : labelsAt declKeyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem labels_bent : labelsAt (declKeyFull.2.1, declKeyFull.2.1, declKeyFull.2.2) = false := by
  decide +kernel

theorem WK_labels : WK.labelsOk = true := by
  rw [labelsOk_at, WK_decl]
  exact labels_full

set_option maxRecDepth 1000000 in
theorem reads_full : readsAt declKeyFull = true := by decide +kernel

set_option maxRecDepth 1000000 in
theorem reads_bent : readsAt (declKeyFull.1, declKeyFull.2.1,
    { entry := { name := "CS", poss := 1 } } :: declKeyFull.2.2) = false := by decide +kernel

theorem WK_reads : WK.readsOk = true := by
  rw [readsOk_at, WK_decl]
  exact reads_full

end Johnson.KB4

#print axioms Johnson.KB4.WK_eq₁
#print axioms Johnson.KB4.WK_eq₂
#print axioms Johnson.KB4.WK_eq₃
#print axioms Johnson.KB4.depth_full
#print axioms Johnson.KB4.depth_bent
#print axioms Johnson.KB4.WK_depth
#print axioms Johnson.KB4.labels_full
#print axioms Johnson.KB4.labels_bent
#print axioms Johnson.KB4.WK_labels
#print axioms Johnson.KB4.reads_full
#print axioms Johnson.KB4.reads_bent
#print axioms Johnson.KB4.WK_reads
