-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/WK.lean: a closed description of a key file's protocol at the full size, for
the tests on the plan: its three chains are the texts of the library's own routines at written
values (Chains.lean), the first with the two lookups' rounds written off the planner's plain list
(FirstW.lean, where an equation ties it to Key.firstChain); its plans are the written declared
rounds; its depth is 32. Definitions, and three closed equations.

What it is for. The tests on the plan (FileDescription.planOk, Johnson/Desc/Block.lean) read of a
description its three chains' blocks, plans, tableDepth and fileOk. WK holds these at written
values, so that each test is a closed question for Lean's kernel. A law (another file) carries a yes
from WK to Key.descriptionFromSource X N P under named equations on X, N and P.

Main names.
  WK: the description. fileOk is the literal true: the key file's test on the file is no matter of
  this term. Its instance, starts, last test, and its tables wanted and owed are idle stand-ins.
  The shared chain's front block's own test is the literal true in WK (sharedFull, Chains.lean):
  that a key file's description's front says yes is earned elsewhere (front_W, CFile.lean; front_of,
  Pins.lean).
  WK_decl₁, WK_decl₂, WK_decl₃, WK_decl: its blocks' rounds in a row are the written declared rounds
  (KB8.declKeyFull): by the test == in Lean's kernel. Negative tests: at each chain, with
  one row more at a proximity test's batching, the blocks' rounds are not the written ones.
Limits. WK is no verifier: its starts and last test are stand-ins. Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.FirstW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

/-- **The closed description.** -/
def WK : FileDescription (FirstState × _root_.Desc.K14.St) :=
  { S₁ := FirstState, S₂ := _root_.Desc.K14.St, S₃ := VerifiableInference.Desc.Third.S₃
    Cl := Claim, plans := declKeyFull, tableDepth := 32, wanted := [], owed := [], fileOk := true
    okStart := fun _ => true, XiPub := FirstState × _root_.Desc.K14.St, pub := id
    start₁ := (·.1), start₂ := (·.2), start₃ := fun _ _ _ => .error "a stand-in"
    first := firstW, shared := sharedFull, second := thirdFull, fin := fun _ _ _ _ => true }

set_option maxRecDepth 1000000 in
theorem WK_decl₁ : WK.roundsDeclaredByBlocks.1 = declKeyFull.1 := eq_of_beq (by decide +kernel)

theorem WK_decl₂ : WK.roundsDeclaredByBlocks.2.1 = declKeyFull.2.1 := eq_of_beq (by decide +kernel)

theorem WK_decl₃ : WK.roundsDeclaredByBlocks.2.2 = declKeyFull.2.2 := eq_of_beq (by decide +kernel)

/-- A place's numbers with one row more at the batching. -/
def oneRowMore (x : H2U.PlaceNums) : H2U.PlaceNums :=
  { x with nums := { x.nums with rows := x.nums.rows + 1 } }

set_option maxRecDepth 1000000 in
theorem WK_decl₁_bent : ((firstChainL (lookLinks lookE oneFull Lk6.AtPlan.keyFull.set) oneFull
    declKeyFull.1 toldKeyFull.1 (oneRowMore Johnson.KB8.rangesNumsFull)).blocksInOrder.flatMap (·.rounds) ==
      declKeyFull.1) = false := by decide +kernel

theorem WK_decl₂_bent : (((sharedZ Lk6.AtPlan.keyFull true { Johnson.KB8.laterPlacesFull with
    U := oneRowMore Johnson.KB8.laterPlacesFull.U }).retype : Chain _ Claim).blocksInOrder.flatMap
      (·.rounds) == declKeyFull.2.1) = false := by decide +kernel

theorem WK_decl₃_bent : (((thirdZ Lk6.AtPlan.keyFull { Johnson.KB8.laterPlacesFull with
    W := oneRowMore Johnson.KB8.laterPlacesFull.W }).retype : Chain _ Claim).blocksInOrder.flatMap
      (·.rounds) == declKeyFull.2.2) = false := by decide +kernel

theorem WK_decl : WK.roundsDeclaredByBlocks = declKeyFull :=
  Prod.ext WK_decl₁ (Prod.ext WK_decl₂ WK_decl₃)

end Johnson.KB4

#print axioms Johnson.KB4.WK_decl₁
#print axioms Johnson.KB4.WK_decl₂
#print axioms Johnson.KB4.WK_decl₃
#print axioms Johnson.KB4.WK_decl₁_bent
#print axioms Johnson.KB4.WK_decl₂_bent
#print axioms Johnson.KB4.WK_decl₃_bent
#print axioms Johnson.KB4.WK_decl
