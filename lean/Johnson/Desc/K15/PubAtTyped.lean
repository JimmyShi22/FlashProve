-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/PubAtTyped.lean: THE CLOSED CALLER, SECOND HALF: PubAt AND OpensAt HAVE A MEMBER:
at the typed parameters frP | srP (Johnson/Desc/K15/TypedP.lean), BY LEAN's KERNEL.
  fr_early | fr_answers | fr_stages (the small twins sr_…)   the masks ride · one answer to a sample
  · the stages of the library's typed chain frC | srC ARE the stages of the test's place: each by
  «decide +kernel»
  fr_pubAt | sr_pubAt      PubAt frP frC recordRead.codes | the small twin: its fourth clause is the
  library's own fr_pub | sr_pub, at the stages in the program's form that the place's numbers give
  (two equations by the kernel)
  fr_opensAt | sr_opensAt  OpensAt: the batching's round opens nothing (kernel); OpensAre by
  opensAre_of_B (Johnson/Desc/K15/OpensB.lean) at the test opensB's yes (kernel)
SO THE THEOREMS OF Johnson/Desc/K15/HsemAt.lean ARE NOT EMPTY FOR WANT OF A P: at P := frP | srP all
five premises on P are met (samples = 1 · P.S · P.codes by rfl).
NOT SHOWN HERE: that the P that RUNS (p15Of c of the public files) is frP | srP: at the full size a
law in scope (Johnson/Goal/Conditions/LinkTypedAtLines.lean: inScope_typed); at the small example
evaluated, no theorem; and that «written … run» says yes to any transcript.
-/
import Johnson.Desc.K15.TypedP
import Johnson.Desc.K15.HsemAt
import Johnson.Desc.K15.OpensB

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open OnBytes.Params (recordRead smallRecordRead)
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem sr_early : (p12Of srP).early = true := by decide +kernel
theorem sr_answers : (p12Of srP).answers = 1 := by decide +kernel
theorem sr_stages : stagesOf srC = (p12Of srP).nums.stages := by decide +kernel
theorem fr_early : (p12Of frP).early = true := by decide +kernel
theorem fr_answers : (p12Of frP).answers = 1 := by decide +kernel
theorem fr_stages : stagesOf frC = (p12Of frP).nums.stages := by decide +kernel

theorem sr_pubAt : PubAt srP srC smallRecordRead.codes := by
  refine ⟨sr_early, sr_answers, sr_stages, ?_⟩
  intro first rest cu restI e1 e2 e3
  have h1 : stageAt (p12Of srP) 0 ((p12Of srP).nums.stages.headD default) = some srSt1 := by
    decide +kernel
  have h2 : stagesAt (p12Of srP) 1 (p12Of srP).nums.stages.tail = some srRest := by decide +kernel
  rw [e1] at h1 h2
  obtain rfl : cu = srSt1 := Option.some.inj (e2.symm.trans h1)
  obtain rfl : restI = srRest := Option.some.inj (e3.symm.trans h2)
  exact sr_pub

theorem sr_opensAt : OpensAt srP srC := by
  refine ⟨by decide +kernel, opensAre_of_B _ _ _ ?_⟩
  rw [sr_stages]
  decide +kernel

theorem fr_pubAt : PubAt frP frC recordRead.codes := by
  refine ⟨fr_early, fr_answers, fr_stages, ?_⟩
  intro first rest cu restI e1 e2 e3
  have h1 : stageAt (p12Of frP) 0 ((p12Of frP).nums.stages.headD default) = some frSt1 := by
    decide +kernel
  have h2 : stagesAt (p12Of frP) 1 (p12Of frP).nums.stages.tail = some frRest := by decide +kernel
  rw [e1] at h1 h2
  obtain rfl : cu = frSt1 := Option.some.inj (e2.symm.trans h1)
  obtain rfl : restI = frRest := Option.some.inj (e3.symm.trans h2)
  exact fr_pub

theorem fr_opensAt : OpensAt frP frC := by
  refine ⟨by decide +kernel, opensAre_of_B _ _ _ ?_⟩
  rw [fr_stages]
  decide +kernel

end Desc.K15

#print axioms Desc.K15.sr_pubAt
#print axioms Desc.K15.sr_opensAt
#print axioms Desc.K15.fr_pubAt
#print axioms Desc.K15.fr_opensAt
