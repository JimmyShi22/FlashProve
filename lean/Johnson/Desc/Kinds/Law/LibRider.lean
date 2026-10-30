-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibRider.lean: THE LEDGER's TWO LINES AT EVERY POSITION, IN THE LIBRARY's OWN WORDS (Inst.Model.Head.dB4, dZ: the third of the five clauses on the output head from which the goals' "Means" follows), OVER THE BASE FIELD, AT THE LIBRARY's RECORD MADE OF OUR CELLS (cellsN c): FROM THE TWO GUESTS' CORNER VALUES IN K6's FILES (HeadLaw.lean: clipAt, tableAt at the corner of each
position) BEING 0, ALONE: STATED AND PROVED.
  lib_dB4 · lib_dZ · lib_lines
THE ARITHMETIC IS NOT THIS FILE's: every identity between the library's expressions and ours is CALLED from Law/LibJoin.lean | Law/LibJoinNorm.lean, which are ported whole from texts of this project that are not in this repository, as their heads say.
WHAT IT DOES NOT SAY. **THE PREMISE IS NOT WHAT K6's LAW CLOSES**: Law/RowFront.lean's FrontRider is ONE SUM of the corner values under the weights of the lookup's point on the positions: that each corner value is 0 follows only with the lookup's rider's law (a drawn point; other files' to show). So this file carries that law's conclusion to the library's letters and no more. Same Y,
Wide (d = 5120 · V = JV = 202048: NO PADDING · F = 24 · a block's size divides 64) and the tests on the plan (PlanFacts) are premises. FULL SIZE ALONE. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.LibIdn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open OnBytes (E)
open Inst.Model.Head (Req nT dB4 dZ)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide cellsN)
open Norm (lt ls d lPd S2 T)

variable [Sizes] [Policy] [Request] [Token] {c : NCells} {Y : Req}

/-- (B4) at every position. -/
theorem lib_dB4 (S : Same Y) (h : ∀ i, i < T → clipAt c.toCells (corner 0 i) = 0) :
    ∀ i < nT, dB4 ((cellsN c).cast Cb.Gl.F) Y i = 0 := by
  intro i hi
  have hi' : i < T := by rw [S.T]; exact hi
  have h1 := congrArg rd (h i hi')
  rw [rd_clip hi', rd_zero] at h1
  refine (Inst.Model.Head.map_dB4 (Int.castRingHom Cb.Gl.F) (cellsN c) Y i).symm.trans ?_
  rw [show dB4 (cellsN c) Y i = _ from HeadJoin.dB4_int (c := c.toCells) (X := c.stream) S i]
  by_cases hc : costed i = true
  · rw [if_pos hc] at h1 ⊢
    exact baseZero h1
  · rw [if_neg hc]
    simp

/-- (Z) at every position. -/
theorem lib_dZ (S : Same Y) (Wd : Wide) (P : PlanFacts)
    (h : ∀ i, i < T → tableAt c.toCells (corner 0 i) = 0) :
    ∀ i < nT, dZ ((cellsN c).cast Cb.Gl.F) Y i = 0 := by
  intro i hi
  have hi' : i < T := by rw [S.T]; exact hi
  have h1 := congrArg rd (h i hi')
  rw [rd_table P hi', rd_zero] at h1
  refine (Inst.Model.Head.map_dZ (Int.castRingHom Cb.Gl.F) (cellsN c) Y i).symm.trans ?_
  rw [show dZ (cellsN c) Y i = _ from HeadJoin.dZ_int (c := c.toCells) (X := c.stream) S Wd i]
  by_cases hc : costed i = true
  · rw [if_pos hc] at h1 ⊢
    exact baseZero h1
  · rw [if_neg hc]
    simp

/-- **THE LEDGER's TWO LINES AT EVERY POSITION.** -/
theorem lib_lines (S : Same Y) (Wd : Wide) (P : PlanFacts)
    (h : ∀ i, i < T → clipAt c.toCells (corner 0 i) = 0 ∧ tableAt c.toCells (corner 0 i) = 0) :
    ∀ i < nT, dB4 ((cellsN c).cast Cb.Gl.F) Y i = 0 ∧ dZ ((cellsN c).cast Cb.Gl.F) Y i = 0 :=
  fun i hi => ⟨lib_dB4 S (fun j hj => (h j hj).1) i hi, lib_dZ S Wd P (fun j hj => (h j hj).2) i hi⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.lib_lines
