-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TailBack.lean: THE COEFFICIENT DRAWN IN THE SUMCHECK OF THE TERMS, READ OFF
THE CHAIN's LAST STATEMENT `TailH.z7` (OnBytes/Tie/Pv/Lay/OwnTieL.lean), IS THE READING OF THE WORD
HEARD. Three statements and their proofs.

  `ch4_run_z7`: under `TailH.Claims`: the chain from the draw that combines on, run from `z3`, ends
    in `z7`.
  `back4_z7`: so the statement in front of that draw, inside `z7` (`Ch.back`, Cb/Pv/Att/Chain.lean),
    is `z3`.
  `eps3_z7`: its output's eps is the reading of the third sumcheck's word eps. This is the number of
    which `LayVO.epsOK` (Cb/Pv/Lay/OwnTest.lean) says that it is not 0.

NO NEW ARGUMENT: `stage_run` (TailRun.lean) four times; `Ch.back_run` (Cb/Pv/Att/ChainLast.lean).

Limits. `TailH.Claims` is a premise. No routine, no tape, no text. Nothing on soundness.

-/
import OnBytes.Desc.First.P1.TailRun

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Lay.Eng

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {M : Type}

theorem ch4_run_z7 {X : Type} (T : LayTail K M X) (D : TailH ρ T) (x : X) (h : D.Claims x) :
    T.ch4.run (D.z3 x) D.t4 = D.z7 x :=
  (stage_run ρ T.s4 D.d4 T.ow4 T.ch5 (D.y4 x) D.t5 h.c4).trans
  ((stage_run ρ T.s5 D.d5 T.ow5 (.draw (dE K) 1 T.p5 (.draw (dPt K T.gR) T.eR T.pR T.ch6))
    (D.z4 x) (ρ.val D.x5, (D.rR, D.t6)) h.c5).trans
  ((stage_run ρ T.s6 D.d6 T.ow6 (.draw (dE K) 1 T.p6 T.chW) (D.y6 x) (ρ.val D.x6, D.tW)
    h.c6).trans
  (stage_run ρ T.s7 D.d7 T.s7.Out (.done _) (D.y7 x) () h.c7)))

theorem back4_z7 {X : Type} (T : LayTail K M X) (D : TailH ρ T) (x : X) (h : D.Claims x) :
    T.ch4.back (D.z7 x) = D.z3 x := by
  rw [← ch4_run_z7 ρ T D x h]
  exact Ch.back_run T.ch4 _ _

/-- **The coefficient of the terms' sumcheck, read off the last statement.** -/
theorem eps3_z7 {X : Type} (T : LayTail K M X) (D : TailH ρ T) (x : X) (h : D.Claims x) :
    (T.ch4.back (D.z7 x)).2.eps = ρ.val D.d3.H.eps := by
  rw [back4_z7 ρ T D x h]
  rfl

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.ch4_run_z7
#print axioms OnBytes.Desc.First.P1.back4_z7
#print axioms OnBytes.Desc.First.P1.eps3_z7
