-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TailRun.lean: THE LAST STATEMENT OF THE CHAIN OF A LAYERS' SUB-PROOF'S OWN
ROUNDS, ON THE TRANSCRIPT THAT IS MADE FROM WHAT WAS HEARD, WRITTEN OUT.
OnBytes/Tie/Pv/Lay/OwnTieL.lean names the statements that the stages find (`TailH.y1` … `TailH.z7`)
and unfolds what the chain OWES on that transcript (`tail_owed`, `own_last`). Here: the chain's run
(`Ch.run`, Cb/Pv/Att/ChainRun.lean) ENDS IN `TailH.z7`. Three statements and their proofs.

  `stage_run`: a sumcheck's stage, under `StgH.Claim`: the run goes on from `StgH.nx`.
  `tail_run_z7`: under `TailH.Claims`: `T.ch.run x D.trs = D.z7 x`.
  `own_run_z7`: a sub-proof that is not the first: `A.ch.run x (ownTrs A pT D) = D.z7 (x, the token
    point read)`. `own_run_z7F`: the first sub-proof, with its two further points.

NO NEW ARGUMENT: `owed_stage`'s own unfolding, seven times.

Limits. Those of OwnTieL.lean: `TailH.Claims` is a premise, and it is the bridge: each letter's
claim at the statement that its stage finds is (the reading of the stage's target, its state). No
routine, no tape, no text occurs here. Nothing on soundness.
-/
import OnBytes.Tie.Pv.Lay.OwnTieL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Iop Prob Cb TWhole OnBytes OnBytes.Model Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay
open OnBytes.Tie.Pv.Lay.Eng

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K) {M : Type}

/-- A sumcheck's stage: the run goes on from the statement behind the stage. -/
theorem stage_run {X : Type} (S : Stg K M X) (D : StgH ρ S) (Ow : S.Nx → M → Prop)
    (next : Ch K M S.Nx) (x : X) (ts : next.Trs) (h : D.Claim x) :
    (S.stage Ow next).run x (D.tr, ts) = next.run (D.nx x) ts := by
  show next.run ((x, D.rd), shortV S.L.T.par S.F (S.cl x D.rd) (unrideN S.L.T.par S.n D.tr)) ts =
    _
  rw [show S.cl x D.rd = (ρ.val D.t, D.st) from h]
  rfl

/-- **The chain from the limbs' scalars on ends in `z7`.** -/
theorem tail_run_z7 {X : Type} (T : LayTail K M X) (D : TailH ρ T) (x : X) (h : D.Claims x) :
    T.ch.run x D.trs = D.z7 x :=
  (stage_run ρ T.s1 D.d1 T.ow1 (.draw (dE K) 1 T.p1 T.chP) (D.y1 x) (ρ.val D.x1, D.tP) h.c1).trans
  ((stage_run ρ T.s2 D.d2 T.ow2 (T.s3.stage T.ow3 T.ch4) (D.y2 x) (D.d3.tr, D.t4) h.c2).trans
  ((stage_run ρ T.s3 D.d3 T.ow3 T.ch4 (D.z2 x) D.t4 h.c3).trans
  ((stage_run ρ T.s4 D.d4 T.ow4 T.ch5 (D.y4 x) D.t5 h.c4).trans
  ((stage_run ρ T.s5 D.d5 T.ow5 (.draw (dE K) 1 T.p5 (.draw (dPt K T.gR) T.eR T.pR T.ch6))
    (D.z4 x) (ρ.val D.x5, (D.rR, D.t6)) h.c5).trans
  ((stage_run ρ T.s6 D.d6 T.ow6 (.draw (dE K) 1 T.p6 T.chW) (D.y6 x) (ρ.val D.x6, D.tW)
    h.c6).trans
  (stage_run ρ T.s7 D.d7 T.s7.Out (.done _) (D.y7 x) () h.c7))))))

variable {ρ}

/-- A sub-proof that is not the first. -/
theorem own_run_z7 {X : Type} (A : LayOwn K M X) (pT : List E) (D : TailH ρ A.tail) (x : X)
    (h : D.Claims (x, Johnson.L5.Layers.rd ρ A.gT pT)) :
    A.ch.run x (ownTrs A pT D) = D.z7 (x, Johnson.L5.Layers.rd ρ A.gT pT) :=
  tail_run_z7 ρ A.tail D _ h

/-- The first sub-proof. -/
theorem own_run_z7F {X : Type} (A : LayOwnFirst K M X) (pT pA pB : List E) (D : TailH ρ A.tail)
    (x : X)
    (h : D.Claims (((x, Johnson.L5.Layers.rd ρ A.gT pT), Johnson.L5.Layers.rd ρ A.gA pA),
      Johnson.L5.Layers.rd ρ A.gB pB)) :
    A.ch.run x (ownTrsF A pT pA pB D) =
      D.z7 (((x, Johnson.L5.Layers.rd ρ A.gT pT), Johnson.L5.Layers.rd ρ A.gA pA),
        Johnson.L5.Layers.rd ρ A.gB pB) :=
  tail_run_z7 ρ A.tail D _ h

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.tail_run_z7
#print axioms OnBytes.Desc.First.P1.own_run_z7
#print axioms OnBytes.Desc.First.P1.own_run_z7F
