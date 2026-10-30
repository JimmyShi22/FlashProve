-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/LookR.lean: THE SENTENCE ON WHAT THE LOOKUP ON THE CALLS RETURNED THAT AN
ATTENTION LINK's FOUR RUNS OF CLAIMS SPEND OF IT ON VALUES, AS ONE TERM AT THE PLAN's LETTERS; and
the facts on the plan alone that stand beside it. Two definitions; no theorem. OVER THE LIBRARY
ALONE: so that whoever lays the sentence, whoever keeps it and whoever spends it can import one
text.

Main names:
  `lookR A o`   **the sentence**: something is laid, and its key points follow the lookup's own rule
    (K3Pts, Johnson/Desc/First/Att/K05LookAll.lean): zx has dT coordinates, zy rK, and the key point
    of call q is a cut of zy, then zx
  `PlanR A r1 r2 u1 u2 wl ix wh`   the facts on the plan

Who spends them: `valsTS_of_R`, Johnson/Desc/K5/Honest/Law/RunsPreR.lean.
Limits. Definitions: premises' forms. Nothing says that either holds anywhere.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.First.Att.K05MergedAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Honest
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Att
open VerifiableInference.Desc.First.Att.P (UnitG UnitsAll K3Pts)
open OnBytes.Road.L5 (dimOf)

/-- **THE SENTENCE ON THE FIELD g**, at the plan's letters: something is laid, and its key points
follow the lookup's own rule: zx has dT coordinates, zy rK, and the key point of call q is a cut of
zy, then zx. -/
def lookR (A : Attention.Plan) (o : Option Forest.Heard) : Prop :=
  ∃ gl, o = some gl ∧ K3Pts A.fs gl.zx gl.zy gl.zk (OnBytes.Slice.readV (gl.zx ++ gl.zy))

/-- The facts on the plan alone. -/
structure PlanR (A : Attention.Plan) (r1 r2 u1 u2 wl ix wh : UnitG) : Prop where
  units : UnitsAll A.S A.fs r1 r2 u1 u2 wl ix wh
  norm : OnBytes.Road.L5.Norm A.S
  tiles : 1 ≤ A.S.lnT
  planes : ∀ f : Inst.Model.AttSeg.Fam, Cb.Pv.Att.End.IsPlane f → A.S.cf.lmS ≤ f.l (dimOf A.S)
  calls : OnBytes.Road.L5.CallsFit A.S A.fs
  lmS : A.S.cf.lmS ≤ A.fs.dT
  tokens : A.S.cf.lt + A.S.cf.ldh ≤ A.fs.dT

end H2K5.Honest
