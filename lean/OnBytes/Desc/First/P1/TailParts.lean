-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/TailParts.lean: THE PARTS OF THE CHAIN's LAST STATEMENT, AS THE LIBRARY's END
FILES NAME THEM (`LayTail.b1` … `b6`, Cb/Pv/Lay/End/Last.lean), AT `TailH.z7`
(OnBytes/Tie/Pv/Lay/OwnTieL.lean): they are `TailH.z1` … `z6`; so the k-th sumcheck's typed output
inside the last statement is the k-th stage's `StgH.out`. Equations by unfolding.

  `b6_z7` … `b1_z7`: `T.b_k (D.z7 x) = D.z_k x`. `o7_z7`, `o_k`: the outputs.

No premise: `z7` is a nested pair, and the library's names are its projections. Nothing on
soundness.
-/
import OnBytes.Tie.Pv.Lay.OwnTieL
import Cb.Pv.Lay.End.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.P1
open Cb Cb.Pv.Lay OnBytes.Model
open OnBytes.Tie.Pv.Lay.Eng

variable {K : Type} [Field K] [Fintype K] {ρ : Reading K} {M X : Type} (T : LayTail K M X)
  (D : TailH ρ T) (x : X)

theorem b6_z7 : T.b6 (D.z7 x) = D.z6 x := rfl
theorem b5_z7 : T.b5 (D.z7 x) = D.z5 x := rfl
theorem b4_z7 : T.b4 (D.z7 x) = D.z4 x := rfl
theorem b3_z7 : T.b3 (D.z7 x) = D.z3 x := rfl
theorem b2_z7 : T.b2 (D.z7 x) = D.z2 x := rfl
theorem b1_z7 : T.b1 (D.z7 x) = D.z1 x := rfl

theorem o7_z7 : (D.z7 x).2 = D.d7.out := rfl
theorem o6_z7 : (T.b6 (D.z7 x)).2 = D.d6.out := rfl
theorem o5_z7 : (T.b5 (D.z7 x)).2 = D.d5.out := rfl
theorem o4_z7 : (T.b4 (D.z7 x)).2 = D.d4.out := rfl
theorem o3_z7 : (T.b3 (D.z7 x)).2 = D.d3.out := rfl
theorem o2_z7 : (T.b2 (D.z7 x)).2 = D.d2.out := rfl
theorem o1_z7 : (T.b1 (D.z7 x)).2 = D.d1.out := rfl

end OnBytes.Desc.First.P1

#print axioms OnBytes.Desc.First.P1.b1_z7
#print axioms OnBytes.Desc.First.P1.o1_z7
