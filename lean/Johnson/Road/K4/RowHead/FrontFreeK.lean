-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/FrontFreeK.lean: THE ONE CLOSED FACT `FrontFree`
(Johnson/Road/K4/RowHead/FrontOfHead.lean), AT ALL LETTERS: for all eight free
numbers, all counts of padding keys, all scales and all rotary tables: the twins return, and the
listing "front" returns at the plan's value at the groups 0 and 1. And so, under the head, the same
at the head's own public record.

  HOW: four facts at closed values (ClosedAt.lean) and five equations on the scan (ClosedTies.lean)
    are each closed by `kernel_rfl` (Johnson/Unfolds/KernelRfl.lean), one comparison by Lean's
    kernel; that the returns do not hang on the letters is proved by ordinary laws (ClosedJoin.lean
    and the files that it names). `kernel_rfl` is not called in this file.
  **`front_free`** : FrontFree.
  **`front_at_head`** (hA : P5J.AtMgA …) : the test frontB false accepts at the groups 0 and 1 of
  the head's own public record: NO PREMISE BUT THE HEAD.

Limits. On the test frontB at two groups alone: k4RowB's other half (the light test at the twelve
groups) is not here. `front_free_at` HAS NO NEGATIVE TEST THAT CAN FAIL IN THIS TREE. K04_law, the
law of K4's sub-protocol itself, IS NOT PROVED. Nothing on
soundness.
-/
import Johnson.Unfolds.KernelRfl
import Johnson.Road.K4.RowHead.FrontOfHead
import Johnson.Road.K4.RowHead.ClosedJoin

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Desc.First.K4.Total (frontB)
open OnBytes.Maker (WholeD)

theorem front_free_at (v : VerifierAndGoals.FreeLines) (pub : Array ℕ) (sc : Layer.Scales) (rope : Array ℕ) :
    withPlans v pub sc rope (fun L G => (List.range 2).all fun g => (G[g]?).any fun hp =>
      frontB false L hp g L.y.fo) = true :=
  Closed.plans_closed fun e1 e2 eF W => Closed.num_two (fun _ _ a b => Closed.all_two a b)
    (Closed.after_letters e1 e2 eF pub #[] sc Closed.scC rope #[] W Closed.wC
      (Closed.front_blind 0 e1 e2 eF pub sc rope W) Closed.closedFrontZero)
    (Closed.after_letters e1 e2 eF pub #[] sc Closed.scC rope #[] W Closed.wC
      (Closed.front_blind 1 e1 e2 eF pub sc rope W) Closed.closedFrontOne)

/-- **The one closed fact.** -/
theorem front_free : FrontFree := front_free_at

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **UNDER THE HEAD, AND NOTHING ELSE: the listing "front" returns at the plan's value at the
groups 0
and 1.** -/
theorem front_at_head (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ((List.range 2).all fun g => ((P5J.At.X Zp).G[g]?).any fun hp =>
      frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo) = true :=
  front_of_head front_free hA

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.front_free_at
#print axioms OnBytes.Road.K4.front_free
#print axioms OnBytes.Road.K4.front_at_head
