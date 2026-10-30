-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/Lay/End/Runs.lean: in the last statement of a run of the chain of a layers' sub-proof's own
rounds, the outputs of the first two sumchecks carry the states of their claims.

An output of a sumcheck carries a public state of its own, at which its output claims are read. In
a last statement that is any nested tuple, that state is tied to nothing. In the last statement of a
run (Ch.run, Cb/Pv/Att/ChainRun.lean) it is the state of the sumcheck's claim at the statement that
the sumcheck has found.

Main theorems: st1_run, st2_run. They rest on Ch.back_run (Cb/Pv/Att/ChainLast.lean): the first
statement inside the last statement of a run is the statement from which the run started.

Limits: the first two sumchecks alone. Nothing on whether a transcript of the reduction is a run's.


-/
import Cb.Pv.Att.ChainLast
import Cb.Pv.Lay.End.Last

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cb.Pv.Lay.End

open Cb.Pv.Att Cb.Pv.Lay

variable {E : Type} [Field E] [Fintype E] {M : Type}

variable {X : Type} (T : LayTail E M X)

/-- In the last statement of a run the first sumcheck's output carries the state of its claim. -/
theorem st1_run (x : X) (ts : T.ch.Trs) :
    (T.b1 (T.ch.run x ts)).2.st =
      (T.s1.cl (T.b1 (T.ch.run x ts)).1.1 (T.b1 (T.ch.run x ts)).1.2).2 := by
  obtain ⟨t1, t2, t3, t4, t5⟩ := ts
  have h : T.xP (T.ch.run x (t1, t2, t3, t4, t5)) = _ := Ch.back_run T.chP _ t5
  have h1 : T.b1 (T.ch.run x (t1, t2, t3, t4, t5)) = _ := congrArg Prod.fst h
  rw [h1]
  rfl

/-- The same for the second sumcheck. -/
theorem st2_run (x : X) (ts : T.ch.Trs) :
    (T.b2 (T.ch.run x ts)).2.st =
      (T.s2.cl (T.b2 (T.ch.run x ts)).1.1 (T.b2 (T.ch.run x ts)).1.2).2 := by
  obtain ⟨t1, t2, t3, t4, t5, t6, t7⟩ := ts
  have h : T.b2 (T.ch.run x (t1, t2, t3, t4, t5, t6, t7)) = _ :=
    Ch.back_run (T.s3.stage T.ow3 T.ch4) _ t7
  rw [h]
  rfl

end Cb.Pv.Lay.End
