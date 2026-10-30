-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/TablesPlanCode.lean: TWO TESTS WITH CODE ON PUBLIC NUMBERS, for "the text
that makes the output head's tables of reads answers" (Law/TablesAnswer.lean |
Law/SilentAnswers.lean). Definitions alone. No Mathlib: so that a sheet can evaluate them at a list
of rounds.

  skeleton h       the fifteen tables' public halves, in the order of the text
                   (Johnson/Desc/K8/ReadsQuiet.lean: tables): first matrix, number of matrices,
                   length of a stretch, name.
  tabsOfPlan h hp  the tables without their weights: a function of public numbers.
  tabsPlanB h L hp the list of tables is open; la = ls + lt; two calls bear the segments "CNF" and
                   "ROW"; no table of the skeleton is empty; they fill the vector of reads.
  readsPlanB h hp  each of the twelve tables that the head's forms name is in tabsOfPlan's table of
                   tables, and is no shorter than what the forms spend of it.

WHAT IT IS NOT. NEITHER TEST HAS RUN ANYWHERE. Nothing on soundness.

-/
import Johnson.Desc.K8.ReadsQuiet
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law

open OnBytes.Model.Head (Shape HL HPlanH2 Tables)

/-- The fifteen tables' public halves, in the text's order. -/
def skeleton (h : Shape) : List (Nat × Nat × Nat × String) :=
  [(0, h.NHf, 2 ^ h.la, "hf@Z"), (0, h.NHf, 2 ^ h.la, "hf@phiZ"),
   (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, "xbL@Z_V"), (h.NHf + 1 + 1 + 1, 1, 2 ^ h.la, "xbL@Y_N"),
   (h.NHf, 1, h.T, "hd@zt_FC"), (h.NHf, 1, h.T, "hd@r_H"),
   (h.NHf + 1, 1, h.T, "hr@zt_ROW"), (h.NHf + 1, 1, h.T, "hr@P_V"),
   (h.NHf + 1, 1, h.T, "hr@r_tV"), (h.NHf + 1, 1, h.T, "hr@rt_N"),
   (h.NHf + 1, 1, h.T, "hr@phiC"), (h.NHf + 1, 1, h.T, "hr@rhoC"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, "bH-bits-0"), (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, "bH-bits-1"),
   (h.NHf + 1 + 1, 1, 2 ^ h.lmbH, "bH-pin")]

/-- The tables without their weights: of public numbers alone. -/
def tabsOfPlan (h : Shape) (hp : HPlanH2) : Option Tables :=
  (skeleton h).foldlM (fun t a => Own.tableAdded hp.tl.mats t a.1 a.2.1 a.2.2.1 #[] a.2.2.2) {}

/-- **A TEST WITH CODE ON PUBLIC NUMBERS.** -/
def tabsPlanB (h : Shape) (L : HL) (hp : HPlanH2) : Bool :=
  !hp.tl.funClosed && h.la == h.ls + h.lt && (Own.callWith L "CNF").isSome &&
    (Own.callWith L "ROW").isSome && ((tabsOfPlan h hp).any fun t => t.p == hp.nU.getD 2 0)

/-- **A TEST WITH CODE ON PUBLIC NUMBERS**: each of the twelve tables that the head's forms name is
in the plan's table of tables, and is no shorter than what the forms spend of it. -/
def readsPlanB (h : Shape) (hp : HPlanH2) : Bool :=
  (tabsOfPlan h hp).any fun t0 => (readsNeed h).all fun n =>
    (t0.tab.find? fun e => e.1 == n.1).any fun e => Nat.ble n.2 e.2.2

end VerifiableInference.Desc.Kinds.Head.Law
