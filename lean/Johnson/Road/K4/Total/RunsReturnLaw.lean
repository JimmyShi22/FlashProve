-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Total/RunsReturnLaw.lean: THE LAW, PROVED: "BEHIND K4's HEARING ITS TWO RUNS OF
CLAIMS RETURN": `runs_return : RunsReturn` (the sentence and every premise: Total/Returns.lean), out
of the joining (RunsJoin.lean) and the three parts on the listing (`front_skel`: FrontOfParts.lean;
`front_pub`, `run_pub`: PubOnly.lean). And its payers beside it, by name: `fit_behind : FitBehind`
(WindowsFit.lean) for the premise `Fit` at the ledger that the hearing leaves; `hear_skel :
HearSkel` (HearSkel.lean) for the premise `Asks.skel` where the member is itself a return of the
hearing at one plan (one hp and g; one layout, reads and groups' lists), from lookups of one shape.
Two statements: calls.

  **`runs_return`** : `RunsReturn`.
  `runs_return_behind`: the law at Fb := G, `Asks` AS IT WAS (the member too): from a sized ledger F
    whose slots from its next free number on are free and in which the lookup's leaves' window,
    below that number, is there and free.

Limits. THE LAW STANDS UNDER A MEMBER (`Asks.member`): one record o₀ of o's skeleton at which the
listing `front` returns: a premise. BY A RUN, NO THEOREM, such records are there: at one honest
proof of each of two sizes both runs return behind K4's yes at every layers' place (2 | 12), and a
control rings. leavesReady, leavesBelow and "the leaves' window is there and free" are the lookup's
law's to pay; "F has arrays of the right sizes" and "free from its next free number on" are the
table of joints' public items ledger and freeAbove, in the promise in front of K4's block. It says
that the runs return, not what a form is worth. K04_law, the law of K4's block itself, IS NOT
PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.Total.RunsJoin
import Johnson.Road.K4.Total.FrontOfParts
import Johnson.Road.K4.Total.PubOnly
import Johnson.Road.K4.Total.HearSkel

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Desc.First.K4.Total

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Pub HPlan2 Own)
open OnBytes.PscRun (Sized Filled)

/-- **THE LAW.** -/
theorem runs_return : RunsReturn := runs_return_of front_skel front_pub run_pub

/-- The law at the ledger that the hearing leaves. -/
theorem runs_return_behind {rows : Bool} {P Pr P₀ : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard}
    {F G : Fork} {t u : Tape} {o o₀ : Own} (h : hear engFl P hp g fo F t = some (o, G, u))
    (hy : Pr.y = P.y) (hr : Pr.rd = P.rd) (A : Asks rows P P₀ g fo F o o₀)
    (hfree : ∀ j, F.next ≤ j → ¬ Filled F j) (hwL : WinFree fo.leaves F) :
    (∃ fs G₁, formsFrontWith rows Pr g o G = some (fs, G₁) ∧
      ∃ fb G₂, formsBack o G₁ = some (fb, G₂)) ∧
    ∃ fb Gb, formsBack o G = some (fb, Gb) :=
  runs_return rows P Pr P₀ hp g fo F G G t u o o₀ h hy hr A
    (fit_behind P hp g fo F G t u o A.sized hfree hwL A.leavesBelow h)

end OnBytes.Desc.First.K4.Total

#print axioms OnBytes.Desc.First.K4.Total.runs_return
#print axioms OnBytes.Desc.First.K4.Total.runs_return_behind
