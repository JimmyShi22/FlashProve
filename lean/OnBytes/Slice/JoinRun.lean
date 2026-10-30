-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/JoinRun.lean: the join at tables of the oracle's values, for an experiment in which a
verifier is run.

OnBytes/Slice/JoinAtSet.lean (`join_id_at`) bounds the probability of an event on the outcomes
of "a committer, then a prover": no verifier stands in its experiment; `Yes` is any event. A top
statement has another shape: a committer runs, its log is kept; a prover runs on its output; THEN A
VERIFIER IS RUN, under the same oracle, on what the two put out; and the bound is on "it says yes,
and what is read off the committer's log is not fine". This file passes from the one shape to the
other, for a verifier that is an algorithm without coins.

How. `Pr_twoExp_det` (OnBytes/Slice/OneLog.lean) turns an experiment "a maker, then a checker
without coins" into an event on the maker with its log. Taken at the maker "a committer, then a
prover", the maker's output with its log is the join's outcome: C's output with its log, P's output,
the whole log.

Main theorem.
 `Pr_run_eq`          the probability, in the experiment in which V is run behind C and P, that V
     says yes and `Fine` fails, is the probability, in the experiment with C and P alone, that V's
     one value under the drawn oracle is yes and `Fine` fails. An equation.
 `Pr_run_eq` carries `join_id_at3` to `join_id_run3` (OnBytes/Slice/JoinOut3.lean). There `Yes` is
     "V's value is yes"; `Fine` does not read the oracle; no hypothesis on measurability is asked
     (`measurableSet_det`); of the two hypotheses on logs without the entries at the strings the
     half on `Yes` is not asked, since V sees the two outputs, which stay as they are. They are
     asked of every outcome, also of one on which V says no: more than `join_id_at` asks.

What is not claimed. What the head of OnBytes/Slice/JoinAtSet.lean does not claim: every part, the
sets, the key, what is fine are variables, and nothing is joined. No verifier stands here: V is a
variable. V SEES C's OUTPUT AND P's OUTPUT, NOT C's LOG. No bound is asked on the number of V's
queries, and V's queries stand in no log that is read. A verifier that tosses coins is not covered.
`Fine` may read the whole outcome, but not the oracle. The bound says nothing once it reaches 1.

-/
import OnBytes.Slice.JoinAtSet

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open OnBytes.Tie (IdKey idCode firstId)
open scoped ENNReal

variable {β δ : Type}

/-- **An experiment in which a verifier is run behind a committer and a prover is an event on these
two alone.** V has no coins and sees C's output and P's output. The probability that V says yes and
`Fine` fails of the outcome (C's output with its log, P's output, the log of both) is the
probability, with C and P alone, that V's one value under the drawn oracle is yes and `Fine` fails.
V's own queries are in no log. An equation: no bound. -/
theorem Pr_run_eq (C : OComp (rom 256) β) (P : β → OComp (rom 256) δ)
    (V : β × δ → OComp (rom 256) Bool) (hV : ∀ x, (V x).NoCoin)
    (Fine : ((β × Trace (rom 256)) × δ) × Trace (rom 256) → Prop) :
    Rom.Pr (twoExp (twoExp C P) fun x => V (x.1.1, x.2))
        (fun _ => {z | z.2 = true ∧ ¬ Fine z.1}) =
      Rom.Pr (twoExp C P).withTrace
        (fun g => {w | (V (w.1.1.1, w.1.2)).det g = true ∧ ¬ Fine w}) :=
  Pr_twoExp_det (twoExp C P) (fun x => V (x.1.1, x.2)) (fun _ => hV _)
    {z | z.2 = true ∧ ¬ Fine z.1}

end OnBytes.Slice
