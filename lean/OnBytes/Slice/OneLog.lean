-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneLog.lean: two tools for several bounds over one random oracle on bit strings: no
two strings of a log have one answer; an experiment with a checker as an event on the maker alone.

OnBytes/Slice/OneWorld.lean bounds an experiment "the maker, then a checker" over one random oracle.
Before such bounds for several checkers can be added they must speak of one experiment, and what is
read off the maker's log must not depend on which entry with a given answer comes first. This file
has tools for that. That the bounds add is not shown here (the bound for a union:
OnBytes/Slice/OneMaker.lean).

Main definitions: `NoClash`.
Main theorems.
 `Pr_clash_le`     an algorithm with at most t queries to the one oracle puts out a log in which two
                   different strings have one answer with probability at most t^2 / 2^lam.
 `PrCoins_twoExp_det`, `measurable_twoExp_det`   the next, oracle by oracle; and that the event's
                   probability over the coins is a measurable function of the oracle.
 `Pr_twoExp_det`   for a checker without coins, the probability of an event in the experiment "the
                   maker, then the checker" is the probability, for the maker alone, of the event
                   "the maker's output with its log, and the checker's one value on it under the
                   drawn oracle, lie in the event". So experiments with one maker and different
                   checkers are events on one experiment.

What is not claimed. Nothing on any protocol, checker or hash function. The bound in `Pr_clash_le`
is the library's count for a wider event (`ZKCP.DigestKey.RepeatsAt`) and is not tight. The oracle
is a function from all bit strings to strings of lam bits, each value drawn uniformly and
independently.

-/
import OnBytes.Slice.OneWorld
import Compile.DigestKeyBinding

set_option autoImplicit false

namespace OnBytes.Slice
open Rom Prob MeasureTheory
open scoped ENNReal

variable {lam : ℕ} {β δ : Type}

/-- No two entries of the log with different strings have one answer. A string that stands twice is
no clash. That one string has one answer is not asked. -/
def NoClash (σ : Trace (rom lam)) : Prop :=
  ∀ e ∈ σ, ∀ e' ∈ σ, e.2.2 = e'.2.2 → e.2.1 = e'.2.1

/-- A part of a log without a clash has none. -/
theorem NoClash.of_subset {σ τ : Trace (rom lam)} (h : NoClash σ) (hs : ∀ e ∈ τ, e ∈ σ) :
    NoClash τ := fun e he e' he' => h e (hs e he) e' (hs e' he')

/-- A log with a clash shows the library's event "an answer repeats". -/
theorem stepEvent_of_clash {σ : Trace (rom lam)} (h : ¬ NoClash σ) :
    StepEvent ZKCP.DigestKey.RepeatsAt σ := by
  unfold NoClash at h
  push Not at h
  obtain ⟨e, he, e', he', ha, hne⟩ := h
  exact ZKCP.DigestKey.stepEvent_of_two he he' (fun hee => hne (by rw [hee])) ha

/-- **Two strings with one answer are rare.** The oracle is a function from all bit strings to
strings of lam bits, each value drawn uniformly and independently. An algorithm with at most t
queries to it, a repeated one counted again, which may toss coins, puts out a log in which two
different strings have one answer with probability at most t^2 / 2^lam. Not tight: it is the
library's count for a wider event. The bound says nothing once it reaches 1. -/
theorem Pr_clash_le (A : OComp (rom lam) β) (t : ℕ) (hA : A.QueryBound t) :
    Rom.Pr A.withTrace (fun _ => {o | ¬ NoClash o.2}) ≤ ((t ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam := by
  refine le_trans (Rom.Pr_mono A.withTrace (F := fun _ =>
    {o | StepEvent ZKCP.DigestKey.RepeatsAt o.2}) fun _ _ ho => stepEvent_of_clash ho) ?_
  rw [Rom.Pr_eq_law]
  refine le_trans (Rom.pr_stepEvent_le ZKCP.DigestKey.RepeatsAt
    (fun n => ((2 * n + 1 : ℕ) : ℝ≥0∞) / 2 ^ lam) (fun _ _ he hs => hs.1 he)
    (fun pre o q _ => ZKCP.DigestKey.pr_repeatsAt_le pre o q) _ t hA) (le_of_eq ?_)
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Nat.cast_sum, ZKCP.DigestKey.sum_odd_eq_sq]

/-- Oracle by oracle: for a checker without coins, the probability over the coins that the maker's
output with its log, and what the checker returns on it, lie in W is the probability over the
maker's coins that its output with its log and the checker's one value under g lie in W. -/
theorem PrCoins_twoExp_det (A : OComp (rom lam) β) (chk : β → OComp (rom lam) δ)
    (hnc : ∀ x, (chk x).NoCoin) (W : Set ((β × Trace (rom lam)) × δ)) (g : Fam (rom lam)) :
    PrCoins g (twoExp A chk) W = PrCoins g A.withTrace {x | (x, (chk x.1).det g) ∈ W} := by
  unfold PrCoins twoExp
  have e : (A.withTrace.bind fun x => (chk x.1).bind fun y => OComp.pure (x, y)).runEager g =
      (A.withTrace.runEager g).map fun x => (x, (chk x.1).det g) := by
    rw [OComp.runEager_bind, ← PMF.bind_pure_comp]
    refine congrArg _ (funext fun x => ?_)
    rw [(hnc x.1).runEager_bind]
    rfl
  rw [e, pr_map]
  rfl

/-- **An experiment with a checker is an event on the maker alone.** For a checker without coins:
the probability that the maker's output with its log, and what the checker returns on it, lie in W
is the probability, in the experiment with the maker alone, that the maker's output with its log and
the checker's one value under the drawn oracle lie in W. The checker sees the maker's output, not
its log; its own queries are in no log. W does not depend on the oracle. An equation: no bound. -/
theorem Pr_twoExp_det (A : OComp (rom lam) β) (chk : β → OComp (rom lam) δ)
    (hnc : ∀ x, (chk x).NoCoin) (W : Set ((β × Trace (rom lam)) × δ)) :
    Rom.Pr (twoExp A chk) (fun _ => W) =
      Rom.Pr A.withTrace (fun g => {x | (x, (chk x.1).det g) ∈ W}) := by
  unfold Rom.Pr
  exact lintegral_congr fun g => PrCoins_twoExp_det A chk hnc W g

/-- For a checker without coins, the probability over the maker's coins that its output with its log
and the checker's one value under g lie in W is a measurable function of g. So its average over the
oracle is a true integral, and such an event can stand in a bound for a union
(OnBytes/Slice/OneMaker.lean: `Pr_union_le`). -/
theorem measurable_twoExp_det (A : OComp (rom lam) β) (chk : β → OComp (rom lam) δ)
    (hnc : ∀ x, (chk x).NoCoin) (W : Set ((β × Trace (rom lam)) × δ)) :
    Measurable fun g => PrCoins g A.withTrace {x | (x, (chk x.1).det g) ∈ W} := by
  have h : (fun g => PrCoins g A.withTrace {x | (x, (chk x.1).det g) ∈ W}) =
      fun g => PrCoins g (twoExp A chk) W :=
    funext fun g => (PrCoins_twoExp_det A chk hnc W g).symm
  rw [h]
  exact measurable_PrCoins _ _

end OnBytes.Slice
