-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/OneMaker.lean: two algorithms, one behind the other, as one maker with one log; and a
bound for the union of two events that may depend on the drawn oracle.

The files beside this one have three forms of an experiment over one random oracle. `A.withTrace`:
one algorithm with its log. `twoExp B1 B2` (OnBytes/Slice/OneWorld.lean): a first algorithm, whose
log is kept, then a second one on its output. `bothExp B1 B2` (OnBytes/Slice/StableLeaf.lean): the
same with both logs kept. A bound that is stated in one form says nothing yet of an event in
another. This file takes `twoExp C P` as an ALGORITHM, "the first with its log in its output, then
the second", and its own whole log, `(twoExp C P).withTrace`, as the one experiment, and carries two
bounds there. To add bounds on one experiment it proves that the probability of a union is at most
the sum. For a checker behind any maker, OnBytes/Slice/OneLog.lean has the experiment as an event on
the maker alone, oracle by oracle, and that the event's probability is a measurable function of the
oracle (`PrCoins_twoExp_det`, `measurable_twoExp_det`): that is what the bound for a union asks of
its first event.

Main theorems.
 `twoExp_withTrace`      the maker `twoExp B1 B2` with its whole log is `bothExp B1 B2` with the two
                         logs put one behind the other. An equation between two algorithms.
 `stableLeaf_maker`      `stableLeaf_log` as an event on that one experiment: with probability at
                         most 2 (t1 + 1 + t2)^2 / 2^lam some leaf that is read off the first
                         algorithm's log under the root differs from the leaf that is read off the
                         whole log.
 `clash_maker`           with probability at most (t1 + t2)^2 / 2^lam two different strings of the
                         whole log have one answer.
 `Pr_union_le`           `Rom.Pr c (E ∪ F) ≤ Rom.Pr c E + Rom.Pr c F` for events that may depend on
                         the oracle, if the first one's probability over the coins is a measurable
                         function of the oracle.

What is not claimed. No bound is added to another here: the theorems are tools. Nothing on a
protocol, a language or a checker's yes. `stableLeaf_maker` and `clash_maker` are what
OnBytes/Slice/StableLeaf.lean and OnBytes/Slice/OneLog.lean prove, in another form of the
experiment: all limits in these two heads hold here. The implementation m of the typed oracles by
one oracle is a variable. t1 and t2 count strings put to the one oracle, a repeated one again.
Nothing on the program, which is the Lean port built from OnBytes/, on the C++ verifier or on
BLAKE2b. A bound says nothing once it reaches 1.

-/
import OnBytes.Slice.OneLog
import OnBytes.Slice.StableLeaf

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch MeasureTheory
open scoped ENNReal

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} {β δ : Type}

/-! ## One maker, one log -/

/-- **The maker "the first with its log in its output, then the second", with its own whole log**,
is the experiment that keeps both logs, with the two put one behind the other. An equation between
two algorithms: nothing is drawn. -/
theorem twoExp_withTrace {S : OSpec} (B1 : OComp S β) (B2 : β → OComp S δ) :
    (twoExp B1 B2).withTrace =
      (bothExp B1 B2).bind fun z => OComp.pure ((z.1, z.2.1), z.1.2 ++ z.2.2) := by
  unfold twoExp bothExp
  simp only [Compile.withTrace_bind, withTrace_withTrace, OComp.bind_assoc, OComp.bind,
    OComp.withTrace, List.append_nil]

/-- The maker `twoExp C P` asks at most t1 + t2 queries, if C asks at most t1 and P at most t2 on
every output of C. -/
theorem queryBound_twoExp {S : OSpec} (C : OComp S β) (P : β → OComp S δ) (t1 t2 : ℕ)
    (h1 : C.QueryBound t1) (h2 : ∀ b, (P b).QueryBound t2) : (twoExp C P).QueryBound (t1 + t2) := by
  unfold twoExp
  refine OComp.QueryBound.bind (queryBound_withTrace C t1 h1) fun x => ?_
  have h : ((P x.1).bind fun y => OComp.pure (x, y)).QueryBound (t2 + 0) :=
    OComp.QueryBound.bind (h2 x.1) fun _ => trivial
  exact h

/-- **What lies under a root in the first algorithm's log stays as the log grows, as an event on the
one experiment.** The oracle is drawn; C asks it at most t1 strings; `rt` reads a root off C's
output and log; P, on C's output, asks at most t2. With probability at most 2 (t1 + 1 + t2)^2 /
2^lam there are a depth and a place at which the leaf that is read off C's log under that root
differs from the leaf that is read off the whole log of C and P. The logs are read through m, in
which a leaf's and a vertex's answer is one block. This is `stableLeaf_log` in another form of the
experiment. Conditions and limits as in `stableLeaf_one`. One root: for several, one use for each.
-/
theorem stableLeaf_maker (m : OracleCoding (spec lam K L) lam) (hl : m.blocks Batch.OracleName.leaf = 1)
    (hn : m.blocks Batch.OracleName.node = 1) (C : OComp (rom lam) β)
    (rt : β × Trace (rom lam) → Option (Dig lam)) (P : β → OComp (rom lam) δ) (t1 t2 : ℕ)
    (h1 : C.QueryBound t1) (h2 : ∀ b, (P b).QueryBound t2) :
    Rom.Pr (twoExp C P).withTrace (fun _ => {w | ∃ cm, rt w.1.1 = some cm ∧
        ∃ d j, Batch.extLeaf (singleTr m w.1.1.2) d cm j ≠
          Batch.extLeaf (singleTr m w.2) d cm j}) ≤
      2 * ((t1 + 1 + t2 : ℕ) : ℝ≥0∞) ^ 2 / 2 ^ lam := by
  rw [twoExp_withTrace, Rom.Pr_bind_pure]
  exact stableLeaf_log m hl hn C rt P t1 t2 h1 h2

/-- **Two strings with one answer are rare, on the one experiment.** C asks at most t1 strings, and
P at most t2 on every output of C, a repeated one counted again. With probability at most (t1 +
t2)^2 / 2^lam the whole log of C and P holds two different strings with one answer. This is
`Pr_clash_le` at the maker `twoExp C P`; its conditions and limits hold. -/
theorem clash_maker (C : OComp (rom lam) β) (P : β → OComp (rom lam) δ) (t1 t2 : ℕ)
    (h1 : C.QueryBound t1) (h2 : ∀ b, (P b).QueryBound t2) :
    Rom.Pr (twoExp C P).withTrace (fun _ => {w | ¬ NoClash w.2}) ≤
      (((t1 + t2) ^ 2 : ℕ) : ℝ≥0∞) / 2 ^ lam :=
  Pr_clash_le (twoExp C P) (t1 + t2) (queryBound_twoExp C P t1 t2 h1 h2)

/-! ## The union of two events -/

/-- **The probability of a union is at most the sum**, for events that may depend on the drawn
oracle. Asked: the first event's probability over the algorithm's coins is a measurable function of
the oracle. Without that the library's `Rom.Pr` is a lower integral, which need not be subadditive:
the hypothesis is not idle (an argument on paper; no theorem here). Oracle by oracle it is
`Prob.pr_union_le`. -/
theorem Pr_union_le {S : OSpec} {α : Type} (c : OComp S α) (E F : Fam S → Set α)
    (hE : Measurable fun g => PrCoins g c (E g)) :
    Rom.Pr c (fun g => E g ∪ F g) ≤ Rom.Pr c E + Rom.Pr c F := by
  unfold Rom.Pr
  rw [← lintegral_add_left hE]
  exact lintegral_mono fun g => Prob.pr_union_le _ _ _

end OnBytes.Slice
