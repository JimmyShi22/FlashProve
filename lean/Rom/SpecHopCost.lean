-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecHopCost.lean: a bound on the game hop that replaces the oracle's answers at an honest
party's marked evaluations by independent uniform values (mode R to mode I of Rom/Defer.lean:
deferred programming of the random oracle), for every challenger with given counts. One definition
(`HopCost`), the library's two bounds as terms (`costNames`, `costTotal`), and what follows from the
definition only. That the two bounds are bounds is proved in Rom/HopCost.lean.

Every privacy proof over Rom/Defer.lean has this game hop. All that the rest of such a proof uses of
the hop is a bound on its distance, for an adversary with t queries in all.

  `HopCost S e M ℓ os c`    For every way to split answers, every challenger, every start state and
                            every adversary with at most t queries in all (and at most N calls, for
                            any N): if every run in mode I keeps the rules and the counts
                            (`DSt.Within e M ℓ os`), the two modes differ by at most c t.

So a proof can take c as a variable, and be done once. `costNames` is the bound of deferred
programming with a query bound for each oracle, every oracle given the whole of t; `costTotal` is
the bound for a total query bound (Rom/SpecDeferTotal.lean, whose head compares the two).

Notation:
  e, M, ℓ, os: three functions from oracles to natural numbers and a finite set of oracles; in
      `DSt.Within e M ℓ os` (Rom/Defer.lean): what a run may do at most: e o plain and M o marked
      evaluations of o; marked ones only at oracles of os, each charged to a token of at least ℓ o
      bits; no violation of the rules
  c: a function from natural numbers to `ℝ≥0∞`

Limits: nothing on any particular challenger or count. e, M, ℓ are required of every run in mode I,
t of every path of the adversary. c need not grow with t. `Spec.defer` with different budgets at
different oracles is no instance.
-/
import Rom.Defer
noncomputable section -- Lean tags what it cannot compile

open scoped ENNReal
open Prob
namespace Rom

/-- c bounds the distance of mode R and mode I for every challenger whose runs in mode I keep the
rules and the counts (`DSt.Within e M ℓ os`), against an adversary with t queries in all and N calls
(N is in no bound). (e, M, ℓ, os: the head.) -/
def HopCost (S : OSpec) (e M ℓ : S.ι → ℕ) (os : Finset S.ι) (c : ℕ → ℝ≥0∞) : Prop :=
  ∀ (sp : Split S) (Out In α : Type) (C : Chall S sp Out In) (s₀ : C.τ)
      (A : Adv S Out In α) (t N : ℕ),
    A.TotalBound t N →
    (∀ x ∈ (interact (C.world true) A (s₀, DSt.init S)).support, x.2.2.Within e M ℓ os) →
    tv ((interact (C.world false) A (s₀, DSt.init S)).map Prod.fst)
        ((interact (C.world true) A (s₀, DSt.init S)).map Prod.fst) ≤ c t

variable {S : OSpec} {e M ℓ : S.ι → ℕ} {os : Finset S.ι}

theorem HopCost.mono {c c' : ℕ → ℝ≥0∞} (h : HopCost S e M ℓ os c) (hc : ∀ t, c t ≤ c' t) :
    HopCost S e M ℓ os c' :=
  fun sp Out In α C s₀ A t N hT hw => (h sp Out In α C s₀ A t N hT hw).trans (hc t)

/-- Smaller counts, longer tokens, fewer oracles: the same bound holds. -/
theorem HopCost.anti {e' M' ℓ' : S.ι → ℕ} {os' : Finset S.ι} {c : ℕ → ℝ≥0∞} (he : ∀ o, e o ≤ e' o)
    (hM : ∀ o, M o ≤ M' o) (hl : ∀ o, ℓ' o ≤ ℓ o) (hos : os ⊆ os') (h : HopCost S e' M' ℓ' os' c) :
    HopCost S e M ℓ os c :=
  fun sp Out In α C s₀ A t N hT hw => h sp Out In α C s₀ A t N hT fun x hx =>
    let w := hw x hx
    ⟨w.1, fun o => (w.2.1 o).trans (he o),
      fun o => (w.2.2.1 o).trans (hM o),
      fun v hv => ⟨hos (w.2.2.2 v hv).1, (hl _).trans (w.2.2.2 v hv).2⟩⟩

/-- the bound of deferred programming with the whole query bound at every oracle -/
def costNames (e M ℓ : S.ι → ℕ) (os : Finset S.ι) (t : ℕ) : ℝ≥0∞ :=
  ∑ o ∈ os, (M o : ℝ≥0∞) * (t + e o + M o : ℕ) / 2 ^ ℓ o

/-- the bound of deferred programming for a total query bound -/
def costTotal (e M ℓ : S.ι → ℕ) (os : Finset S.ι) (t : ℕ) : ℝ≥0∞ :=
  (t : ℝ≥0∞) * os.sup (fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) +
    ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o

/-- The bound for a total query bound is never the larger. -/
theorem costTotal_le (e M ℓ : S.ι → ℕ) (os : Finset S.ι) (t : ℕ) :
    costTotal e M ℓ os t ≤ costNames e M ℓ os t := by
  have h1 : (t : ℝ≥0∞) * os.sup (fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) ≤
      ∑ o ∈ os, (t : ℝ≥0∞) * ((M o : ℝ≥0∞) / 2 ^ ℓ o) := by
    rw [← Finset.mul_sum]
    gcongr
    exact Finset.sup_le fun o ho =>
      Finset.single_le_sum (f := fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) (fun _ _ => zero_le _) ho
  unfold costTotal costNames
  refine le_trans (add_le_add h1 le_rfl) (le_of_eq ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun o _ => ?_
  simp only [div_eq_mul_inv]
  push_cast
  ring

end Rom
