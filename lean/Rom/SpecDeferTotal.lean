-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/SpecDeferTotal.lean: deferred programming of a random oracle (Rom/Defer.lean) for an adversary
with one query bound for all oracles. A statement, `Spec.deferTotal`; the proof is in
Rom/DeferTotal.lean. (Words of this library: lean/GLOSSARY.md.)

`Spec.defer` (Rom/Defer.lean) takes an adversary with a query bound t o for each oracle o
(`Adv.Bounded`) and bounds the distance of mode R and mode I by
    the sum over o in os of M o (t o + e o + M o) / 2^(ℓ o):
M o marked evaluations, e o plain ones, charged tokens of at least ℓ o bits. If only the number t of
all the adversary's queries is known (`Adv.TotalBound`), every oracle has to be given the whole
budget, and the part of the bound that is linear in t grows with the number of oracles. That is a
cost of the form of the statement, not of the experiment: each query of the adversary goes to one
oracle o, and forms a pair with each of the at most M o marked evaluations of that oracle only. So
in `Spec.deferTotal` the distance is at most
    t * max over o in os of (M o / 2^(ℓ o)) + the sum over o in os of M o (e o + M o) / 2^(ℓ o).
t counts the queries to all oracles, also to those outside os; such a query uses up one of the t and
adds nothing to the bound. (In the words of the head of Rom/Defer.lean: mode R: one lazily sampled
table serves everybody; mode I: a marked evaluation returns a fresh uniform answer and does not
touch the table; every marked evaluation is charged to one token.)

What it is for. Honest programs that query one oracle at many points which hold the same secret
string, written with further oracles for the later points (Rom/SpecVia.lean). An adversary that is
translated along a bijection of the points keeps only its total query bound. With T further oracles
`Spec.defer`'s form costs a factor of up to T + 1 in the part that is linear in t. This form costs
none there, as long as M o / 2^(ℓ o) is at no further oracle larger than at the true one (no more
marked evaluations, no shorter charged tokens). The second term still has one summand for each
oracle, so it grows with T.

Limits: the second term is `Spec.defer`'s bound at t o = 0: the sum over all oracles of os. Nothing
on expected numbers: e, M, ℓ and no violation of the rules (`DSt.Within`) are required of every run
in mode I, t of every path of the adversary. `Spec.defer` is neither used nor replaced, and neither
statement is an instance of the other: if only the total t is known, this bound is never the larger;
if the budgets t o are known and t is their sum, `Spec.defer`'s bound is never the larger.
-/
import Rom.Defer

open scoped ENNReal
open Prob
namespace Rom

/-- Deferred programming for a total query bound. t queries in all and N calls (N is in no bound); e
o plain and M o marked evaluations of o; tokens charged at o have at least ℓ o bits; marked
evaluations at oracles of os only; no violation of the rules (`DSt.Within`, of every run in mode I).
A statement; the bound: see the head. -/
def Spec.deferTotal : Prop :=
  ∀ (S : OSpec) (sp : Split S) (Out In α : Type) (C : Chall S sp Out In) (s₀ : C.τ)
      (A : Adv S Out In α) (t : ℕ) (e M ℓ : S.ι → ℕ) (N : ℕ) (os : Finset S.ι),
    A.TotalBound t N →
    (∀ x ∈ (interact (C.world true) A (s₀, DSt.init S)).support, x.2.2.Within e M ℓ os) →
    tv ((interact (C.world false) A (s₀, DSt.init S)).map Prod.fst)
        ((interact (C.world true) A (s₀, DSt.init S)).map Prod.fst) ≤
      (t : ℝ≥0∞) * os.sup (fun o => (M o : ℝ≥0∞) / 2 ^ ℓ o) +
        ∑ o ∈ os, (M o : ℝ≥0∞) * (e o + M o : ℕ) / 2 ^ ℓ o

end Rom
