-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Rom/HopCost.lean: the library's two bounds on one game hop. The hop replaces the oracle's answers at
an honest party's marked evaluations by independent uniform values (mode R to mode I of
Rom/Defer.lean). The two bounds are the two instances of `HopCost` (Rom/SpecHopCost.lean, whose head
says what the definition is for).

  `hopCost_names`     `HopCost S e M ℓ os (costNames e M ℓ os)`, from `Spec.defer`
                      (Rom/DeferProof_tail.lean), where every oracle is given the whole query bound
                      t; `costNames e M ℓ os t` is the sum over o in os of M o (t + e o + M o) /
                      2^(ℓ o).
  `hopCost_total`     `HopCost S e M ℓ os (costTotal e M ℓ os)`, which is `Spec.deferTotal` itself
                      (Rom/DeferTotal.lean); `costTotal e M ℓ os t` is t * max over o in os of (M o
                      / 2^(ℓ o)) + the sum over o in os of M o (e o + M o) / 2^(ℓ o), and is never
                      the larger (`costTotal_le`, Rom/SpecHopCost.lean).

Both hold for all counts e, M, ℓ and every os, without hypotheses (the conditions are inside
`HopCost`: `A.TotalBound t N`, and every run in mode I keeps `DSt.Within e M ℓ os`).

Notation:
  `HopCost S e M ℓ os c` (Rom/SpecHopCost.lean): c bounds the distance of mode R and mode I for
    every challenger whose runs in mode I keep the rules and the counts (`DSt.Within e M ℓ os`),
    against an adversary with t queries in all
  `d.Within e M ℓ os` (Rom/Defer.lean): what a run may do at most: e o plain and M o marked
    evaluations of o; marked ones only at oracles of os, each charged to a token of at least ℓ o
    bits; no violation of the rules
  `A.TotalBound t N` (Rom/World.lean): at most t queries in all and at most N calls, on every path
  `sp`: `Split S`; `C`: `Chall S sp Out In`; `s₀`: `C.τ` (Rom/Defer.lean)
-/
import Rom.SpecHopCost
import Rom.DeferTotal

open scoped ENNReal
open Prob
namespace Rom

variable {S : OSpec}

/-- an adversary with t queries in all makes at most t queries to each oracle -/
theorem Adv.Bounded.of_total {Out In α : Type} :
    ∀ (A : Adv S Out In α) (t N : ℕ) (f : S.ι → ℕ),
      (∀ o, t ≤ f o) → A.TotalBound t N → A.Bounded f N
  | .halt _, _, _, _, _, _ => trivial
  | .sample _ k, t, N, f, hf, h => fun r => Adv.Bounded.of_total (k r) t N f hf (h r)
  | .query _ _ _, 0, _, _, _, h => h.elim
  | .query o _ k, t + 1, N, f, hf, h =>
      ⟨Nat.lt_of_lt_of_le (Nat.succ_pos t) (hf o), fun r => Adv.Bounded.of_total (k r) t N _ (fun o' => by
        by_cases ho : o' = o
        · subst ho
          rw [Function.update_self]
          have := hf o'
          omega
        · rw [Function.update_of_ne ho]
          exact (Nat.le_succ t).trans (hf o')) (h r)⟩
  | .call _ _, _, 0, _, _, h => by cases ‹ℕ› <;> exact h.elim
  | .call _ k, t, N + 1, f, hf, h =>
    fun a => Adv.Bounded.of_total (k a) t N f hf (by cases t <;> exact h a)

theorem hopCost_names (e M ℓ : S.ι → ℕ) (os : Finset S.ι) :
    HopCost S e M ℓ os (costNames e M ℓ os) :=
  fun sp Out In α C s₀ A t N hT hw =>
    DeferTail.defer S sp Out In α C s₀ A (fun _ => t) e M ℓ N os
      (Adv.Bounded.of_total A t N _ (fun _ => le_rfl) hT) hw

theorem hopCost_total (e M ℓ : S.ι → ℕ) (os : Finset S.ι) :
    HopCost S e M ℓ os (costTotal e M ℓ os) :=
  fun sp Out In α C s₀ A t N hT hw => DeferTail.deferTotal S sp Out In α C s₀ A t e M ℓ N os hT hw

end Rom
