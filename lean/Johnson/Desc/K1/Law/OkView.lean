-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/OkView.lean: where every word of a view is below the prime, the seeds that a
round of the view draws read as joint seeds of the field as soon as no factor is spelt by three
words 0.

Main names: okE_ofTriple, cutSeeds_ok, okView_factors, reads_of_view.

What is not claimed. That the seeds so read are uniform: from a hash's blocks to draws is not here.
Nothing on an honest prover or on hiding.

-/
import Johnson.Desc.K1.Law.Sound

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice

theorem okE_ofTriple (x : UInt64 × UInt64 × UInt64)
    (h : (x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) = true) :
    okE (E.ofTriple x) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [okE, okF, E.ofTriple, E.mk3, Bool.and_eq_true, decide_eq_true_eq]
  exact h

theorem cutSeeds_ok (v : Nat) : ∀ (n : Nat) (l : List E), (∀ e ∈ l, okE e = true) →
    ∀ s ∈ cutSeeds v n l, okE s.2 = true
  | 0, _, _, s, hs => by simp [cutSeeds] at hs
  | n + 1, l, h, s, hs => by
    simp only [cutSeeds, List.mem_cons] at hs
    rcases hs with rfl | hs
    · show okE ((l.drop v).headD zeroE) = true
      cases hd : l.drop v with
      | nil => rfl
      | cons a t =>
        exact h a (List.mem_of_mem_drop (by rw [hd]; exact List.mem_cons_self))
    · exact cutSeeds_ok v n (l.drop (v + 1)) (fun e he => h e (List.mem_of_mem_drop he)) s hs

/-- Every factor that a round of such a view draws is spelt by words below the prime. -/
theorem okView_factors (P : Par) (v : Fmt.View) (r₁ : Fmt.RoundView) (hr : r₁ ∈ v.rounds)
    (hv : viewWordsBelowPrime v = true) : ∀ s ∈ seedsOf P r₁, okE s.2 = true := by
  simp only [viewWordsBelowPrime, Bool.and_eq_true, List.all_eq_true] at hv
  have h1 := (hv.1 r₁ hr).1
  refine cutSeeds_ok _ _ _ fun e he => ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 he
  exact okE_ofTriple x (by simpa using h1 x hx)

/-- **The seeds of a round of such a view read**, where no factor is spelt by three words 0. -/
theorem reads_of_view (P : Par) (v : Fmt.View) (r₁ : Fmt.RoundView) (hr : r₁ ∈ v.rounds)
    (hv : viewWordsBelowPrime v = true) (hnz : ∀ s ∈ seedsOf P r₁, isZeroE s.2 = false) :
    ∃ ρ : Seeds P, ReadsAs P r₁ ρ :=
  reads_exists P r₁ (okView_factors P v r₁ hr hv) hnz

end VerifiableInference.Desc.K1
