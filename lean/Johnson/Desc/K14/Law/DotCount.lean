-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/DotCount.lean: the count behind the constraint (Dot) of the linear claim's
second part, at the shared point.

An instance has fixed a vector W, one entry for each column of the index M, before the shared point
psi is drawn. omega_col is M applied to the equality vector at psi (OmegaIs). (Dot) says that the
instance's row weights g applied to omega_col are the equality vector at psi applied to W (DotEq).
If W is not g applied to M's rows, both hold at no more than k |K| ^ (k - 1) of the |K| ^ k points.
Main names: OmegaIs, DotEq, dot_gap, dotCatches, dotCatches_batch.

What is not claimed. This is a count over a finite field alone: it names no verifier and no text.
That omega_col is M applied to the equality vector is a premise inside the event. Nothing on how psi
is drawn or on W being fixed before it.

-/
import Johnson.Desc.K14.Law.Catches

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law

variable {K : Type} [Field K]

/-- omega_col is M applied to the equality vector at psi: R rows, 2 ^ k columns. -/
def OmegaIs (R k : Nat) (M : Nat → Nat → K) (psi : List K) (omega : Nat → K) : Prop :=
  ∀ y < R, omega y = ∑ c ∈ Finset.range (2 ^ k), eqK psi c * M y c

/-- (Dot) as an equation in K. -/
def DotEq (R k : Nat) (g omega : Nat → K) (psi : List K) (W : Nat → K) : Prop :=
  ∑ y ∈ Finset.range R, g y * omega y = ∑ c ∈ Finset.range (2 ^ k), eqK psi c * W c

/-- With omega_col as it should be, (Dot) says that a form in psi vanishes: its coefficients are
what W is short of g applied to M's rows. -/
theorem dot_gap (R k : Nat) (M : Nat → Nat → K) (g omega : Nat → K) (psi : List K) (W : Nat → K)
    (hO : OmegaIs R k M psi omega) (hD : DotEq R k g omega psi W) :
    ∑ c ∈ Finset.range (2 ^ k), eqK psi c * (W c - ∑ y ∈ Finset.range R, g y * M y c) = 0 := by
  have h1 : ∑ y ∈ Finset.range R, g y * omega y =
      ∑ c ∈ Finset.range (2 ^ k), eqK psi c * ∑ y ∈ Finset.range R, g y * M y c := by
    have : ∀ y ∈ Finset.range R, g y * omega y =
        ∑ c ∈ Finset.range (2 ^ k), eqK psi c * (g y * M y c) := by
      intro y hy
      rw [hO y (Finset.mem_range.1 hy), Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by ring
    rw [Finset.sum_congr rfl this, Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => by rw [Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← h1, hD, sub_self]

open Classical in
/-- **CATCHES**, for (Dot): if W is not g applied to M's rows, there are few points psi at which
omega_col can be as it should and (Dot) hold. -/
theorem dotCatches [Fintype K] (R k : Nat) (M : Nat → Nat → K) (g W : Nat → K)
    (h : ∃ c < 2 ^ k, W c ≠ ∑ y ∈ Finset.range R, g y * M y c) :
    (Finset.univ.filter fun psi : Fin k → K =>
      ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
        DotEq R k g omega (List.ofFn psi) W).card ≤ k * Fintype.card K ^ (k - 1) := by
  obtain ⟨c, hc, hne⟩ := h
  refine le_trans (Finset.card_le_card ?_)
    (card_zeros_le k (fun c => W c - ∑ y ∈ Finset.range R, g y * M y c)
      ⟨c, hc, sub_ne_zero.2 hne⟩)
  intro psi hpsi
  rw [Finset.mem_filter] at hpsi
  obtain ⟨_, omega, hO, hD⟩ := hpsi
  unfold zeros
  exact Finset.mem_filter.2 ⟨Finset.mem_univ _, dot_gap R k M g omega _ W hO hD⟩

open Classical in
/-- For a batch of n instances behind one index: the points at which some instance whose W is not as
it should passes are no more than n times as many. -/
theorem dotCatches_batch [Fintype K] (n R k : Nat) (M : Nat → Nat → K) (g W : Nat → Nat → K) :
    (Finset.univ.filter fun psi : Fin k → K =>
      ∃ i < n, (∃ c < 2 ^ k, W i c ≠ ∑ y ∈ Finset.range R, g i y * M y c) ∧
        ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
          DotEq R k (g i) omega (List.ofFn psi) (W i)).card ≤
      n * (k * Fintype.card K ^ (k - 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsub : (Finset.univ.filter fun psi : Fin k → K =>
        ∃ i < n + 1, (∃ c < 2 ^ k, W i c ≠ ∑ y ∈ Finset.range R, g i y * M y c) ∧
          ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
            DotEq R k (g i) omega (List.ofFn psi) (W i)) ⊆
        (Finset.univ.filter fun psi : Fin k → K =>
          ∃ i < n, (∃ c < 2 ^ k, W i c ≠ ∑ y ∈ Finset.range R, g i y * M y c) ∧
            ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
              DotEq R k (g i) omega (List.ofFn psi) (W i)) ∪
        (Finset.univ.filter fun psi : Fin k → K =>
          (∃ c < 2 ^ k, W n c ≠ ∑ y ∈ Finset.range R, g n y * M y c) ∧
            ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
              DotEq R k (g n) omega (List.ofFn psi) (W n)) := by
      intro psi hpsi
      rw [Finset.mem_filter] at hpsi
      obtain ⟨_, i, hi, hrest⟩ := hpsi
      rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
      by_cases e : i = n
      · subst e
        exact Or.inr ⟨Finset.mem_univ _, hrest⟩
      · exact Or.inl ⟨Finset.mem_univ _, i, by omega, hrest⟩
    have hlast : (Finset.univ.filter fun psi : Fin k → K =>
        (∃ c < 2 ^ k, W n c ≠ ∑ y ∈ Finset.range R, g n y * M y c) ∧
          ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
            DotEq R k (g n) omega (List.ofFn psi) (W n)).card ≤
        k * Fintype.card K ^ (k - 1) := by
      by_cases hb : ∃ c < 2 ^ k, W n c ≠ ∑ y ∈ Finset.range R, g n y * M y c
      · refine le_trans (Finset.card_le_card ?_) (dotCatches R k M (g n) (W n) hb)
        intro psi hpsi
        rw [Finset.mem_filter] at hpsi ⊢
        exact ⟨hpsi.1, hpsi.2.2⟩
      · have : (Finset.univ.filter fun psi : Fin k → K =>
            (∃ c < 2 ^ k, W n c ≠ ∑ y ∈ Finset.range R, g n y * M y c) ∧
              ∃ omega, OmegaIs R k M (List.ofFn psi) omega ∧
                DotEq R k (g n) omega (List.ofFn psi) (W n)) = ∅ :=
          Finset.filter_eq_empty_iff.2 fun psi _ hh => hb hh.1
        rw [this]; simp
    calc _ ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
      _ ≤ n * (k * Fintype.card K ^ (k - 1)) + k * Fintype.card K ^ (k - 1) :=
        Nat.add_le_add ih hlast
      _ = (n + 1) * (k * Fintype.card K ^ (k - 1)) := by ring

end Desc.K14.Law
