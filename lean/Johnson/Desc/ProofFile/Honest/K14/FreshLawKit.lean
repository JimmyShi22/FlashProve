-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/FreshLawKit.lean: two general lemmas for the owner's sentence on a
coin that another part spends (the field fresh of Good, Honest/Side.lean). No protocol, no part and
no book occurs here.

The setting of the first. Coins c of a finite type C are cut, by a bijection e, into x and w. A
function tr makes of x a triple (a, b, k), where k has n entries, and over uniform x THE TRIPLE IS
UNIFORM.

  entryBeside     a bijection: a triple and w, as (the entry kappa of k, a, b, w) beside the other
                  entries of k
  apart_of_law    **then, over uniform c, (the entry kappa of k, a, b, w) has the distribution of
                  (a fresh uniform element, a, b, w)**
  residues_set    numbers whose residues modulo 2 ^ a are at most r distinct numbers: a set of at
                  most r members of Fin (2 ^ a) holds all these residues

What is not claimed. That any function of a protocol's coins makes a uniform triple. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.Law.ToyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open Prob

variable {C X Om A B K : Type}

/-- A triple and w, as (the entry kappa, a, b, w) beside the other entries. -/
def entryBeside {n : Nat} (kappa : Fin n) :
    (A × B × (Fin n → K)) × Om ≃ (K × A × B × Om) × ({j : Fin n // j ≠ kappa} → K) where
  toFun p := ((p.1.2.2 kappa, p.1.1, p.1.2.1, p.2), fun j => p.1.2.2 j.1)
  invFun q := ((q.1.2.1, q.1.2.2.1, fun j => if h : j = kappa then q.1.1 else q.2 ⟨j, h⟩),
    q.1.2.2.2)
  left_inv p := by
    refine Prod.ext (Prod.ext rfl (Prod.ext rfl (funext fun j => ?_))) rfl
    by_cases h : j = kappa
    · subst h
      exact dif_pos rfl
    · exact dif_neg h
  right_inv q := by
    refine Prod.ext (Prod.ext ?_ rfl) (funext fun j => ?_)
    · exact dif_pos rfl
    · exact dif_neg j.2

variable [Fintype C] [Nonempty C] [Fintype X] [Nonempty X] [Fintype Om] [Nonempty Om] [Fintype A]
  [Nonempty A] [Fintype B] [Nonempty B] [Fintype K] [Nonempty K]

/-- **Where the triple is uniform, its entry kappa is uniform and independent of its two other
components together with the coins w.** -/
theorem apart_of_law {n : Nat} (kappa : Fin n) (e : C ≃ X × Om) (tr : X → A × B × (Fin n → K))
    (hlaw : (unif X).map tr = unif (A × B × (Fin n → K))) :
    (unif C).map (fun c => ((tr (e c).1).2.2 kappa, (tr (e c).1).1, (tr (e c).1).2.1, (e c).2)) =
      (unif (K × C)).map fun a => (a.1, (tr (e a.2).1).1, (tr (e a.2).1).2.1, (e a.2).2) := by
  have hT : (unif (X × Om)).map (fun a => (tr a.1, a.2)) =
      unif ((A × B × (Fin n → K)) × Om) := by
    have h := Iop.MaskKit.map_pair_indep (β := Om) tr (id : A × B × (Fin n → K) → _)
      (by rw [hlaw, PMF.map_id])
    rw [h]
    exact PMF.map_id _
  have hL : (unif C).map
      (fun c => ((tr (e c).1).2.2 kappa, (tr (e c).1).1, (tr (e c).1).2.1, (e c).2)) =
      unif (K × A × B × Om) := by
    have h1 : (unif C).map
        (fun c => ((tr (e c).1).2.2 kappa, (tr (e c).1).1, (tr (e c).1).2.1, (e c).2)) =
        (unif (X × Om)).map fun a => (entryBeside kappa (tr a.1, a.2)).1 :=
      Iop.MaskKit.map_unif_of_equiv e fun a => (entryBeside kappa (tr a.1, a.2)).1
    have h2 : (unif (X × Om)).map (fun a => (entryBeside kappa (tr a.1, a.2)).1) =
        ((unif (X × Om)).map fun a => (tr a.1, a.2)).map fun p => (entryBeside kappa p).1 :=
      (PMF.map_comp (fun a : X × Om => (tr a.1, a.2)) (unif (X × Om))
        fun p => (entryBeside kappa p).1).symm
    rw [h1, h2, hT]
    exact (map_unif_fst_equiv (entryBeside kappa) id (fun p => (entryBeside kappa p).1)
      fun _ => rfl).trans (PMF.map_id _)
  have hH : (unif C).map (fun c => ((tr (e c).1).1, (tr (e c).1).2.1, (e c).2)) =
      unif (A × B × Om) := by
    have h1 : (unif C).map (fun c => ((tr (e c).1).1, (tr (e c).1).2.1, (e c).2)) =
        ((unif C).map fun c =>
          ((tr (e c).1).2.2 kappa, (tr (e c).1).1, (tr (e c).1).2.1, (e c).2)).map Prod.snd :=
      (PMF.map_comp
        (fun c : C => ((tr (e c).1).2.2 kappa, (tr (e c).1).1, (tr (e c).1).2.1, (e c).2))
        (unif C) Prod.snd).symm
    rw [h1, hL, map_snd_unif]
  have hR : (unif (K × C)).map
      (fun a => (a.1, (tr (e a.2).1).1, (tr (e a.2).1).2.1, (e a.2).2)) =
      unif (K × A × B × Om) := by
    have h1 : ∀ a : K, ((unif C).map fun c =>
        (a, (tr (e c).1).1, (tr (e c).1).2.1, (e c).2)) =
        (unif (A × B × Om)).map fun y => (a, y) := fun a => by
      rw [← hH, PMF.map_comp]
      rfl
    rw [map_unif_prod, funext h1, ← map_unif_prod fun p : K × A × B × Om => p]
    exact PMF.map_id _
  rw [hL, hR]

/-- Numbers whose residues modulo 2 ^ a are at most r distinct numbers: there is a set of at most r
members of Fin (2 ^ a) that holds each of these residues. -/
theorem residues_set (a r : Nat) (l : List Nat)
    (h : ((l.map (· % 2 ^ a)).toFinset).card ≤ r) :
    ∃ S : Finset (Fin (2 ^ a)), S.card ≤ r ∧
      ∀ x ∈ l, ∀ hx : x % 2 ^ a < 2 ^ a, (⟨x % 2 ^ a, hx⟩ : Fin (2 ^ a)) ∈ S := by
  classical
  refine ⟨Finset.univ.filter fun y => y.val ∈ (l.map (· % 2 ^ a)).toFinset, ?_,
    fun x hx hlt => ?_⟩
  · refine le_trans ?_ h
    refine Finset.card_le_card_of_injOn Fin.val (fun y hy => ?_) fun _ _ _ _ e => Fin.ext e
    exact (Finset.mem_filter.1 hy).2
  · exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
      List.mem_toFinset.2 (List.mem_map.2 ⟨x, hx, rfl⟩)⟩

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.entryBeside
#print axioms ProofFile.Honest.K14.apart_of_law
#print axioms ProofFile.Honest.K14.residues_set
