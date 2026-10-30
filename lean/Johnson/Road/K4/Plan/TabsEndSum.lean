-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Plan/TabsEndSum.lean: THE END OF THE SMALLNESS TEST's TABLES IS A SUM. "The tables'
end": the second component of K8.tabs' own fold (Johnson/Desc/First/K8/Hear.lean): the first entry
behind the last table. General in a place's numbers: every kind of segment; no scope, no numeral.

  `famSum p a`: the entries of one family of tables.
  `foldl_snd`: a fold that adds to its second component.
  **`layFamily_snd`** : (layFamily p a e).2 = e + famSum p a.
  **`end_sum`**, **`end_sum0`**: K8.tabs' fold's second component, from any start and from ([], 0):
    the sum of the families' entries. At p.asks the second is P5J.K8N.tabsEnd p
    (Johnson/P5J/K8ThreeBoxes.lean), by unfolding.
  `sum_rep`, `famSum_const`, `famSum_one`: a family whose matrices have one size.
Limits. Arithmetic on lists. Nothing on soundness.

-/
import Johnson.Desc.First.K8.Hear

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Plan

open VerifiableInference.Desc.First.K8 (Par layFamily)

/-! ## The tables' end is a sum -/

/-- The entries of one family of tables: one for each column and each run of a.2.2 rows, matrix by
matrix. -/
def famSum (p : Par) (a : Nat × Nat × Nat) : Nat :=
  ((List.range a.2.1).map fun q =>
    p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2)).sum

/-- A fold that adds t q to its second component. -/
theorem foldl_snd {α β : Type} (t : β → Nat) (f : List α × Nat → β → List α) :
    ∀ (l : List β) (x : List α × Nat),
      (l.foldl (fun x q => (f x q, x.2 + t q)) x).2 = x.2 + (l.map t).sum
  | [], x => by simp
  | q :: l, x => by
    rw [List.foldl_cons, foldl_snd t f l, List.map_cons, List.sum_cons, Nat.add_assoc]

/-- One family ends its entries further on. -/
theorem layFamily_snd (p : Par) (a : Nat × Nat × Nat) (e : Nat) :
    (layFamily p a e).2 = e + famSum p a :=
  foldl_snd (fun q => p.ks.getD (a.1 + q) 0 * (p.ms.getD (a.1 + q) 0 / a.2.2))
    (fun x q => x.1 ++ [(a.1 + q, a.2.2, x.2)]) (List.range a.2.1) ([], e)

/-- The fold of K8.tabs, from any start. -/
theorem end_sum (p : Par) : ∀ (l : List (Nat × Nat × Nat)) (x : List (Nat × Nat × Nat) × Nat),
    (l.foldl (fun x a => let z := layFamily p a x.2; (x.1 ++ z.1, z.2)) x).2 =
      x.2 + (l.map (famSum p)).sum
  | [], x => by simp
  | a :: l, x => by
    rw [List.foldl_cons, end_sum p l, List.map_cons, List.sum_cons, ← Nat.add_assoc]
    show (layFamily p a x.2).2 + _ = _
    rw [layFamily_snd]

/-- From entry 0. -/
theorem end_sum0 (p : Par) (l : List (Nat × Nat × Nat)) :
    (l.foldl (fun x a => let z := layFamily p a x.2; (x.1 ++ z.1, z.2)) ([], 0)).2 =
      (l.map (famSum p)).sum := by
  rw [end_sum p l ([], 0)]
  exact Nat.zero_add _

/-- The sum of n equal numbers. -/
theorem sum_rep (n a : Nat) : (List.replicate n a).sum = n * a := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.replicate_succ, List.sum_cons, ih, Nat.succ_mul, Nat.add_comm]

/-- A family whose matrices have one size. -/
theorem famSum_const (p : Par) {M0 n L k m : Nat}
    (h : ∀ q, q < n → p.ks.getD (M0 + q) 0 = k ∧ p.ms.getD (M0 + q) 0 = m) :
    famSum p (M0, n, L) = n * (k * (m / L)) := by
  have e : ((List.range n).map fun q =>
      p.ks.getD (M0 + q) 0 * (p.ms.getD (M0 + q) 0 / L)) = List.replicate n (k * (m / L)) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp, fun b hb => ?_⟩
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hb
    obtain ⟨e1, e2⟩ := h q (List.mem_range.1 hq)
    rw [e1, e2]
  show ((List.range n).map fun q =>
      p.ks.getD (M0 + q) 0 * (p.ms.getD (M0 + q) 0 / L)).sum = _
  rw [e, sum_rep]

/-- A family of one matrix. -/
theorem famSum_one (p : Par) {M0 L k m : Nat}
    (h : ∀ q, q < 1 → p.ks.getD (M0 + q) 0 = k ∧ p.ms.getD (M0 + q) 0 = m) :
    famSum p (M0, 1, L) = k * (m / L) := by
  rw [famSum_const p h, Nat.one_mul]

end OnBytes.Road.K4.Plan

#print axioms OnBytes.Road.K4.Plan.foldl_snd
#print axioms OnBytes.Road.K4.Plan.layFamily_snd
#print axioms OnBytes.Road.K4.Plan.end_sum
#print axioms OnBytes.Road.K4.Plan.end_sum0
#print axioms OnBytes.Road.K4.Plan.sum_rep
#print axioms OnBytes.Road.K4.Plan.famSum_const
#print axioms OnBytes.Road.K4.Plan.famSum_one
