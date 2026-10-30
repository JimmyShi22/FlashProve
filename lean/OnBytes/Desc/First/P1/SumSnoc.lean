-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/P1/SumSnoc.lean: THE LAST VARIABLE ON ITS OWN. What a caller of the sumcheck owes
(`IsSum`, OnBytes/Desc/First/P1/SumCore.lean) for a summand with one variable more behind the
others, from what it owes without it. Algebra over a field. Statements and proofs.

  `isSum_snoc`: let S' be summed by the variables vs to c. Let S be a function of one challenge more
    such that, AT EVERY LIST rs OF CHALLENGES, y ↦ S (rs ++ [y]) is a polynomial of degree below w.d
    whose sum under w is S' rs. Then S is summed by vs ++ [w] to c.
  `isSum_Y`: the case of the masked sumcheck's further variable Y, which is read at 0 (a two-point
    weight (1, 0)): S' rs is S (rs ++ [0]).
  `isSum_Y_mul`: S (rs ++ [y]) = (a rs + y * ma rs) * (b rs + y * mb rs): two end terms, each shown
    under a mask THAT MAY DEPEND ON THE CHALLENGES rs (a combination of mask entries under public
    coefficients at the run's own challenges); Y wants three coefficients.
  `isSum_Y_lin`: S (rs ++ [y]) = s rs + y * m rs: affine in Y; Y wants two coefficients.

This asks nothing of the shape of S in the other variables, and no degree of Y but the one that the
caller's own polynomial has: so it serves summands of any degree in Y. The way of
OnBytes/Desc/First/P1/SumMle.lean (`ext1`: Y as one more bit of a table) serves constant masks only.
Nothing is said of probabilities.
-/
import OnBytes.Desc.First.P1.SumMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace OnBytes.Desc.First.P1
open Polynomial

variable {K : Type} [Field K]

/-- **One variable more, behind the others.** -/
theorem isSum_snoc (w : Wt K) : ∀ (vs : List (Wt K)) (S S' : List K → K) (c : K),
    (∀ rs, ∃ q : K[X], q.natDegree < w.d ∧ w.sum q = S' rs ∧ ∀ y, q.eval y = S (rs ++ [y])) →
    IsSum vs S' c → IsSum (vs ++ [w]) S c
  | [], S, S', c, h, hs => by
    obtain ⟨q, hd, hsum, hev⟩ := h []
    have hc : S' [] = c := hs
    exact ⟨q, hd, by rw [hsum, hc], fun y => (hev y).symm⟩
  | v :: vs, S, S', c, h, hs => by
    obtain ⟨q, hd, hsum, hrest⟩ := hs
    refine ⟨q, hd, hsum, fun x => ?_⟩
    exact isSum_snoc w vs (fun rs => S (x :: rs)) (fun rs => S' (x :: rs)) (q.eval x)
      (fun rs => h (x :: rs)) (hrest x)

/-- **The further variable, read at 0.** -/
theorem isSum_Y (w : Wt K) (hw : w.Two 1 0) (vs : List (Wt K)) (S : List K → K) (c : K)
    (h : ∀ rs, ∃ q : K[X], q.natDegree < w.d ∧ ∀ y, q.eval y = S (rs ++ [y]))
    (hs : IsSum vs (fun rs => S (rs ++ [0])) c) : IsSum (vs ++ [w]) S c := by
  refine isSum_snoc w vs S (fun rs => S (rs ++ [0])) c (fun rs => ?_) hs
  obtain ⟨q, hd, hev⟩ := h rs
  refine ⟨q, hd, ?_, hev⟩
  rw [hw q hd, hev 0]
  ring

/-- Two end terms, each under a mask that may depend on the challenges. -/
theorem isSum_Y_mul (w : Wt K) (hw : w.Two 1 0) (h3 : 3 ≤ w.d) (vs : List (Wt K))
    (a b ma mb : List K → K) (c : K) (hs : IsSum vs (fun rs => a rs * b rs) c) (S : List K → K)
    (hS : ∀ rs y, S (rs ++ [y]) = (a rs + y * ma rs) * (b rs + y * mb rs)) :
    IsSum (vs ++ [w]) S c := by
  refine isSum_Y w hw vs S c (fun rs => ?_) (hs.congr (fun rs => ?_) rfl)
  · refine ⟨(C (a rs) + X * C (ma rs)) * (C (b rs) + X * C (mb rs)), ?_, fun y => ?_⟩
    · refine lt_of_le_of_lt ?_ (show 2 < w.d by omega)
      have h1 : ∀ u v : K, (C u + X * C v : K[X]).natDegree ≤ 1 := fun u v => by
        refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
        refine le_trans natDegree_mul_le ?_
        have hx : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
        have hc : (C v : K[X]).natDegree = 0 := natDegree_C v
        omega
      refine le_trans natDegree_mul_le ?_
      have := h1 (a rs) (ma rs)
      have := h1 (b rs) (mb rs)
      omega
    · rw [hS]
      simp only [eval_mul, eval_add, eval_C, eval_X]
  · rw [hS]
    ring

/-- A summand that is affine in the further variable. -/
theorem isSum_Y_lin (w : Wt K) (hw : w.Two 1 0) (h2 : 2 ≤ w.d) (vs : List (Wt K))
    (s m : List K → K) (c : K) (hs : IsSum vs s c) (S : List K → K)
    (hS : ∀ rs y, S (rs ++ [y]) = s rs + y * m rs) : IsSum (vs ++ [w]) S c := by
  refine isSum_Y w hw vs S c (fun rs => ?_) (hs.congr (fun rs => ?_) rfl)
  · refine ⟨C (s rs) + X * C (m rs), ?_, fun y => ?_⟩
    · refine lt_of_le_of_lt ?_ (show 1 < w.d by omega)
      refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
      refine le_trans natDegree_mul_le ?_
      have hx : (X : K[X]).natDegree ≤ 1 := natDegree_X_le
      have hc : (C (m rs) : K[X]).natDegree = 0 := natDegree_C _
      omega
    · rw [hS]
      simp only [eval_mul, eval_add, eval_C, eval_X]
  · rw [hS]
    ring

end OnBytes.Desc.First.P1
