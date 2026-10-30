-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/TokTables.lean: CONDITIONAL.

Not shown here. That a product's second factor is the same entry of the same table at a point and at
the tokens: a law on the verifier's panels. That the number of tokens is at most 2 ^ lt, and that
the point has lt coordinates: hypotheses on public numbers. Nothing on what the tables hold. Nothing
here is evaluated at an example. No property is claimed.

THE WEIGHT CLAIMS' TABLES AT A TOKEN POINT ARE THE COMBINATION, UNDER THE POINT's EQUALITY WEIGHTS,
OF THE TABLES AT THE TOKENS. The second token sumcheck of the sub-protocol K4 ends at a point z of
the tokens' cube. The honest side makes each weight claim's table at a table et of weights on the
tokens (Sides.weights, Johnson/Desc/K4/Honest/Sides.lean): a table whose unit has no group "cd" does
not read et; the others close that group under the verifier's rotation factor at et (ropeFactor,
OnBytes/Model/LayerPanels.lean), which is a sum over the tokens under et. Here: read in the field,
every entry at eqTab z is the sum over the tokens t of eq(z, t) times that entry at the corner t.

  Comb           x reads as the combination of the xs t under the weights lam.
  ropeSum_comb, rope_comb   the rotation factor's two sums; its entries.
  weights_comb   an entry of a claim's table, general in the weights: they add up to 1.
  at2_comb       the same through at2.
  tok_tables, tok_tables_ext   **at a token point and the tokens' corners.**
  tok_tables_plain   a table whose unit has no group "cd" is the same at all weights: on words.
-/
import Johnson.Road.K4.C.TokWeights
import Johnson.Road.K4.C.Fold
import Johnson.Road.K4.C.StackEnds
import Johnson.Road.FormsKeysQK
import Johnson.Desc.K4.Honest.Sides

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (ClaimEnv)
open OnBytes.Desc.First.K4.Honest (Sides at2)

/-- The honest side's corner of the cube as a point (Johnson/Desc/K4/Honest/Cells.lean), pinned by
its full name: under this namespace the bare name is another function's. -/
local notation "cornerAt" => OnBytes.Desc.First.K4.Honest.bitsOf

/-- x reads as the combination of the xs t, t below n, under the weights lam. This defines a
sentence; the definition claims nothing. -/
def Comb (n : ℕ) (lam : ℕ → Cb.Gl.E) (x : E) (xs : ℕ → E) : Prop :=
  Reading.gl.val x = ∑ t ∈ range n, lam t * Reading.gl.val (xs t)

theorem Comb.zero (n : ℕ) (lam : ℕ → Cb.Gl.E) : Comb n lam zeroE fun _ => zeroE := by
  unfold Comb
  simp [Reading.gl.zero]

theorem Comb.const {n : ℕ} {lam : ℕ → Cb.Gl.E} (h1 : ∑ t ∈ range n, lam t = 1) (x : E) :
    Comb n lam x fun _ => x := by
  unfold Comb
  rw [← Finset.sum_mul, h1, one_mul]

/-- A sum of products whose first factors are combinations and whose second are the same. -/
theorem Comb.sum_mul {n : ℕ} {lam : ℕ → Cb.Gl.E} (m : ℕ) (a : ℕ → E) (as : ℕ → ℕ → E)
    (b : ℕ → Cb.Gl.E) (h : ∀ j < m, Comb n lam (a j) fun t => as t j) :
    ∑ j ∈ range m, Reading.gl.val (a j) * b j =
      ∑ t ∈ range n, lam t * ∑ j ∈ range m, Reading.gl.val (as t j) * b j := by
  have e : ∀ j ∈ range m, Reading.gl.val (a j) * b j =
      ∑ t ∈ range n, lam t * (Reading.gl.val (as t j) * b j) := by
    intro j hj
    rw [h j (mem_range.mp hj), Finset.sum_mul]
    exact sum_congr rfl fun t _ => mul_assoc _ _ _
  rw [sum_congr rfl e, sum_comm]
  exact sum_congr rfl fun t _ => (Finset.mul_sum _ _ _).symm

section
variable {n : ℕ} {lam : ℕ → Cb.Gl.E} (c : ClaimEnv) (et : Array E) (ets : ℕ → Array E)
  (h : ∀ j < c.v.y.T, Comb n lam (et.getD j zeroE) fun t => (ets t).getD j zeroE)
include h

/-- The rotation factor's sum over the tokens. -/
theorem ropeSum_comb (l i : ℕ) (sine : Bool) :
    Comb n lam (ropeSum c et l i sine) fun t => ropeSum c (ets t) l i sine := by
  unfold Comb ropeSum
  rw [foldl_madd_range Reading.gl (fun t => et.getD t zeroE) _ c.v.y.T]
  rw [Comb.sum_mul c.v.y.T (fun j => et.getD j zeroE) (fun t j => (ets t).getD j zeroE) _ h]
  refine sum_congr rfl fun t _ => ?_
  rw [foldl_madd_range Reading.gl (fun j => (ets t).getD j zeroE) _ c.v.y.T]

/-- **An entry of the rotation factor.** -/
theorem rope_comb (lfc : Array E) (l x : ℕ) :
    Comb n lam ((c.ropeFactor et lfc l).getD x zeroE) fun t =>
      (c.ropeFactor (ets t) lfc l).getD x zeroE := by
  by_cases hx : x < 2 * (c.v.y.h.dh / 2)
  · have hi : x / 2 < c.v.y.h.dh / 2 := by omega
    have hC := ropeSum_comb c et ets h l (x / 2) false
    have hS := ropeSum_comb c et ets h l (x / 2) true
    unfold Comb at hC hS ⊢
    rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
    · have ex : x = 2 * (x / 2) := by omega
      rw [ex, (ropeFactor_getD c et lfc l hi).1, Reading.gl.add, Reading.gl.mul, Reading.gl.mul,
        hC, hS, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine sum_congr rfl fun t _ => ?_
      beta_reduce
      rw [(ropeFactor_getD c (ets t) lfc l hi).1, Reading.gl.add, Reading.gl.mul, Reading.gl.mul]
      ring
    · have ex : x = 2 * (x / 2) + 1 := by omega
      rw [ex, (ropeFactor_getD c et lfc l hi).2, Reading.gl.sub, Reading.gl.mul, Reading.gl.mul,
        hC, hS, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_sub_distrib]
      refine sum_congr rfl fun t _ => ?_
      beta_reduce
      rw [(ropeFactor_getD c (ets t) lfc l hi).2, Reading.gl.sub, Reading.gl.mul, Reading.gl.mul]
      ring
  · have e : ∀ u : Array E, (c.ropeFactor u lfc l).getD x zeroE = zeroE := fun u =>
      getD_ge _ (by rw [ropeFactor_size]; omega) zeroE
    rw [e et]
    simp only [e]
    exact Comb.zero n lam

end

section
variable {n : ℕ} {lam : ℕ → Cb.Gl.E} (S : Sides) (et : Array E) (ets : ℕ → Array E)
  (h : ∀ j < S.ce.v.y.T, Comb n lam (et.getD j zeroE) fun t => (ets t).getD j zeroE)
  (h1 : ∑ t ∈ range n, lam t = 1)
include h h1

/-- **An entry of a weight claim's table**, general in the weights. -/
theorem weights_comb (a i : ℕ) :
    Comb n lam (((S.weights et).getD a #[]).getD i zeroE) fun t =>
      ((S.weights (ets t)).getD a #[]).getD i zeroE := by
  unfold Sides.weights
  by_cases ha : a < S.opens.size
  · simp only [getD_map_lt S.opens _ ha #[] {}]
    by_cases hc : ((S.opens.getD a {}).cd == 0) = true
    · simp only [hc, if_true]
      exact Comb.const h1 _
    · simp only [hc, Bool.false_eq_true, if_false]
      by_cases hi : i < (S.opens.getD a {}).kk
      · simp only [getD_range_map _ _ _ _ hi]
        unfold Comb
        rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum,
          Comb.sum_mul (S.opens.getD a {}).cd
            (fun x => (S.ce.ropeFactor et S.lfc (S.opens.getD a {}).lam).getD x zeroE)
            (fun t x => (S.ce.ropeFactor (ets t) S.lfc (S.opens.getD a {}).lam).getD x zeroE) _
            fun x _ => rope_comb S.ce et ets h S.lfc _ x]
        refine sum_congr rfl fun t _ => ?_
        rw [gl_foldl_maddE, Reading.gl.zero, zero_add, range_sum]
      · have e : ∀ f : ℕ → E, ((Array.range (S.opens.getD a {}).kk).map f).getD i zeroE = zeroE :=
          fun f => getD_ge _ (by rw [Array.size_map, Array.size_range]; omega) zeroE
        simp only [e]
        exact Comb.zero n lam
  · have e : ∀ f : OnBytes.Desc.First.K4.Honest.Open → Array E,
        ((S.opens.map f).getD a #[]).getD i zeroE = zeroE := fun f => by
      rw [getD_ge _ (by rw [Array.size_map]; omega) #[]]
      rfl
    simp only [e]
    exact Comb.zero n lam

/-- The same through `at2`. -/
theorem at2_comb (a kk hi yv : ℕ) :
    Comb n lam (at2 ((S.weights et).getD a #[]) kk hi yv) fun t =>
      at2 ((S.weights (ets t)).getD a #[]) kk hi yv := by
  unfold at2
  by_cases hy : yv < kk
  · simp only [hy, if_true]
    exact weights_comb S et ets h h1 a _
  · simp only [hy, if_false]
    exact Comb.zero n lam

end

/-- **THE WEIGHT CLAIMS' TABLES AT A TOKEN POINT**: entry (hi, yv) of claim number a's table at the
equality table of z is the sum over the tokens t of eq(z, t) times that entry at the corner t. At
every a, kk, hi, yv. CONDITIONAL on the two hypotheses on public numbers. -/
theorem tok_tables (S : Sides) {lt : ℕ} {z : Array E} (hz : z.size = lt)
    (hT : S.ce.v.y.T ≤ 2 ^ lt) (a kk hi yv : ℕ) :
    Reading.gl.val (at2 ((S.weights (eqTab z)).getD a #[]) kk hi yv) =
      ∑ t ∈ range (2 ^ lt), Blocks.eqN lt 0 (pt Reading.gl z) t *
        Reading.gl.val (at2 ((S.weights (eqTab (cornerAt lt t))).getD a #[]) kk hi yv) :=
  at2_comb S (eqTab z) (fun t => eqTab (cornerAt lt t))
    (fun _ hj => tok_short hz (Nat.lt_of_lt_of_le hj hT)) (sum_eqN_one lt _) a kk hi yv

/-- The same with the multilinear extension written as such. -/
theorem tok_tables_ext (S : Sides) {lt : ℕ} {z : Array E} (hz : z.size = lt)
    (hT : S.ce.v.y.T ≤ 2 ^ lt) (a kk hi yv : ℕ) :
    Reading.gl.val (at2 ((S.weights (eqTab z)).getD a #[]) kk hi yv) =
      Blocks.ext lt (fun t =>
        Reading.gl.val (at2 ((S.weights (eqTab (cornerAt lt t))).getD a #[]) kk hi yv))
        (pt Reading.gl z) := by
  unfold Blocks.ext
  exact tok_tables S hz hT a kk hi yv

/-- **A table whose unit has no group "cd" does not read the weights on the tokens**: on words. -/
theorem tok_tables_plain (S : Sides) (a : ℕ) (hcd : (S.opens.getD a {}).cd = 0)
    (et et' : Array E) : (S.weights et).getD a #[] = (S.weights et').getD a #[] := by
  unfold Sides.weights
  by_cases ha : a < S.opens.size
  · have h0 : ((S.opens.getD a {}).cd == 0) = true := by
      rw [hcd]
      rfl
    simp only [getD_map_lt S.opens _ ha #[] {}, h0, if_true]
  · rw [getD_ge _ (by rw [Array.size_map]; omega) #[],
      getD_ge _ (by rw [Array.size_map]; omega) #[]]

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.Comb.zero
#print axioms OnBytes.Road.K4.C.Comb.const
#print axioms OnBytes.Road.K4.C.Comb.sum_mul
#print axioms OnBytes.Road.K4.C.ropeSum_comb
#print axioms OnBytes.Road.K4.C.rope_comb
#print axioms OnBytes.Road.K4.C.weights_comb
#print axioms OnBytes.Road.K4.C.at2_comb
#print axioms OnBytes.Road.K4.C.tok_tables
#print axioms OnBytes.Road.K4.C.tok_tables_ext
#print axioms OnBytes.Road.K4.C.tok_tables_plain
