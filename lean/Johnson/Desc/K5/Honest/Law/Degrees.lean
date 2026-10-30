-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K5/Honest/Law/Degrees.lean: CONDITIONAL: how high the degree of a summand's round
polynomial is, READ IN A FIELD, where only some of a term's letters move with the round's variable.
Definitions of propositions, and statements with their proofs. rho: any reading
(OnBytes/Model/HideLaws.lean).

Why. The function that makes a round polynomial (Summand.round, Johnson/Desc/K5/Honest/Terms.lean)
multiplies one line for a term's coefficient and one for each of its factors, so its list has two
members more than the term has factors, at every variable. A sumcheck may keep fewer coefficients at
a variable. What is then dropped reads 0 if few enough of the lines have a slope: a line through two
values that read the same has a slope that reads 0.

Main names:
  Deg.Aff v F, Deg.Free v F   a function F of a point in the field is of degree at most 1 in
                  coordinate v; it does not read coordinate v
  Deg.Free.aff .. Deg.aff_eqPt   a small calculus: constants, coordinates, sums, products, a product
                  in which one member alone reads the coordinate, the library's equality weights
  ptL             a list of the program's elements, read, as a point
  Still           read, a function of a list takes the same value at 0 and at 1 in a coordinate
  affine_of_reads, still_of_reads   from a function of the read point to a function of the list
  natDegree_line_le, Summand.natDegree_termLine_le, Summand.coeff_lines_zero
                  the degree of a line; of a term's polynomial; of the sum of all terms'
  Summand.cut_of_still   **the statement**: weights 0 or more on a term's coefficient and factors;
                  weight 0 only on what is still; then the round polynomial's coefficients from
                  (the greatest sum of a term's weights) + 1 on read 0

Summand.cut_of_still is CONDITIONAL: on a skeleton that does not depend on the point
(Summand.Uniform, Johnson/Desc/K5/Honest/Law/TermsLaw.lean), and on the stillness of every letter of
weight 0; the round is one of the summand's, and d lies above each term's sum of weights. The caller
pays these.
Limits. No summand of the protocol is spoken of. No property is claimed by a definition.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.K5.Honest.Law.TermsLaw
import Inst.Model.Att.Sums

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Honest
open OnBytes (E addE subE mulE zeroE oneE)
open OnBytes.Model (Reading)
open VerifiableInference.Desc.Part.MaskedSum (polyOf polyOf_coeff)
open Polynomial

variable {K : Type} [Field K]

/-! ## 1 Functions of a point in the field -/

namespace Deg

/-- F is of degree at most 1 in coordinate v. -/
def Aff (v : ℕ) (F : (ℕ → K) → K) : Prop :=
  ∀ (ξ : ℕ → K) (r : K), F (Function.update ξ v r) =
    (1 - r) * F (Function.update ξ v 0) + r * F (Function.update ξ v 1)

/-- F does not read coordinate v. -/
def Free (v : ℕ) (F : (ℕ → K) → K) : Prop :=
  ∀ (ξ : ℕ → K) (r : K), F (Function.update ξ v r) = F ξ

variable {v : ℕ} {F G : (ℕ → K) → K}

theorem Free.aff (h : Free v F) : Aff v F := fun ξ r => by
  rw [h ξ r, h ξ 0, h ξ 1]
  ring

omit [Field K] in
theorem free_const (c : K) : Free v fun _ => c := fun _ _ => rfl

omit [Field K] in
theorem free_coord {i : ℕ} (h : i ≠ v) : Free v fun ξ : ℕ → K => ξ i := fun ξ r =>
  Function.update_of_ne h r ξ

theorem aff_coord (i : ℕ) : Aff v fun ξ : ℕ → K => ξ i := by
  by_cases h : i = v
  · subst h
    intro ξ r
    simp only [Function.update_self]
    ring
  · exact (free_coord h).aff

theorem Free.add (hF : Free v F) (hG : Free v G) : Free v fun ξ => F ξ + G ξ := fun ξ r => by
  show F _ + G _ = _
  rw [hF ξ r, hG ξ r]

theorem Free.sub (hF : Free v F) (hG : Free v G) : Free v fun ξ => F ξ - G ξ := fun ξ r => by
  show F _ - G _ = _
  rw [hF ξ r, hG ξ r]

theorem Free.mul (hF : Free v F) (hG : Free v G) : Free v fun ξ => F ξ * G ξ := fun ξ r => by
  show F _ * G _ = _
  rw [hF ξ r, hG ξ r]

theorem Free.sum {ι : Type} (s : Finset ι) {Φ : ι → (ℕ → K) → K} (h : ∀ k ∈ s, Free v (Φ k)) :
    Free v fun ξ => ∑ k ∈ s, Φ k ξ := fun ξ r => Finset.sum_congr rfl fun k hk => h k hk ξ r

theorem Free.prod {ι : Type} (s : Finset ι) {Φ : ι → (ℕ → K) → K} (h : ∀ k ∈ s, Free v (Φ k)) :
    Free v fun ξ => ∏ k ∈ s, Φ k ξ := fun ξ r => Finset.prod_congr rfl fun k hk => h k hk ξ r

theorem Aff.add (hF : Aff v F) (hG : Aff v G) : Aff v fun ξ => F ξ + G ξ := fun ξ r => by
  show F _ + G _ = _
  rw [hF ξ r, hG ξ r]
  ring

theorem Aff.sub (hF : Aff v F) (hG : Aff v G) : Aff v fun ξ => F ξ - G ξ := fun ξ r => by
  show F _ - G _ = _
  rw [hF ξ r, hG ξ r]
  ring

theorem Aff.mul_free (hF : Aff v F) (hG : Free v G) : Aff v fun ξ => F ξ * G ξ := fun ξ r => by
  show F _ * G _ = (1 - r) * (F _ * G _) + r * (F _ * G _)
  rw [hF ξ r, hG ξ r, hG ξ 0, hG ξ 1]
  ring

theorem Free.mul_aff (hF : Free v F) (hG : Aff v G) : Aff v fun ξ => F ξ * G ξ := fun ξ r => by
  show F _ * G _ = (1 - r) * (F _ * G _) + r * (F _ * G _)
  rw [hG ξ r, hF ξ r, hF ξ 0, hF ξ 1]
  ring

theorem Aff.sum {ι : Type} (s : Finset ι) {Φ : ι → (ℕ → K) → K} (h : ∀ k ∈ s, Aff v (Φ k)) :
    Aff v fun ξ => ∑ k ∈ s, Φ k ξ := fun ξ r => by
  show ∑ k ∈ s, Φ k _ = (1 - r) * ∑ k ∈ s, Φ k _ + r * ∑ k ∈ s, Φ k _
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k hk => h k hk ξ r

/-- **A product in which one member alone reads the coordinate**, and that one with degree at most
1. -/
theorem Aff.prod_one {ι : Type} [DecidableEq ι] (s : Finset ι) {Φ : ι → (ℕ → K) → K} (k0 : ι)
    (h0 : Aff v (Φ k0)) (h : ∀ k ∈ s, k ≠ k0 → Free v (Φ k)) :
    Aff v fun ξ => ∏ k ∈ s, Φ k ξ := by
  by_cases hk : k0 ∈ s
  · have e : (fun ξ => ∏ k ∈ s, Φ k ξ) = fun ξ => Φ k0 ξ * ∏ k ∈ s.erase k0, Φ k ξ := by
      funext ξ
      exact (Finset.mul_prod_erase s (fun k => Φ k ξ) hk).symm
    rw [e]
    exact h0.mul_free (Free.prod _ fun k hk' =>
      h k (Finset.mem_of_mem_erase hk') (Finset.ne_of_mem_erase hk'))
  · exact (Free.prod s fun k hk' => h k hk' fun e => hk (e ▸ hk')).aff

/-! ### The library's equality weights -/

/-- An equality weight does not read a coordinate outside its stretch. -/
theorem free_eqN (m off z : ℕ) (h : v < off ∨ off + m ≤ v) :
    Free v fun ξ : ℕ → K => Blocks.eqN m off ξ z := by
  unfold Blocks.eqN
  refine Free.prod _ fun t ht => ?_
  have ht' := Finset.mem_range.mp ht
  have hc : Free v fun ξ : ℕ → K => ξ (off + t) := free_coord (by omega)
  by_cases hb : z.testBit (m - 1 - t)
  · simpa only [if_pos hb] using hc
  · simpa only [if_neg hb] using (free_const (1 : K)).sub hc

/-- An equality weight is of degree at most 1 in each coordinate. -/
theorem aff_eqN (m off z : ℕ) : Aff v fun ξ : ℕ → K => Blocks.eqN m off ξ z := by
  unfold Blocks.eqN
  have one : ∀ t, Aff v fun ξ : ℕ → K =>
      if z.testBit (m - 1 - t) then ξ (off + t) else 1 - ξ (off + t) := fun t => by
    by_cases hb : z.testBit (m - 1 - t)
    · simpa only [if_pos hb] using aff_coord (K := K) (v := v) (off + t)
    · simpa only [if_neg hb] using (free_const (1 : K)).aff.sub (aff_coord (off + t))
  refine Aff.prod_one _ (v - off) (one _) fun t _ hne => ?_
  have hc : Free v fun ξ : ℕ → K => ξ (off + t) := free_coord (by omega)
  by_cases hb : z.testBit (m - 1 - t)
  · simpa only [if_pos hb] using hc
  · simpa only [if_neg hb] using (free_const (1 : K)).sub hc

open Inst.Model.AttSeg (eqPt eq1 sh)

/-- The equality polynomial of a fixed point and a stretch of the point. -/
theorem free_eqPt (n a : ℕ) (u : ℕ → K) (h : v < a ∨ a + n ≤ v) :
    Free v fun ξ : ℕ → K => eqPt n u (sh ξ a) := by
  unfold eqPt eq1 sh
  refine Free.prod _ fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  have hc : Free v fun ξ : ℕ → K => ξ (a + k) := free_coord (by omega)
  exact ((free_const (u k)).mul hc).add
    ((free_const (1 - u k)).mul ((free_const (1 : K)).sub hc))

theorem aff_eqPt (n a : ℕ) (u : ℕ → K) : Aff v fun ξ : ℕ → K => eqPt n u (sh ξ a) := by
  unfold eqPt eq1 sh
  have one : ∀ k, Aff v fun ξ : ℕ → K => u k * ξ (a + k) + (1 - u k) * (1 - ξ (a + k)) :=
    fun k => ((free_const (u k)).mul_aff (aff_coord (a + k))).add
      ((free_const (1 - u k)).mul_aff ((free_const (1 : K)).aff.sub (aff_coord (a + k))))
  refine Aff.prod_one _ (v - a) (one _) fun k _ hne => ?_
  have hc : Free v fun ξ : ℕ → K => ξ (a + k) := free_coord (by omega)
  exact ((free_const (u k)).mul hc).add
    ((free_const (1 - u k)).mul ((free_const (1 : K)).sub hc))

end Deg

/-! ## 2 From a function of the read point to a function of the list -/

variable (ρ : Reading K)

/-- A list of the program's elements, read, as a point: 0 past its end. -/
def ptL (x : List E) : ℕ → K := fun i => ρ.val (x.getD i zeroE)

/-- Laying s into place number a.length of a list lays its reading into the point. -/
theorem ptL_at (a y : List E) (s s' : E) :
    ptL ρ (a ++ s :: y) = Function.update (ptL ρ (a ++ s' :: y)) a.length (ρ.val s) := by
  funext i
  by_cases hi : i = a.length
  · rw [hi, Function.update_self]
    exact congrArg ρ.val (Lists.getD_at zeroE s a y)
  · rw [Function.update_of_ne hi]
    exact congrArg ρ.val (Lists.getD_mid zeroE s s' a y i hi)

/-- **Read, f takes the same value at 0 and at 1 in coordinate number v, from 0, of n.** -/
def Still (n v : Nat) (f : List E → E) : Prop :=
  ∀ a y : List E, a.length = v → a.length + 1 + y.length = n →
    ρ.val (f (a ++ zeroE :: y)) = ρ.val (f (a ++ oneE :: y))

section Bridge
variable {n v : Nat} {f : List E → E} {F : (ℕ → K) → K}

private theorem len_at {n : Nat} (a y : List E) (s : E) (h : a.length + 1 + y.length = n) :
    (a ++ s :: y).length = n := by
  rw [List.length_append, List.length_cons]
  omega

/-- Where f reads as a function of the read point that is of degree at most 1 in coordinate v. -/
theorem affine_of_reads (h : ∀ x : List E, x.length = n → ρ.val (f x) = F (ptL ρ x))
    (hF : Deg.Aff v F) : Affine ρ n v f := by
  intro a y r ha hn
  rw [h _ (len_at a y r hn), h _ (len_at a y zeroE hn), h _ (len_at a y oneE hn),
    ptL_at ρ a y r zeroE, ptL_at ρ a y oneE zeroE, ρ.one, ha, hF _ (ρ.val r)]
  have e : Function.update (ptL ρ (a ++ zeroE :: y)) v 0 = ptL ρ (a ++ zeroE :: y) := by
    rw [← ha, ← ρ.zero, ← ptL_at ρ a y zeroE zeroE]
  rw [e]

/-- Where f reads as a function of the read point that does not read coordinate v. -/
theorem still_of_reads (h : ∀ x : List E, x.length = n → ρ.val (f x) = F (ptL ρ x))
    (hF : Deg.Free v F) : Still ρ n v f := by
  intro a y ha hn
  rw [h _ (len_at a y zeroE hn), h _ (len_at a y oneE hn), ptL_at ρ a y oneE zeroE, ha, hF]

end Bridge

/-! ## 3 The degree of a product of lines -/

/-- A list sum's coefficient is 0 where each member's is. -/
private theorem coeff_list_sum_zero (j : ℕ) : ∀ l : List K[X], (∀ p ∈ l, p.coeff j = 0) →
    l.sum.coeff j = 0
  | [], _ => by simp
  | p :: l, h => by
    rw [List.sum_cons, coeff_add, h p List.mem_cons_self,
      coeff_list_sum_zero j l fun q hq => h q (List.mem_cons_of_mem _ hq), add_zero]

/-- A fold that multiplies by the list g f for each member f, from p on, as a polynomial. -/
theorem polyOf_foldl_mulP {α : Type} (g : α → List E) : ∀ (l : List α) (p : List E),
    polyOf ρ (l.foldl (fun p f => mulP p (g f)) p) =
      polyOf ρ p * (l.map fun f => polyOf ρ (g f)).prod
  | [], p => by simp
  | f :: l, p => by
    rw [List.foldl_cons, polyOf_foldl_mulP g l, polyOf_mulP, List.map_cons, List.prod_cons,
      mul_assoc]

/-- **The degree of a line** is at most any w that is 0 only if the two values read the same. -/
theorem natDegree_line_le (v0 v1 : E) (w : ℕ) (h : w = 0 → ρ.val v0 = ρ.val v1) :
    (polyOf ρ (lineP v0 v1)).natDegree ≤ w := by
  rw [polyOf_lineP]
  by_cases hw : w = 0
  · rw [h hw, sub_self, C_0, mul_zero, add_zero, natDegree_C]
    exact Nat.zero_le w
  · refine le_trans (natDegree_add_le _ _) (max_le (by rw [natDegree_C]; exact Nat.zero_le w) ?_)
    refine le_trans natDegree_mul_le ?_
    rw [natDegree_C, add_zero]
    exact le_trans natDegree_X_le (by omega)

/-- A sum over two lists of one length, side by side, member by member below a bound. -/
private theorem sum_zip_le {α β : Type} (da : α) (db : β) (g : α × β → ℕ) :
    ∀ (a : List α) (b : List β) (w : ℕ → ℕ), a.length = b.length →
      (∀ i, i < a.length → g (a.getD i da, b.getD i db) ≤ w i) →
      ((a.zip b).map g).sum ≤ ∑ i ∈ Finset.range a.length, w i
  | [], [], _, _, _ => by simp
  | x :: a, y :: b, w, h, hw => by
    rw [List.zip_cons_cons, List.map_cons, List.sum_cons, List.length_cons,
      Finset.sum_range_succ', add_comm]
    refine Nat.add_le_add (sum_zip_le da db g a b (fun i => w (i + 1)) (by simpa using h)
      fun i hi => ?_) (hw 0 (by simp))
    have := hw (i + 1) (by simpa using hi)
    simpa only [List.getD_cons_succ] using this
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h

/-- A member of two lists laid side by side is a pair of members of one number. -/
private theorem mem_zip_getD {α : Type} (d : α) : ∀ (a b : List α) (p : α × α), p ∈ a.zip b →
    ∃ i, p = (a.getD i d, b.getD i d)
  | [], _, p, h => by simp at h
  | _ :: _, [], p, h => by simp at h
  | x :: a, y :: b, p, h => by
    rw [List.zip_cons_cons] at h
    rcases List.mem_cons.1 h with h | h
    · exact ⟨0, h⟩
    · obtain ⟨i, hi⟩ := mem_zip_getD d a b p h
      exact ⟨i + 1, by simpa only [List.getD_cons_succ] using hi⟩

/-- **The degree of a term's polynomial**: at most the sum of weights wc, wf 0, wf 1, .., of which
one is 0 only if that letter's two values read the same. -/
theorem Summand.natDegree_termLine_le (S : Summand) (x0 x1 : List E) (t0 t1 : Term) (wc : ℕ)
    (wf : ℕ → ℕ) (hl : t0.fs.length = t1.fs.length) (hc : wc = 0 → ρ.val t0.c = ρ.val t1.c)
    (hf : ∀ i, wf i = 0 → ρ.val (S.factorAt x0 (t0.fs.getD i ⟨zeroE, 0, zeroE⟩)) =
      ρ.val (S.factorAt x1 (t1.fs.getD i ⟨zeroE, 0, zeroE⟩))) :
    (polyOf ρ (S.termLine x0 x1 t0 t1)).natDegree ≤
      wc + ∑ i ∈ Finset.range t0.fs.length, wf i := by
  unfold Summand.termLine
  rw [polyOf_foldl_mulP ρ fun f : Factor × Factor =>
    lineP (S.factorAt x0 f.1) (S.factorAt x1 f.2)]
  refine le_trans natDegree_mul_le (Nat.add_le_add (natDegree_line_le ρ _ _ wc hc) ?_)
  refine le_trans (natDegree_list_prod_le _) ?_
  rw [List.map_map]
  exact sum_zip_le (⟨zeroE, 0, zeroE⟩ : Factor) (⟨zeroE, 0, zeroE⟩ : Factor)
    (natDegree ∘ fun f : Factor × Factor =>
      polyOf ρ (lineP (S.factorAt x0 f.1) (S.factorAt x1 f.2))) t0.fs t1.fs wf hl
    fun i _ => natDegree_line_le ρ _ _ (wf i) (hf i)

/-- The like for the sum of all terms' polynomials at two points: every coefficient from d on reads
0. -/
theorem Summand.coeff_lines_zero (S : Summand) (x0 x1 : List E) (d : ℕ) (wc : ℕ → ℕ)
    (wf : ℕ → ℕ → ℕ) (hl : ∀ t, (S.termAt x0 t).fs.length = (S.termAt x1 t).fs.length)
    (hc : ∀ t, wc t = 0 → ρ.val (S.coefAt t x0) = ρ.val (S.coefAt t x1))
    (hf : ∀ t i, wf t i = 0 → ρ.val (S.facAt t i x0) = ρ.val (S.facAt t i x1))
    (hd : ∀ t, wc t + ∑ i ∈ Finset.range (S.termAt x0 t).fs.length, wf t i < d) (j : ℕ)
    (hj : d ≤ j) :
    (polyOf ρ (sumP (((S.terms x0).zip (S.terms x1)).map
      fun t => S.termLine x0 x1 t.1 t.2))).coeff j = 0 := by
  rw [polyOf_sumP]
  refine coeff_list_sum_zero j _ fun p hp => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hp
  obtain ⟨tt, ht, rfl⟩ := List.mem_map.1 hg
  obtain ⟨t, ht'⟩ := mem_zip_getD (⟨zeroE, []⟩ : Term) _ _ tt ht
  have e1 : tt.1 = S.termAt x0 t := congrArg Prod.fst ht'
  have e2 : tt.2 = S.termAt x1 t := congrArg Prod.snd ht'
  rw [e1, e2]
  exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt
    (S.natDegree_termLine_le ρ x0 x1 _ _ (wc t) (wf t) (hl t) (hc t) (hf t))
    (lt_of_lt_of_le (hd t) hj))

/-- **What lies beyond a round polynomial's true degree reads 0.** CONDITIONAL on: the skeleton does
not depend on the point; wc and wf lay a weight on each term's coefficient and on each of its
factors, and a letter of weight 0 takes, read, the same value at 0 and at 1 in the round's variable;
each term's weights add up to less than d. Then every coefficient from number d on reads 0. -/
theorem Summand.cut_of_still (S : Summand) (hU : S.Uniform) (rs : List E) (h : rs.length < S.vars)
    (d : ℕ) (wc : ℕ → ℕ) (wf : ℕ → ℕ → ℕ)
    (hc : ∀ t, wc t = 0 → Still ρ S.vars rs.length (S.coefAt t))
    (hf : ∀ t j, wf t j = 0 → Still ρ S.vars rs.length (S.facAt t j))
    (hd : ∀ x : List E, x.length = S.vars → ∀ t,
      wc t + ∑ j ∈ Finset.range (S.termAt x t).fs.length, wf t j < d) :
    ∀ j, d ≤ j → ρ.val ((S.round rs).getD j zeroE) = 0 := by
  intro j hj
  rw [← polyOf_coeff]
  unfold Summand.round
  rw [polyOf_sumP]
  refine coeff_list_sum_zero j _ fun p hp => ?_
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hp
  obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hg
  have hl : rs.length + 1 + y.length = S.vars := by
    rw [length_of_mem_cube _ y hy]
    omega
  exact S.coeff_lines_zero ρ (rs ++ zeroE :: y) (rs ++ oneE :: y) d wc wf
    (hU.factors (len_at rs y zeroE hl) (len_at rs y oneE hl))
    (fun t e => hc t e rs y rfl hl) (fun t i e => hf t i e rs y rfl hl)
    (hd _ (len_at rs y zeroE hl)) j hj

end H2K5.Honest

#print axioms H2K5.Honest.Deg.Free.aff
#print axioms H2K5.Honest.Deg.free_const
#print axioms H2K5.Honest.Deg.free_coord
#print axioms H2K5.Honest.Deg.aff_coord
#print axioms H2K5.Honest.Deg.Free.add
#print axioms H2K5.Honest.Deg.Free.sub
#print axioms H2K5.Honest.Deg.Free.mul
#print axioms H2K5.Honest.Deg.Free.sum
#print axioms H2K5.Honest.Deg.Free.prod
#print axioms H2K5.Honest.Deg.Aff.add
#print axioms H2K5.Honest.Deg.Aff.sub
#print axioms H2K5.Honest.Deg.Aff.mul_free
#print axioms H2K5.Honest.Deg.Free.mul_aff
#print axioms H2K5.Honest.Deg.Aff.sum
#print axioms H2K5.Honest.Deg.Aff.prod_one
#print axioms H2K5.Honest.Deg.free_eqN
#print axioms H2K5.Honest.Deg.aff_eqN
#print axioms H2K5.Honest.Deg.free_eqPt
#print axioms H2K5.Honest.Deg.aff_eqPt
#print axioms H2K5.Honest.ptL_at
#print axioms H2K5.Honest.affine_of_reads
#print axioms H2K5.Honest.still_of_reads
#print axioms H2K5.Honest.polyOf_foldl_mulP
#print axioms H2K5.Honest.natDegree_line_le
#print axioms H2K5.Honest.Summand.natDegree_termLine_le
#print axioms H2K5.Honest.Summand.coeff_lines_zero
#print axioms H2K5.Honest.Summand.cut_of_still
