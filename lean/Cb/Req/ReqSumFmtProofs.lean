-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqSumFmtProofs.lean: the proofs of Cb/Req/ReqSumFmt.lean, which computes the numbers of the
sumcheck for a family of conditions from the family's lists.

Main names (statements and hypotheses: Cb/Req/ReqSumFmt.lean):
  `nc_eq`: in a family whose terms name atoms below na there are na vector maps.
  `summand_eq`, `summand_deg`, `summand_corner`: the law of the steps; the degree; the value at a
    vertex.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req.ReqSumFmt
import Cb.Req.ReqSumCubeProofs
import Cb.Req.ReqSumTermsProofs
import Cb.Req.ReqSpecProofs

set_option autoImplicit false

namespace Cb.Req
open Blocks Alg Finset

/-! ## Numbers -/

theorem maxAtom_le {n : ℕ} : ∀ (as : List (List ℕ)), (∀ l ∈ as, ∀ j ∈ l, j < n) → maxAtom as ≤ n
  | [], _ => Nat.zero_le n
  | a :: ts, h => by
      have hin : ∀ (l : List ℕ), (∀ j ∈ l, j < n) → (l.map (· + 1)).foldr max 0 ≤ n := by
        intro l
        induction l with
        | nil => intro _; exact Nat.zero_le n
        | cons x r ihr =>
          intro hl
          simp only [List.map_cons, List.foldr_cons]
          have h1 := hl x (by simp)
          have h2 := ihr fun j hj => hl j (List.mem_cons_of_mem x hj)
          omega
      have h1 := hin a (h a (by simp))
      have h2 := maxAtom_le ts fun l hl => h l (List.mem_cons_of_mem a hl)
      unfold maxAtom at h2 ⊢
      simp only [List.map_cons, List.foldr_cons]
      omega

theorem nc_eq : Spec.nc_eq := by
  intro X E f h
  have h1 : maxAtom f.lists ≤ f.na := maxAtom_le f.lists fun l hl j hj => by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
    exact h t ht j hj
  unfold Fam.nc
  omega

theorem lt_nc {X E : Type} (f : Fam X E) : ∀ l ∈ f.lists, ∀ j ∈ l, j < f.nc := fun l hl j hj =>
  Nat.lt_of_lt_of_le (lt_maxAtom f.lists l hl j hj) (Nat.le_max_right _ _)

/-! ## The summand -/

section
variable {X E : Type} [Field E]

theorem sum_range_getD {α : Type} (Y : ℕ → E) (a : α → E) (b : α → List ℕ) :
    ∀ L : List α,
      ((List.range L.length).map fun k =>
          (L.map a).getD k 0 * (((L.map b).getD k []).map Y).prod).sum =
        (L.map fun t => a t * ((b t).map Y).prod).sum
  | [] => rfl
  | t :: L => by
      rw [List.length_cons, List.range_succ_eq_map]
      simp only [List.map_cons, List.sum_cons, List.map_map]
      rw [← sum_range_getD Y a b L]
      rfl

theorem summand_eq : Spec.summand_eq := by
  intro X E _ f x u z
  have h := out_stepsOf E f.nc f.lists (f.coefAt x (nat z)) (fun j => mle (u j) z) (lt_nc f)
  have e : Req.summand f x u z =
      (stepsOf f.nc f.lists (f.coefAt x (nat z))).out fun j => mle (u j) z := rfl
  rw [e, h]
  have h2 := sum_range_getD (fun j => mle (u j) z)
    (fun t : Term X E => ext f.v (t.coef x) (nat z)) Term.atoms f.terms
  rw [← h2]
  unfold Fam.lists
  rw [List.length_map]
  rfl

theorem degLE_listSum {ι α : Type} [DecidableEq ι] {d : ι → ℕ} (g : α → (ι → E) → E) :
    ∀ L : List α, (∀ t ∈ L, DegLE d (g t)) → DegLE d fun z => (L.map fun t => g t z).sum
  | [], _ => DegLE.const d 0
  | t :: L, h => by
      simp only [List.map_cons, List.sum_cons]
      exact (h t (by simp)).add (degLE_listSum g L fun s hs => h s (List.mem_cons_of_mem t hs))

theorem degLE_listProd {ι : Type} [Fintype ι] [DecidableEq ι] (u : ℕ → (ι → Bool) → E) :
    ∀ l : List ℕ, DegLE (fun _ => l.length) fun z : ι → E => (l.map fun j => mle (u j) z).prod
  | [] => DegLE.const _ 1
  | j :: l => by
      simp only [List.map_cons, List.prod_cons]
      exact ((DegLE.mle (u j)).mul (degLE_listProd u l)).mono fun _ => by
        simp only [List.length_cons]; omega

theorem summand_deg : Spec.summand_deg := by
  intro X E _ f x u
  have e : Req.summand f x u =
      fun z =>
        (f.terms.map fun t =>
          (fun z : Fin f.v → E =>
              ext f.v (t.coef x) (nat z) * (t.atoms.map fun j => mle (u j) z).prod) z).sum :=
    funext fun z => summand_eq X E f x u z
  rw [e]
  refine degLE_listSum _ f.terms fun t ht => ?_
  have e1 : (fun z : Fin f.v → E =>
        ext f.v (t.coef x) (nat z) * (t.atoms.map fun j => mle (u j) z).prod) =
      fun z =>
        mle (fun b : Fin f.v → Bool => t.coef x (num b)) z *
            (t.atoms.map fun j => mle (u j) z).prod :=
    funext fun z => by rw [ext_nat]
  rw [e1]
  refine ((DegLE.mle _).mul (degLE_listProd u t.atoms)).mono fun _ => ?_
  have := le_maxLen f.lists t.atoms (List.mem_map_of_mem ht)
  unfold Fam.deg
  omega

theorem summand_corner : Spec.summand_corner := by
  intro X E _ f x u b
  rw [summand_eq]
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  rw [ext_nat E f.v (t.coef x) (corner b), mle_corner]
  simp only [mle_corner]
  rfl

end

/-! ## The end set -/

theorem inEnd_false {X E : Type} (f : Fam X E) {j : ℕ} (h : f.inEnd j = false) :
    ∃ g, f.atom j = .base (.cell g) := by
  unfold Fam.inEnd at h
  split at h
  · split at h
    · exact ⟨_, by assumption⟩
    · exact absurd h (by simp)
  · exact absurd h (by simp)

theorem inEnd_cell {X E : Type} (f : Fam X E) {j : ℕ} (hj : j < f.nc)
    {g : ℕ → CForm E} (h : f.atom j = .base (.cell g)) : f.inEnd j = false := by
  unfold Fam.inEnd
  rw [if_pos hj, h]

theorem inEnd_aux {X E : Type} (f : Fam X E) {j : ℕ} (hj : ¬ j < f.nc) : f.inEnd j = true := by
  unfold Fam.inEnd
  rw [if_neg hj]

end Cb.Req
