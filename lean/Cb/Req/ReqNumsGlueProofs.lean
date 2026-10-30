-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqNumsGlueProofs.lean: the proofs of Cb/Req/ReqNumsGlue.lean.

Main names (statements and hypotheses: Cb/Req/ReqNumsGlue.lean):
  `degLe_to`, `degLe_mask`, `degLe_pub`, `degLe_add`: `Fam.DegLe` at the four steps of gluing.
  `degLe_glue`: `Fam.DegLe` of the glued family.
  `glueN_le`, `degLe_glued`, `v_glued`: the bounds on atoms in a term and on the number of
    variables, at the glued family and the glued segment.
  `numsLe_glued`: `SegSpec.NumsLe` of the glued segment.

Limits: what the head of Cb/Req/ReqNumsGlue.lean lists as not said is not said here either. Its
statements are on data only.
-/
import Cb.Req.ReqNumsGlue
import Cb.Gen.CodeProofsComp
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace Cb.Req
open Blocks Iop Prob Hiop Alg
open scoped ENNReal

theorem maxLen_le {d : ℕ} : ∀ (as : List (List ℕ)), (∀ l ∈ as, l.length ≤ d) → maxLen as ≤ d
  | [], _ => Nat.zero_le d
  | a :: ts, h => by
      have h1 := h a (by simp)
      have h2 := maxLen_le ts fun l hl => h l (List.mem_cons_of_mem a hl)
      unfold maxLen at h2 ⊢
      simp only [List.map_cons, List.foldr_cons]
      omega

theorem deg_le_iff : Spec.deg_le_iff := by
  intro X E f d
  constructor
  · intro h t ht
    exact (le_maxLen f.lists t.atoms (List.mem_map_of_mem ht)).trans h
  · intro h
    refine maxLen_le f.lists fun l hl => ?_
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hl
    exact h t ht

theorem deg_toFam_to {X E : Type} (P : Poly0 X E) (M d : ℕ) (h : P.toFam.deg ≤ d) :
    (P.to M).toFam.deg ≤ d := by
  rw [deg_le_iff] at h ⊢
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 (show t ∈ P.terms.map (Term.low P.v) from ht)
  exact h t' ht'

theorem degLe_to : Spec.degLe_to := by
  intro X E f N d h
  refine ⟨(deg_le_iff X E _ d).2 fun t ht => ?_, fun j w P hj => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 (show t ∈ f.terms.map (Term.low f.v) from ht)
    exact (deg_le_iff X E f d).1 h.1 t' ht'
  · have hj' : (f.atom j).to N f.v = .sum w P := hj
    cases hA : f.atom j with
    | base b =>
      rw [hA] at hj'
      exact absurd hj' (by simp [Atom.to])
    | sum w' P' =>
      rw [hA] at hj'
      have e : Atom.sum w' (P'.to (N + w')) = Atom.sum w P := hj'
      injection e with e1 e2
      subst e2
      exact deg_toFam_to P' _ d (h.2 j w' P' hA)

theorem degLe_mask : Spec.degLe_mask := by
  intro X E _ f c d h
  refine ⟨(deg_le_iff X E _ d).2 fun t ht => ?_, h.2⟩
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1
    (show t ∈ f.terms.map (fun t => (⟨fun x b => c x b * t.coef x b, t.atoms⟩ : Term X E)) from ht)
  exact (deg_le_iff X E f d).1 h.1 t' ht'

theorem degLe_pub : Spec.degLe_pub := by
  intro X E _ v c d
  refine ⟨(deg_le_iff X E _ d).2 fun t ht => ?_, fun j w P hj => ?_⟩
  · obtain rfl : t = ⟨c, []⟩ := by simpa [Fam.pub] using ht
    exact Nat.zero_le d
  · exact absurd hj (by simp [Fam.pub])

theorem degLe_add : Spec.degLe_add := by
  intro X E f g d hf hg
  refine ⟨(deg_le_iff X E _ d).2 fun t ht => ?_, fun j w P hj => ?_⟩
  · rcases List.mem_append.1
      (show t ∈ f.terms ++ g.terms.map (fun t => (⟨t.coef, t.atoms.map (· + f.na)⟩ : Term X E))
        from ht) with ht | ht
    · exact (deg_le_iff X E f d).1 hf.1 t ht
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
      show (t'.atoms.map (· + f.na)).length ≤ d
      rw [List.length_map]
      exact (deg_le_iff X E g d).1 hg.1 t' ht'
  · have hj' : (if j < f.na then f.atom j else g.atom (j - f.na)) = .sum w P := hj
    by_cases h : j < f.na
    · rw [if_pos h] at hj'
      exact hf.2 j w P hj'
    · rw [if_neg h] at hj'
      exact hg.2 _ w P hj'

theorem degLe_glueFrom {X E : Type} [_root_.Zero E] [One E] [Mul E] (N V d : ℕ) :
    ∀ (L : List (Fam X E)) (i : ℕ), (∀ f ∈ L, f.DegLe d) → (glueFrom N V i L).DegLe d
  | [], _, _ => degLe_pub X E N _ d
  | f :: L, i, h =>
    degLe_add X E _ _ d (degLe_mask X E _ _ d (degLe_to X E f N d (h f (by simp))))
      (degLe_glueFrom N V d L (i + 1) fun g hg => h g (List.mem_cons_of_mem f hg))

theorem degLe_glue : Spec.degLe_glue := fun X E _ _ _ _ L d h =>
  degLe_add X E _ _ d (degLe_pub X E _ _ d) (degLe_glueFrom _ _ d L 0 h)

theorem maxV_le {X E : Type} {V : ℕ} : ∀ (L : List (Fam X E)), (∀ f ∈ L, f.v ≤ V) → maxV L ≤ V
  | [], _ => Nat.zero_le V
  | f :: L, h => by
      have h1 := h f (by simp)
      have h2 := maxV_le L fun g hg => h g (List.mem_cons_of_mem f hg)
      unfold maxV at h2 ⊢
      simp only [List.map_cons, List.foldr_cons]
      omega

theorem glueN_le : Spec.glueN_le := fun _ _ L _ h => Nat.add_le_add_left (maxV_le L h) _

theorem degLe_glued : Spec.degLe_glued := by
  intro X F E _ _ _ S d hi hk
  classical
  refine ⟨fun f hf => ?_, fun k hk' => ?_⟩
  · obtain rfl : f = Fam.glue 0 S.idn := by simpa [SegSpec.glued] using hf
    exact degLe_glue X E 0 S.idn d hi
  · obtain ⟨T, _, rfl⟩ := List.mem_map.1 hk'
    refine degLe_glue X E _ _ d fun f hf => ?_
    obtain ⟨k, hk2, rfl⟩ := List.mem_map.1 hf
    exact hk k (List.mem_filter.1 hk2).1

theorem v_glued : Spec.v_glued := by
  intro X F E _ _ _ S V hi hk
  classical
  refine ⟨fun f hf => ?_, fun k hk' => ?_⟩
  · obtain rfl : f = Fam.glue 0 S.idn := by simpa [SegSpec.glued] using hf
    exact glueN_le X E S.idn V hi
  · obtain ⟨T, _, rfl⟩ := List.mem_map.1 hk'
    refine (glueN_le X E _ V fun f hf => ?_).trans
      (Nat.add_le_add_right (Nat.clog_mono_right 2 ?_) V)
    · obtain ⟨k, hk2, rfl⟩ := List.mem_map.1 hf
      exact hk k (List.mem_filter.1 hk2).1
    · rw [List.length_map]
      exact List.length_filter_le _ _

theorem numsLe_glued : Spec.numsLe_glued := by
  intro X F E _ _ _ S d V n h hi hk
  obtain ⟨d1, d2⟩ := degLe_glued X F E S d (fun f hf => (h.1 f hf).1) fun k hk' => (h.2 k hk').1
  obtain ⟨v1, v2⟩ := v_glued X F E S V (fun f hf => (h.1 f hf).2) fun k hk' => (h.2 k hk').2
  exact ⟨fun f hf => ⟨d1 f hf, (v1 f hf).trans (Nat.add_le_add_right (Nat.clog_mono_right 2 hi) V)⟩,
    fun k hk' => ⟨d2 k hk', (v2 k hk').trans (Nat.add_le_add_right (Nat.clog_mono_right 2 hk) V)⟩⟩

end Cb.Req
