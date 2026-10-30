-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req/ReqFamTupleProofs.lean: the proofs of Cb/Req/ReqFamTuple.lean.

The change of instance touches coefficient tables only; the combined family is put together by the
steps of Cb/Req/ReqGlue.lean, whose laws are used as they stand.

Main names (statements and hypotheses: Cb/Req/ReqFamTuple.lean):
  `famT_val`: the value of the combined family.
  `tuple_zero_iff`: the families' vanishing, on their cubes and on the large cube.
  `famT_eq`: `famT L` as `tupFrom (maxV L) 0 L` (statement and hypotheses: this file).
  `tupFrom_val`, `tupFrom_wf`, `tupFrom_places`, `degLe_tupFrom`: the inductions along the list
    (statements and hypotheses: this file).

Limits: what the head of Cb/Req/ReqFamTuple.lean lists as not said is not said here either.
-/
import Cb.Req.ReqFamTuple
import Cb.Req.ReqGlueProofs
import Cb.Req.ReqNumsGlueProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Cb
open Blocks Hiop Finset Cb.Req

section
variable {X X' F E : Type} [Field F] [Field E] [Algebra F E] (π : X' → X) (Φ : IdxFmt F)

theorem Term.reX_val (t : Term X E) (x' : X') (b : ℕ) (Y : ℕ → E) :
    (t.reX π).val x' b Y = t.val (π x') b Y := rfl

theorem Poly0.reX_val (P : Poly0 X E) (x' : X') (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    (P.reX π).val Φ x' W A b = P.val Φ (π x') W A b := by
  show ((P.terms.map (Term.reX π)).map fun t =>
      t.val x' b fun j => (P.atom j).val Φ P.v W A b).sum = _
  rw [List.map_map]
  rfl

theorem Atom.reX_val (a : Atom X E) (v : ℕ) (x' : X') (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    (a.reX π).val Φ v x' W A b = a.val Φ v (π x') W A b := by
  cases a with
  | base a => rfl
  | sum w P => exact Finset.sum_congr rfl fun j _ => Poly0.reX_val π Φ P x' W A _

theorem Poly0.reX_wf {P : Poly0 X E} (h : P.WF Φ) : (P.reX π).WF Φ := by
  refine ⟨fun t ht j hj => ?_, h.2⟩
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact h.1 t' ht' j hj

theorem Atom.reX_wf {a : Atom X E} {v : ℕ} (h : a.WF Φ v) : (a.reX π).WF Φ v := by
  cases a with
  | base a => exact h
  | sum w P => exact ⟨h.1, Poly0.reX_wf π Φ h.2⟩

omit [Field E] in
theorem Atom.reX_places (a : Atom X E) (v : ℕ) : (a.reX π).places v = a.places v := by
  cases a <;> rfl

end

theorem reX_val : Spec.reX_val := by
  intro X X' F E _ _ _ π f Φ x' W A b
  show ((f.terms.map (Term.reX π)).map fun t =>
      t.val x' b fun j => ((f.atom j).reX π).val Φ f.v x' W A b).sum = _
  rw [List.map_map]
  unfold Fam.val
  refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
  show t.coef (π x') b * (t.atoms.map fun j => ((f.atom j).reX π).val Φ f.v x' W A b).prod = _
  simp only [Atom.reX_val]
  rfl

theorem reX_wf : Spec.reX_wf := by
  intro X X' F E _ _ _ π f Φ h
  refine ⟨fun t ht j hj => ?_, fun j hj => Atom.reX_wf π Φ (h.2 j hj)⟩
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact h.1 t' ht' j hj

theorem reX_places : Spec.reX_places := by
  intro X X' E π f
  ext p
  show (∃ j < f.na, p ∈ ((f.atom j).reX π).places f.v) ↔ ∃ j < f.na, p ∈ (f.atom j).places f.v
  simp only [Atom.reX_places]

theorem degLe_reX : Spec.degLe_reX := by
  intro X X' E π f d h
  refine ⟨(deg_le_iff X' E _ d).2 fun t ht => ?_, fun j w P hP => ?_⟩
  · obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact (deg_le_iff X E f d).1 h.1 t' ht'
  · have hP' : (f.atom j).reX π = .sum w P := hP
    cases ha : f.atom j with
    | base a => rw [ha] at hP'; cases hP'
    | sum w' P' =>
      rw [ha] at hP'
      obtain ⟨rfl, rfl⟩ : w' = w ∧ P'.reX π = P := by
        injection hP' with h1 h2
        exact ⟨h1, h2⟩
      refine (deg_le_iff X' E _ d).2 fun t ht => ?_
      obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
      exact (deg_le_iff X E _ d).1 (h.2 j w' P' ha) t' ht'

theorem tupFrom_v {X E : Type} [Zero E] [Mul E] (V t : ℕ) (L : List (Fam X E)) :
    (tupFrom V t L).v = V := by
  cases L <;> rfl

theorem famT_v : Spec.famT_v := fun _ _ _ _ _ => rfl

theorem fam_eta {X E : Type} (f : Fam X E) (V : ℕ) (h : f.v = V) :
    (⟨V, f.na, f.atom, f.terms⟩ : Fam X E) = f := by
  subst h
  rfl

theorem famT_eq {X E : Type} [Zero E] [Mul E] (L : List (Fam X E)) :
    famT L = tupFrom (maxV L) 0 L :=
  fam_eta _ _ (tupFrom_v _ 0 L)

section
variable {X F E : Type} [Field F] [Field E] [Algebra F E] (Φ : IdxFmt F)

theorem part_wf {V : ℕ} {f : Fam X E} (t : ℕ) (h : f.WF Φ) (hv : f.v ≤ V) :
    (Fam.mask (fun (x' : XZ X E) _ => x'.2 t) ((f.reX Prod.fst).to V)).WF Φ :=
  mask_wf Φ _ (to_wf (XZ X E) F E _ Φ V (reX_wf X (XZ X E) F E Prod.fst f Φ h) hv)

theorem tupFrom_wf {V : ℕ} :
    ∀ (L : List (Fam X E)) (t : ℕ), (∀ f ∈ L, f.WF Φ ∧ f.v ≤ V) → (tupFrom V t L).WF Φ
  | [], _, _ => pub_wf Φ V _
  | f :: L, t, h =>
    add_wf Φ (part_wf Φ t (h f List.mem_cons_self).1 (h f List.mem_cons_self).2)
      (tupFrom_wf L (t + 1) fun g hg => h g (List.mem_cons_of_mem f hg)) (tupFrom_v V (t + 1) L)

theorem tupFrom_val {V : ℕ} (x : X) (z : ℕ → E) (W : ℕ → ℕ → F) (A : ℕ → ℕ → ℕ → E) (b : ℕ) :
    ∀ (L : List (Fam X E)) (t : ℕ), (∀ f ∈ L, f.WF Φ ∧ f.v ≤ V) →
      (tupFrom V t L).val Φ (x, z) W A b = tupVal (fun f => f.val Φ x W A (b % 2 ^ f.v)) z t L
  | [], _, _ => pub_val Φ (x, z) W A V _ b
  | f :: L, t, h => by
      have hf := h f List.mem_cons_self
      show (Fam.add (Fam.mask (fun (x' : XZ X E) _ => x'.2 t) ((f.reX Prod.fst).to V))
            (tupFrom V (t + 1) L)).val
          Φ (x, z) W A b =
        z t * f.val Φ x W A (b % 2 ^ f.v) + tupVal _ z (t + 1) L
      rw [add_val Φ (x, z) W A (part_wf Φ t hf.1 hf.2).1 (tupFrom_v V (t + 1) L) b, mask_val,
        to_val (XZ X E) F E _ Φ V (x, z) W A (reX_wf X (XZ X E) F E Prod.fst f Φ hf.1) hf.2 b,
        reX_val X (XZ X E) F E Prod.fst f Φ (x, z) W A,
        tupFrom_val x z W A b L (t + 1) fun g hg => h g (List.mem_cons_of_mem f hg)]
      rfl

theorem tupFrom_places {V : ℕ} :
    ∀ (L : List (Fam X E)) (t : ℕ),
      (∀ f ∈ L, f.WF Φ ∧ f.v ≤ V) → ∀ p, p ∈ (tupFrom V t L).places ↔ ∃ f ∈ L, p ∈ f.places
  | [], _, _, p =>
    ⟨fun ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero j), fun ⟨_, hf, _⟩ => absurd hf List.not_mem_nil⟩
  | f :: L, t, h, p => by
      have hf := h f List.mem_cons_self
      show p ∈ (Fam.add (Fam.mask (fun (x' : XZ X E) _ => x'.2 t) ((f.reX Prod.fst).to V))
            (tupFrom V (t + 1) L)).places ↔
        _
      rw [add_places (tupFrom_v V (t + 1) L) p,
        tupFrom_places L (t + 1) (fun g hg => h g (List.mem_cons_of_mem f hg)) p]
      have e : (Fam.mask (fun (x' : XZ X E) _ => x'.2 t) ((f.reX Prod.fst).to V)).places =
          f.places :=
        (to_places (XZ X E) F E _ Φ V (reX_wf X (XZ X E) F E Prod.fst f Φ hf.1) hf.2).trans
          (reX_places X (XZ X E) E Prod.fst f)
      rw [e]
      simp only [List.mem_cons, exists_eq_or_imp]

end

/-- the sum from number t on, over the positions of the list -/
theorem tupVal_eq {X E : Type} [Field E] (val : Fam X E → E) (z : ℕ → E) :
    ∀ (L : List (Fam X E)) (t : ℕ),
      tupVal val z t L = ∑ i : Fin L.length, z (t + i.val) * val (L.get i)
  | [], _ => by simp [tupVal]
  | f :: L, t => by
      show z t * val f + tupVal val z (t + 1) L =
        ∑ i : Fin (L.length + 1), z (t + i.val) * val ((f :: L).get i)
      rw [Fin.sum_univ_succ, tupVal_eq val z L (t + 1)]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      show z (t + 1 + i.val) * _ = z (t + (i.val + 1)) * _
      rw [show t + 1 + i.val = t + (i.val + 1) by omega]
      rfl

theorem famT_val : Spec.famT_val := by
  intro X F E _ _ _ L Φ x z W A h b
  rw [famT_eq, tupFrom_val Φ x z W A b L 0 (glue_hyp h), tupVal_eq]
  simp only [Nat.zero_add]

theorem famT_valTo : Spec.famT_valTo := by
  intro X F E _ _ _ L Φ x z W A h b
  rw [famT_val X F E L Φ x z W A h b]
  exact Finset.sum_congr rfl fun t _ => by
    rw [to_val X F E (L.get t) Φ (maxV L) x W A (h _ (List.get_mem L t))
        (le_maxV (List.get_mem L t)) b]

theorem famT_wf : Spec.famT_wf := fun _ _ _ _ _ _ L Φ h => by
  rw [famT_eq]
  exact tupFrom_wf Φ L 0 (glue_hyp h)

theorem famT_places : Spec.famT_places := fun _ _ _ _ _ _ L Φ h => by
  rw [famT_eq]
  exact tupFrom_places Φ L 0 (glue_hyp h)

theorem degLe_tupFrom {X E : Type} [Zero E] [Mul E] (V d : ℕ) :
    ∀ (L : List (Fam X E)) (t : ℕ), (∀ f ∈ L, f.DegLe d) → (tupFrom V t L).DegLe d
  | [], _, _ => degLe_pub _ E V _ d
  | f :: L, t, h =>
    degLe_add _ E _ _ d
      (degLe_mask _ E _ _ d
        (degLe_to _ E _ V d (degLe_reX X (XZ X E) E Prod.fst f d (h f List.mem_cons_self))))
      (degLe_tupFrom V d L (t + 1) fun g hg => h g (List.mem_cons_of_mem f hg))

theorem degLe_famT : Spec.degLe_famT := fun _ _ _ _ L d h => by
  rw [famT_eq]
  exact degLe_tupFrom _ d L 0 h

theorem low_zero_iff : Spec.low_zero_iff := by
  intro E _ v V h hv
  refine ⟨fun h0 b _ => h0 _ (Nat.mod_lt _ (by positivity)), fun h0 b hb => ?_⟩
  have := h0 b (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by norm_num) hv))
  rwa [Nat.mod_eq_of_lt hb] at this

theorem to_zero_iff : Spec.to_zero_iff := by
  intro X F E _ _ _ f Φ V x W A hf hv
  simp only [to_val X F E f Φ V x W A hf hv]
  exact (low_zero_iff E f.v V (fun b => f.val Φ x W A b) hv).symm

theorem tuple_zero_iff : Spec.tuple_zero_iff := by
  intro X F E _ _ _ L Φ x W A
  constructor
  · intro h t
    exact (low_zero_iff E _ _ _ (le_maxV (List.get_mem L t))).1 (h _ (List.get_mem L t))
  · intro h f hf
    obtain ⟨t, rfl⟩ := List.get_of_mem hf
    exact (low_zero_iff E _ _ _ (le_maxV (List.get_mem L t))).2 (h t)

end Cb
