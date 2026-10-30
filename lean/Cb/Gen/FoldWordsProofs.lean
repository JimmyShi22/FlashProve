-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/FoldWordsProofs.lean: proofs of the statements of Cb/Gen/FoldWords.lean. Every "Spec.name"
there is "theorem name" here. Nothing is assumed beyond the hypotheses of the statements; the counts
come from Blocks/Decode.lean and Code/Derived.lean.
-/
import Cb.Gen.FoldWords
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Fintype
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace Cb
open Prob Blocks Finset

section Basic
variable {E : Type} [Field E]

theorem foldAll_cons : Spec.foldAll_cons := by
  intro E _ V _ _ k x γ f
  unfold foldAll fold1
  rw [Alg.sum_cube_succ]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Alg.eqk_cons, Alg.eqk_cons]
  simp only [if_true, Bool.false_eq_true, if_false]
  rw [smul_add, smul_smul, smul_smul, mul_comm (Alg.eqk γ v), mul_comm (Alg.eqk γ v)]

theorem foldAll_zero : Spec.foldAll_zero := by
  intro E _ V _ _ γ f b
  unfold foldAll
  rw [Fintype.sum_subsingleton _ b]
  simp [Alg.eqk]

theorem decodesTo_fold1 : Spec.decodesTo_fold1 := by
  intro E ι κ _ _ _ G e k x f M h
  refine h.of_imp fun j hj v => ?_
  simp only [fold1, Pi.add_apply, Pi.smul_apply, Matrix.mulVec_add, Matrix.mulVec_smul, hj]

theorem dec_fold1 : Spec.dec_fold1 := by
  intro E ι κ _ _ _ G d e k x f hd h2 h
  have h1 := decodesTo_fold1 E ι κ G e k x f _ h.decodesTo_dec
  exact ⟨⟨_, h1⟩, h1.dec_eq hd h2⟩

/-- The two halves of a table, as a line. -/
theorem fold1_eq_line {V : Type} [AddCommGroup V] [Module E V] {k : ℕ} (x : E)
    (f : (Fin (k + 1) → Bool) → V) (v : Fin k → Bool) :
    fold1 x f v = f (Fin.cons false v) + x • (f (Fin.cons true v) - f (Fin.cons false v)) := by
  unfold fold1
  rw [sub_smul, one_smul, smul_sub]
  abel

theorem cnt_fold1 : Spec.cnt_fold1 := by
  intro E ι κ _ _ _ _ G e bad k f hm hf
  have hf' : ¬ Decodes G e
      (Sum.elim (fun v : Fin k → Bool => f (Fin.cons false v))
        (fun v => f (Fin.cons true v) - f (Fin.cons false v))) := by
    rintro ⟨M, hM⟩
    apply hf
    refine ⟨fun b =>
        if b 0 then M (Sum.inl (Fin.tail b)) + M (Sum.inr (Fin.tail b))
        else M (Sum.inl (Fin.tail b)),
      hM.of_imp fun j hj b => ?_⟩
    have h0 := hj (Sum.inl (Fin.tail b))
    have h1 := hj (Sum.inr (Fin.tail b))
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.sub_apply] at h0 h1
    have hb : b = Fin.cons (b 0) (Fin.tail b) := (Fin.cons_self_tail b).symm
    cases hb0 : b 0 with
    | false =>
        rw [hb0] at hb
        simp only [Bool.false_eq_true, if_false]
        rw [← h0, ← hb]
    | true =>
        rw [hb0] at hb
        simp only [if_true]
        rw [Matrix.mulVec_add, Pi.add_apply, ← h0, ← h1, ← hb]
        ring
  refine le_trans (le_of_eq (cnt_congr fun x => ?_)) (cnt_decodes_line hm hf')
  have : fold1 x f =
      fun v => f (Fin.cons false v) + x • (f (Fin.cons true v) - f (Fin.cons false v)) :=
    funext fun v => fold1_eq_line x f v
  rw [this]

theorem decodesTo_foldAll : Spec.decodesTo_foldAll := by
  intro E ι κ N _ _ _ _ _ G e γ f M h
  exact h.comb (Alg.eqk γ)

theorem dec_foldAll : Spec.dec_foldAll := by
  intro E ι κ N _ _ _ _ _ G d e γ f hd h2 h
  have h1 := decodesTo_foldAll E ι κ N G e γ f _ h.decodesTo_dec
  exact ⟨⟨_, h1⟩, congrFun (h1.dec_eq hd h2) ()⟩

theorem cnt_foldAll : Spec.cnt_foldAll := by
  intro E ι κ _ _ _ _ G e bad k f hm hf
  have hf' : ¬ Code.Close (LinearMap.range G.mulVecLin) e
      (fun p : (Fin k → Bool) × Unit => (fun v (_ : Unit) => f v) p.1 p.2) := by
    intro hc
    exact hf ((decodes_iff_close.mpr hc).comp fun v => (v, ()))
  refine le_trans (le_of_eq (cnt_congr fun γ => ?_))
    (hm.cnt_close_eqk_le (R := Unit) k (f := fun v (_ : Unit) => f v) hf')
  exact decodes_iff_close

theorem decodes_of_clean : Spec.decodes_of_clean := by
  intro E ι κ _ _ _ G e k
  induction k with
  | zero =>
      intro γ f _ h
      have hf : f = fun _ => foldAll γ f := funext fun b => (foldAll_zero E _ γ f b).symm
      rw [hf]
      exact h.comp fun _ => ()
  | succ k ih =>
      intro γ f hc h
      refine hc.1 (ih (Fin.tail γ) (fold1 (γ 0) f) hc.2 ?_)
      rw [← foldAll_cons, Fin.cons_self_tail]
      exact h

end Basic

section Summand
variable {E : Type} [Field E]

theorem foldAll_apply {N κ : Type} [Fintype N] [DecidableEq N] (z : N → E)
    (L : (N → Bool) → κ → E) (c : κ) :
    foldAll z L c = Alg.mle (fun v => L v c) z := by
  simp [foldAll, Alg.mle, Finset.sum_apply]

theorem foldAll_corner {V N : Type} [AddCommGroup V] [Module E V] [Fintype N] [DecidableEq N]
    (b : N → Bool) (f : (N → Bool) → V) :
    foldAll (Alg.corner b : N → E) f = f b := by
  unfold foldAll
  simp_rw [Alg.eqk_corner]
  simp

theorem degLE_summand : Spec.degLE_summand := by
  intro E N κ _ _ _ _ L m
  have h : summand L m =
      fun z =>
        ∑ c ∈ (Finset.univ : Finset κ),
            Alg.mle (fun v => L v c) z * Alg.mle (fun v => m v c) z := by
    funext z
    simp only [summand, dot, foldAll_apply]
  rw [h]
  exact Alg.DegLE.sum _ fun c _ => (Alg.DegLE.mul (Alg.DegLE.mle _) (Alg.DegLE.mle _))

theorem sum_summand : Spec.sum_summand := by
  intro E N κ _ _ _ _ L m
  simp only [summand, foldAll_corner, pair]

end Summand

section Rep
variable {E : Type} [Field E]

open Classical in
/-- The variables of the larger cube: those in the range of the injection, and the others. -/
def splitEquiv {N N' : Type} (em : N → N') (h : Function.Injective em) :
    N ⊕ ↥(Set.range em)ᶜ ≃ N' :=
  ((Equiv.ofInjective em h).sumCongr (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range em))

theorem splitEquiv_inl {N N' : Type} (em : N → N') (h : Function.Injective em) (v : N) :
    splitEquiv em h (Sum.inl v) = em v := by
  simp [splitEquiv]

theorem splitEquiv_symm {N N' : Type} (em : N → N') (h : Function.Injective em) (v : N) :
    (splitEquiv em h).symm (em v) = Sum.inl v := by
  rw [← splitEquiv_inl em h v, Equiv.symm_apply_apply]

/-- A sum over the larger cube, by the values at the range of the injection and the others. -/
theorem sum_split {N N' M : Type} [Fintype N] [DecidableEq N] [Fintype N'] [DecidableEq N']
    [AddCommMonoid M] (em : N → N') (h : Function.Injective em) [Fintype ↥(Set.range em)ᶜ]
    [DecidableEq ↥(Set.range em)ᶜ] (F : (N' → Bool) → M) :
    ∑ b, F b =
      ∑ c : N → Bool,
        ∑ c' : ↥(Set.range em)ᶜ → Bool, F (fun v => Sum.elim c c' ((splitEquiv em h).symm v)) := by
  rw [← Fintype.sum_prod_type']
  let Φ : (N → Bool) × (↥(Set.range em)ᶜ → Bool) ≃ (N' → Bool) :=
    (Equiv.sumArrowEquivProdArrow N _ Bool).symm.trans
      (Equiv.arrowCongr (splitEquiv em h) (Equiv.refl Bool))
  exact (Φ.sum_comp F).symm.trans (Finset.sum_congr rfl fun p _ => rfl)

theorem rep_split {V N N' : Type} (em : N → N') (h : Function.Injective em) (f : (N → Bool) → V)
    (c : N → Bool) (c' : ↥(Set.range em)ᶜ → Bool) :
    rep em f (fun v => Sum.elim c c' ((splitEquiv em h).symm v)) = f c := by
  unfold rep
  congr 1
  funext v
  show Sum.elim c c' ((splitEquiv em h).symm (em v)) = c v
  rw [splitEquiv_symm]
  rfl

theorem decodes_rep_iff : Spec.decodes_rep_iff := by
  intro E ι κ N N' _ _ _ G e em f h
  constructor
  · intro hd
    have h1 := hd.comp fun (c : N → Bool) => Function.extend em c fun _ => false
    have h2 : (fun c : N → Bool => rep em f (Function.extend em c fun _ => false)) = f := by
      funext c
      unfold rep
      congr 1
      funext v
      exact h.extend_apply c _ v
    rwa [h2] at h1
  · intro hd
    exact hd.comp fun (b : N' → Bool) v => b (em v)

theorem dec_rep : Spec.dec_rep := by
  intro E ι κ N N' _ _ _ G d e em f hd h2 h
  exact dec_comp hd h2 h fun (b : N' → Bool) v => b (em v)

theorem foldAll_rep : Spec.foldAll_rep := by
  intro E V N N' _ _ _ _ _ _ _ em γ f h
  classical
  haveI : Fintype ↥(Set.range em)ᶜ := Fintype.ofFinite _
  unfold foldAll
  rw [sum_split em h]
  refine Finset.sum_congr rfl fun c _ => ?_
  have key : ∀ c' : ↥(Set.range em)ᶜ → Bool,
      Alg.eqk γ (fun v => Sum.elim c c' ((splitEquiv em h).symm v)) •
          rep em f (fun v => Sum.elim c c' ((splitEquiv em h).symm v)) =
        (Alg.eqk (fun v => γ (splitEquiv em h (Sum.inr v))) c') •
          (Alg.eqk (fun v => γ (em v)) c • f c) := by
    intro c'
    have h2 : Alg.eqk γ (fun v => Sum.elim c c' ((splitEquiv em h).symm v)) =
        Alg.eqk (fun v => γ (em v)) c * Alg.eqk (fun v => γ (splitEquiv em h (Sum.inr v))) c' := by
      rw [← Alg.eqk_equiv (splitEquiv em h) γ]
      have h3 : (fun v => γ (splitEquiv em h v)) =
          Sum.elim (fun v => γ (em v)) (fun v => γ (splitEquiv em h (Sum.inr v))) := by
        funext v
        cases v with
        | inl v => simp [splitEquiv_inl]
        | inr v => rfl
      rw [h3, Alg.eqk_sumElim]
      simp
    rw [rep_split, h2, mul_comm, mul_smul]
  rw [Finset.sum_congr rfl fun c' _ => key c', ← Finset.sum_smul, Alg.sum_eqk, one_smul]

theorem pair_rep : Spec.pair_rep := by
  intro E κ N N' _ _ _ _ _ _ em L m h
  classical
  haveI : Fintype ↥(Set.range em)ᶜ := Fintype.ofFinite _
  unfold pair
  rw [sum_split em h]
  simp only [rep_split, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  congr 1
  have hc : Fintype.card N + Fintype.card ↥(Set.range em)ᶜ = Fintype.card N' := by
    rw [← Fintype.card_sum]
    exact Fintype.card_congr (splitEquiv em h)
  have hc' : Fintype.card ↥(Set.range em)ᶜ = Fintype.card N' - Fintype.card N := by omega
  rw [Fintype.card_fun, Fintype.card_bool, hc']
  push_cast
  rfl

end Rep
end Cb
