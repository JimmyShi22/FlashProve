-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpTreePProofs.lean: the proofs of the statements of Cb/Ld/LdLkpTreeP.lean (the product tree
built from the sumcheck of Cb/Ld/LdPsc.lean and the line step of Cb/Ld/LdLine.lean).

Beside the theorems `ldLkpP_*` there are helper lemmas, which no statement reads: two records of
relations with equal fields are equal; facts on a level that hold by cases (level 0, a later level);
the degrees and the sum of a product of two multilinear extensions.
-/
import Cb.Ld.LdLkpTreeP
import Cb.Ld.LdLineAt
import Cb.Ld.LdPscVarsProofs
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false

namespace Cb
open Iop IOR Hiop Prob Cb.LdLkp

theorem LdLkp.rels_ext {K X : Type} {Ex : ExtSpec} {W : Type} {A B : Rels K X Ex W}
    (h1 : A.rel = B.rel) (h2 : A.relR = B.relR) (h3 : A.on = B.on) (h4 : A.core = B.core) :
    A = B := by
  cases A
  cases B
  simp only at h1 h2 h3 h4
  subst h1 h2 h3 h4
  rfl

theorem ldLkpP_chain : Spec.ldLkpP_chain := by
  intro K M Ex Wp X b A n
  induction n with
  | zero => exact fun h => h 0 (Nat.le_refl 0)
  | succ n ih =>
    intro h
    exact goodAt_seq_ext K M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ (A 0) (A (n + 1))
      (A (n + 1 + 1)) (fun _ _ _ wp => wp) (fun _ _ _ wp => wp)
      (fun _ _ _ wp => wp) _ _ (ih fun l hl => h l (Nat.le_succ_of_le hl))
      (h (n + 1) (Nat.le_refl _)) fun _ _ _ _ _ _ _ => rfl

section
variable {E : Type} [Field E] [Fintype E]

namespace LdLkp

/-- The degrees of a product of two multilinear extensions, each moved by a constant. -/
theorem degX_aux (k : ℕ) (d : PDats (List.replicate k (pfCube E 2)))
    (t₀ t₁ : (Fin k → Bool) → E) (u₀ u₁ : E) :
    HDeg (pVars (List.replicate k (pfCube E 2)) d) fun X =>
      (Alg.mle t₀ (hFnOf (pfCube E 2) k d X) + u₀) * (Alg.mle t₁ (hFnOf (pfCube E 2) k d X) + u₁) +
          ∑ b : Empty, (b.elim : E) * (b.elim : E) := by
  refine hdeg_of_degLE (pfCube E 2) k d
    (fun x => (Alg.mle t₀ x + u₀) * (Alg.mle t₁ x + u₁) + ∑ b : Empty, (b.elim : E) * (b.elim : E))
    ?_
  have h := (((Alg.DegLE.mle t₀).add (Alg.DegLE.const _ u₀)).mul
      ((Alg.DegLE.mle t₁).add (Alg.DegLE.const _ u₁))).add
    (Alg.DegLE.const (fun _ : Fin k => 1 + 1) (∑ b : Empty, (b.elim : E) * (b.elim : E)))
  exact h

omit [Fintype E] in
theorem degY_aux (v u : Bool → E) (r : Empty → E) :
    ∃ c : Fin (2 + 1) → E, ∀ y : E, (v false + u false * y) * (v true + u true * y) +
        ∑ b : Empty, (b.elim : E) * r b = hev c y := by
  obtain ⟨c, hc⟩ := degY_prod 2 ![v false, v true] ![u false, u true]
  refine ⟨c, fun y => ?_⟩
  rw [← hc y, Fin.prod_univ_two, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  rfl

/-- The sum, under equality weights at z, of a product of two multilinear extensions. -/
theorem sum_aux (k : ℕ) (z : Fin k → E) (t₀ t₁ : (Fin k → Bool) → E) :
    hSumAll (pVars (List.replicate k (pfCube E 2)) (pdEqs E 2 k z)) (fun X =>
      Alg.mle t₀ (hFnOf (pfCube E 2) k (pdEqs E 2 k z) X) *
          Alg.mle t₁ (hFnOf (pfCube E 2) k (pdEqs E 2 k z) X) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E))
      = Alg.mle (fun x => t₀ x * t₁ x) z := by
  rw [psv_eqs_sum E 2 k z]
  unfold Alg.mle
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [psv_fn_pt E (pfCube E 2) k (pdEqs E 2 k z) (Alg.corner b)]
  have h0 := Alg.mle_corner t₀ b
  have h1 := Alg.mle_corner t₁ b
  unfold Alg.mle at h0 h1
  rw [h0, h1, Finset.univ_eq_empty, Finset.sum_empty, add_zero]

/-- As `degX_aux`, with the point read through σ⁻¹. -/
theorem degX_auxS (k : ℕ) (σ : Equiv.Perm (Fin k)) (d : PDats (List.replicate k (pfCube E 2)))
    (t₀ t₁ : (Fin k → Bool) → E) (u₀ u₁ : E) :
    HDeg (pVars (List.replicate k (pfCube E 2)) d) fun X =>
      (Alg.mle t₀ (fun i => hFnOf (pfCube E 2) k d X (σ.symm i)) + u₀) *
          (Alg.mle t₁ (fun i => hFnOf (pfCube E 2) k d X (σ.symm i)) + u₁) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E) := by
  have e : (fun X : HPt (pVars (List.replicate k (pfCube E 2)) d) =>
      (Alg.mle t₀ (fun i => hFnOf (pfCube E 2) k d X (σ.symm i)) + u₀) *
          (Alg.mle t₁ (fun i => hFnOf (pfCube E 2) k d X (σ.symm i)) + u₁) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E)) =
      fun X =>
      (Alg.mle (fun b : Fin k → Bool => t₀ fun v => b (σ.symm v)) (hFnOf (pfCube E 2) k d X) + u₀) *
          (Alg.mle (fun b : Fin k → Bool => t₁ fun v => b (σ.symm v)) (hFnOf (pfCube E 2) k d X) +
            u₁) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E) :=
    funext fun X => by
      rw [mle_perm σ t₀ (hFnOf (pfCube E 2) k d X), mle_perm σ t₁ (hFnOf (pfCube E 2) k d X)]
  rw [e]
  exact degX_aux k d _ _ u₀ u₁

/-- As `sum_aux`, with the weights at z ∘ σ and the point read through σ⁻¹: the sum is the same for
every σ. -/
theorem sum_auxS (k : ℕ) (σ : Equiv.Perm (Fin k)) (z : Fin k → E) (t₀ t₁ : (Fin k → Bool) → E) :
    hSumAll (pVars (List.replicate k (pfCube E 2)) (pdEqs E 2 k fun j => z (σ j))) (fun X =>
      Alg.mle t₀ (fun i => hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X (σ.symm i)) *
          Alg.mle t₁ (fun i => hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X (σ.symm i)) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E))
      = Alg.mle (fun x => t₀ x * t₁ x) z := by
  have e : (fun X : HPt (pVars (List.replicate k (pfCube E 2)) (pdEqs E 2 k fun j => z (σ j))) =>
      Alg.mle t₀ (fun i => hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X (σ.symm i)) *
          Alg.mle t₁ (fun i => hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X (σ.symm i)) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E)) =
      fun X =>
      Alg.mle (fun b : Fin k → Bool => t₀ fun v => b (σ.symm v))
            (hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X) *
          Alg.mle (fun b : Fin k → Bool => t₁ fun v => b (σ.symm v))
            (hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X) +
        ∑ b : Empty, (b.elim : E) * (b.elim : E) :=
    funext fun X => by
      rw [mle_perm σ t₀ (hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X),
        mle_perm σ t₁ (hFnOf (pfCube E 2) k (pdEqs E 2 k fun j => z (σ j)) X)]
  rw [e, sum_aux k (fun j => z (σ j))]
  exact Alg.mle_equiv σ (fun x => t₀ x * t₁ x) z

namespace TreeP
variable (D : TreeP E)

theorem two_surj (l : ℕ) (a : (D.lv l).T.A) : ∃ b, (D.lv l).two b = a := by
  cases l with
  | zero => exact ⟨a, rfl⟩
  | succ l => exact ⟨a, rfl⟩

theorem F_eq (l : ℕ) (o : (D.lv l).T.par.Out) (m : D.J → E) (b : Bool) :
    (D.lv l).T.F o.st (fun j => m ((D.lv l).toJ j)) ((D.lv l).two b)
        ((D.lv l).T.ini o.st ((D.lv l).T.par.hp o.st o.pt)) =
      D.half ((D.lv l).base o.st) m l b ((D.lv l).gam o) := by
  cases l <;> rfl

theorem fmt_len (l : ℕ) : (D.lv l).T.fmt.length = D.g + l := by
  cases l with
  | zero => exact List.length_replicate
  | succ l => exact List.length_replicate

theorem step_fun (hS : D.Step) (st : D.St0) (m : D.J → E) (l : ℕ) :
    (fun x : Fin (D.g + l) → Bool =>
        D.U st m (l + 1) (Fin.snoc x false : Fin (D.g + l + 1) → Bool) *
          D.U st m (l + 1) (Fin.snoc x true : Fin (D.g + l + 1) → Bool)) = D.U st m l :=
  funext fun x => (hS st m l x).symm

end TreeP
end LdLkp
end

section
variable (E : Type) [Field E] [Fintype E]

theorem ldLkpP_sum : Spec.ldLkpP_sum E := by
  intro D hS l x m
  have key : hSumAll ((D.lv l).T.vars x.2) ((D.lv l).T.sum x.2 fun j => m ((D.lv l).toJ j)) =
      Alg.mle (D.U ((D.lv l).base x.2) m l) ((D.lv l).pnt x.2) := by
    rw [← D.step_fun hS ((D.lv l).base x.2) m l]
    cases l with
    | zero => exact sum_auxS (D.g + 0) (D.sg 0) x.2.2 _ _
    | succ l => exact sum_auxS (D.g + l + 1) (D.sg (l + 1)) ((D.cube l).pt x.2) _ _
  unfold PscOur.SumHolds
  rw [key]

theorem ldLkpP_ok : Spec.ldLkpP_ok E := by
  intro D l
  cases l with
  | zero =>
    exact ⟨fun st => psv_eqs_ok E 2 (D.g + 0) (D.z0 st),
      fun f hf => by rw [List.eq_of_mem_replicate hf]; exact (psv_val E).1 2,
      fun st m u => degX_auxS (D.g + 0) (D.sg 0) _ _ _ (u false) (u true),
      fun _ _ v u r => degY_aux v u r⟩
  | succ l =>
    exact ⟨(ldLineC_vars E (D.cube l)).1,
      (ldLineC_vars E (D.cube l)).2,
      fun st m u => degX_auxS (D.g + l + 1) (D.sg (l + 1)) _ _ _ (u false) (u true),
      fun _ _ v u r => degY_aux v u r⟩

theorem ldLkpP_halves : Spec.ldLkpP_halves E := by
  intro D hS l o m b
  refine (D.F_eq l o m b).trans ?_
  refine congrArg (fun u => Alg.mle u ((D.lv l).gam o)) (funext fun x => ?_)
  show D.U ((D.lv l).base o.st) m (l + 1) (Fin.snoc x b : Fin (D.g + l + 1) → Bool) =
    D.half ((D.lv l).base o.st) m (l + 1) false
          (Alg.corner (Fin.snoc x b : Fin (D.g + l + 1) → Bool)) *
        D.half ((D.lv l).base o.st) m (l + 1) true
          (Alg.corner (Fin.snoc x b : Fin (D.g + l + 1) → Bool)) +
      ∑ e : Empty, (e.elim : E) * (e.elim : E)
  unfold TreeP.half
  rw [Alg.mle_corner, Alg.mle_corner, Finset.univ_eq_empty, Finset.sum_empty, add_zero]
  exact hS _ m (l + 1) _

theorem ldLkpP_level : Spec.ldLkpP_level E := by
  intro D Ex M Wp Kc msg A0 l hS
  have ok := ldLkpP_ok E D l
  have g1 := psc_our_goodAt E (D.lv l).T Ex M Wp Kc (D.ride msg A0 l) (D.msgAt M msg l)
    ok.1 ok.2.2.1 ok.2.2.2 ok.2.1
  have g2 := ldLineC_goodAt E (D.cube l) Ex M Wp Kc (D.afterU msg l (D.ride msg A0 l))
    msg (ldLkpP_halves E D hS l)
  have hiff : ∀ (o : (D.lv l).T.par.Out) (mm : (D.lv l).T.J → E) (P : Prop),
      (P ∧ (D.lv l).T.par.OutHolds o mm) ↔
      ((P ∧ (D.lv l).T.par.UHolds o mm) ∧
        ∀ b, (D.lv l).T.par.EHolds o mm ((D.lv l).two b)) := fun o mm P =>
    ⟨fun h => ⟨⟨h.1, h.2.1⟩, fun b => h.2.2 _⟩, fun h => ⟨h.1.1, h.1.2, fun a => by
      obtain ⟨b, rfl⟩ := D.two_surj l a
      exact h.2 b⟩⟩
  refine goodAt_seq_ext Kc M _ _ _ Ex Ex Ex Wp Wp Wp _ _ _ _ _ _ _ (fun _ _ _ wp => wp)
    (fun _ _ _ wp => wp) (fun _ _ _ wp => wp) _ _ ?_ g2 fun _ _ _ _ _ _ _ => rfl
  have e : (D.lv l).T.par.baseOut (D.ride msg A0 l) (fun w : M × Wp => D.msgAt M msg l w.1) =
      ⟨fun o y w =>
          (D.afterU msg l (D.ride msg A0 l)).rel o y w ∧
          ∀ b, (D.cube l).P.par.EHolds o ((D.cube l).toLine.em (msg w.1)) ((D.cube l).a b),
        fun a w =>
          (D.afterU msg l (D.ride msg A0 l)).relR a w ∧
          ∀ b, (D.cube l).P.par.EHolds a.1 ((D.cube l).toLine.em (msg w.1)) ((D.cube l).a b),
        (D.afterU msg l (D.ride msg A0 l)).on,
        (D.afterU msg l (D.ride msg A0 l)).core⟩ :=
    rels_ext (funext fun o => funext fun y => funext fun w => propext (hiff o _ _))
      (funext fun a => funext fun w => propext (hiff a.1 _ _)) rfl rfl
  rw [e] at g1
  exact g1

theorem ldLkpP_tree : Spec.ldLkpP_tree E := by
  intro D Ex M Wp Kc msg A0 n hS
  exact ldLkpP_chain Kc M Ex Wp (fun l => E × (D.lv l).T.St) (D.levA Ex Wp Kc msg) (D.jtAt msg A0) n
    fun l _ => ldLkpP_level E D Ex M Wp Kc msg A0 l hS

theorem ldLkpP_tree_sig : Spec.ldLkpP_tree_sig E := by
  intro D S E₀ Wp Kc msg A0 n hS
  exact sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _
    (ldLkpP_tree E D E₀ S.Msg Wp Kc msg A0 n hS)

theorem ldLkpP_rounds : Spec.ldLkpP_rounds E := by
  intro D Ex M Wp Kc msg n
  have hl : ∀ l, (D.levA Ex Wp Kc msg l).R.shape.length = D.g + l + 3 + 1 := fun l => by
    have e : (D.levA Ex Wp Kc msg l).R.shape =
        ((D.lv l).T.par.psc Ex).shape ++ (D.lineA Ex M Wp Kc l).R.shape := rfl
    rw [e, List.length_append, psc_our_len E (D.lv l).T Ex, D.fmt_len l]
    rfl
  unfold TreeP.treeA
  induction n with
  | zero => simpa [BkA.chain] using hl 0
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih, ← hl (n + 1)]
    exact List.length_append

end
end Cb
