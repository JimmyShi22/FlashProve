-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumClaim.lean: algebra for the soundness analysis of the zero-knowledge sumcheck: the
quantity that is claimed after each round, for arbitrary tables of messages.

Algebra only: no code, no protocol. Definitions, statements and proofs.

Why: round-by-round knowledge soundness follows a claim from round to round. After some rounds, k
variables are left, the main table has rows on their cube, the two mask tables have rows on the cube
of the first h of them. The claim is about any three tables of messages of that format.

Main names:
  `SStg k`: the public side of a claim: three families of weights, each a function of a point in the
    k variables that are left (earlier variables are already at their challenges).
  `S.sm h m z`: the summand at the point z: <weights at z, tables folded at z> (the masks folded at
    the first h coordinates of z).
  `S.next γ`, `foldM k h γ m`: one round: the first variable is set to γ; the tables are folded in
    it (the masks only if h > 0).
  `preP k h z`: the first h coordinates of z, written without a proof of h ≤ k (0 where there is no
    coordinate).
  `sm_next`: the summand after a round is the summand before it with the first variable at γ.
  `SStg.poly`: if the summand has degree at most N in each variable (`S.Deg N h`), then for every m
    there is a polynomial p of degree at most N with p(0) + p(1) = the quantity (`S.val`) before the
    round and p(γ) = the quantity after the round at the folded tables.
  `SStg.Deg.next`: the degree bound passes to the next stage.

Notation: `n`: in `S.val n`, `sVars E n k` (Cb/Ld/LdSum.lean): the largest degree of a round
polynomial; `Jc`, `Jz`: the types that index a row's entries, in the main table and in the two mask
tables (`SMsg`).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumHon
import Alg.Poly

set_option autoImplicit false

namespace Cb
open Polynomial

section
variable {E : Type} [Field E] {Jc Jz : Type}

/-- the first h coordinates -/
def preP (k h : ℕ) (z : Fin k → E) : Fin h → E := fun i =>
  if hi : i.val < k then z ⟨i.val, hi⟩ else 0

theorem preP_succ (k h : ℕ) (γ : E) (z : Fin k → E) :
    preP (k + 1) (h + 1) (Fin.cons γ z : Fin (k + 1) → E) = Fin.cons γ (preP k h z) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [preP]
  · by_cases hi : i.val < k
    · have h1 : (i.succ : Fin (h + 1)).val < k + 1 := by simp; omega
      simp only [preP, Fin.cons_succ, dif_pos hi, dif_pos h1]
      exact Fin.cons_succ (α := fun _ => E) γ z ⟨i.val, hi⟩
    · have h1 : ¬ (i.succ : Fin (h + 1)).val < k + 1 := by simp; omega
      simp only [preP, Fin.cons_succ, dif_neg hi, dif_neg h1]

/-- three tables of messages: main, carried mask, fresh mask -/
abbrev SMsg (E Jc Jz : Type) (k h : ℕ) : Type :=
  ((Fin k → Bool) × Jc) ⊕ (((Fin h → Bool) × Jz) ⊕ ((Fin h → Bool) × Jz)) → E

/-- The public side of a claim with k variables left. -/
structure SStg (E Jc Jz : Type) (k : ℕ) where
  Af : (Fin k → E) → Jc → E
  As : (Fin k → E) → Jz → E
  Aw : (Fin k → E) → Jz → E

/-- one round: the first variable is set -/
def SStg.next {k : ℕ} (γ : E) (S : SStg E Jc Jz (k + 1)) : SStg E Jc Jz k :=
  ⟨fun z => S.Af (Fin.cons γ z), fun z => S.As (Fin.cons γ z), fun z => S.Aw (Fin.cons γ z)⟩

/-- one round: the tables are folded in their first variable; masks without rows to fold stay -/
def foldM (k : ℕ) : (h : ℕ) → E → SMsg E Jc Jz (k + 1) h → SMsg E Jc Jz k (h - 1)
  | 0, γ, m =>
    Sum.elim (fun a =>
        (1 - γ) * m (.inl (Fin.cons false a.1, a.2)) + γ * m (.inl (Fin.cons true a.1, a.2)))
      fun a => (1 - γ) * m (.inr a) + γ * m (.inr a)
  | _ + 1, γ, m =>
    Sum.elim (fun a =>
        (1 - γ) * m (.inl (Fin.cons false a.1, a.2)) + γ * m (.inl (Fin.cons true a.1, a.2)))
      (Sum.elim (fun a =>
          (1 - γ) * m (.inr (.inl (Fin.cons false a.1, a.2))) +
            γ * m (.inr (.inl (Fin.cons true a.1, a.2)))) fun a =>
              (1 - γ) * m (.inr (.inr (Fin.cons false a.1, a.2))) +
                γ * m (.inr (.inr (Fin.cons true a.1, a.2))))

/-- tables whose two halves are given tables -/
def dupM (k : ℕ) : (h : ℕ) → SMsg E Jc Jz k (h - 1) → SMsg E Jc Jz (k + 1) h
  | 0, m => Sum.elim (fun a => m (.inl (fun i => a.1 i.succ, a.2))) fun a => m (.inr a)
  | _ + 1, m =>
    Sum.elim (fun a => m (.inl (fun i => a.1 i.succ, a.2)))
      (Sum.elim (fun a => m (.inr (.inl (fun i => a.1 i.succ, a.2)))) fun a =>
        m (.inr (.inr (fun i => a.1 i.succ, a.2))))

theorem foldM_dup (k : ℕ) :
    ∀ (h : ℕ) (γ : E) (m : SMsg E Jc Jz k (h - 1)), foldM k h γ (dupM k h m) = m
  | 0, γ, m => by
      funext j
      rcases j with a | a
      · show (1 - γ) * m (.inl a) + γ * m (.inl a) = _
        ring
      · show (1 - γ) * m (.inr a) + γ * m (.inr a) = _
        ring
  | h + 1, γ, m => by
      funext j
      rcases j with a | a | a
      · show (1 - γ) * m (.inl a) + γ * m (.inl a) = _
        ring
      · show (1 - γ) * m (.inr (.inl a)) + γ * m (.inr (.inl a)) = _
        ring
      · show (1 - γ) * m (.inr (.inr a)) + γ * m (.inr (.inr a)) = _
        ring

theorem foldV_cons' {J : Type} {k : ℕ} (γ : E) (z : Fin k → E)
    (v : (Fin (k + 1) → Bool) × J → E) (c : J) :
    foldV (Fin.cons γ z : Fin (k + 1) → E) v c =
      foldV z (fun a => (1 - γ) * v (Fin.cons false a.1, a.2) + γ * v (Fin.cons true a.1, a.2))
        c := by
  unfold foldV
  rw [Alg.sum_cube_succ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Alg.eqk_cons, Alg.eqk_cons]
  simp only [if_true, Bool.false_eq_true, if_false]
  ring

theorem foldV_zero' {J : Type} {h : ℕ} (v : (Fin h → Bool) × J → E) (c : J) :
    foldV (fun _ => (0 : E)) v c = v (fun _ => false, c) := by
  have e : (fun _ : Fin h => (0 : E)) = Alg.corner fun _ => false := by funext i; simp [Alg.corner]
  unfold foldV
  rw [e]
  simp only [Alg.eqk_corner]
  simp

variable [Fintype Jc] [Fintype Jz]

/-- The summand at a point. -/
def SStg.sm {k : ℕ} (S : SStg E Jc Jz k) (h : ℕ) (m : SMsg E Jc Jz k h) (z : Fin k → E) : E :=
  ∑ c, S.Af z c * foldV z (fun a => m (.inl a)) c +
    (∑ c, S.As z c * foldV (preP k h z) (fun a => m (.inr (.inl a))) c +
      ∑ c, S.Aw z c * foldV (preP k h z) (fun a => m (.inr (.inr a))) c)

/-- The claimed quantity: the sum of the summand over the cube. -/
def SStg.val (n : ℕ) {k : ℕ} (S : SStg E Jc Jz k) (h : ℕ) (m : SMsg E Jc Jz k h) : E :=
  hSumAll (sVars E n k) fun γ => S.sm h m (sPt n k γ)

/-- the summand has degree at most N in each variable, whatever the tables -/
def SStg.Deg {k : ℕ} (S : SStg E Jc Jz k) (N h : ℕ) : Prop :=
  ∀ m : SMsg E Jc Jz k h, Alg.DegLE (fun _ => N) (S.sm h m)

theorem sm_next {k : ℕ} (S : SStg E Jc Jz (k + 1)) :
    ∀ (h : ℕ) (γ : E) (m : SMsg E Jc Jz (k + 1) h) (z : Fin k → E),
      (S.next γ).sm (h - 1) (foldM k h γ m) z = S.sm h m (Fin.cons γ z)
  | 0, γ, m, z => by
      unfold SStg.sm
      have e0 : preP (k + 1) 0 (Fin.cons γ z : Fin (k + 1) → E) = preP k (0 - 1) z :=
        funext fun i => i.elim0
      have e1 : ∀ a : ((Fin 0 → Bool) × Jz) ⊕ ((Fin 0 → Bool) × Jz),
          foldM k 0 γ m (.inr a) = m (.inr a) := fun a => by
        show (1 - γ) * m (.inr a) + γ * m (.inr a) = _
        ring
      rw [e0]
      simp only [foldV_cons']
      refine congrArg₂ (· + ·) rfl (congrArg₂ (· + ·) ?_ ?_)
      · exact Finset.sum_congr rfl fun c _ =>
          congrArg _ (congrFun (congrArg _ (funext fun a => e1 (.inl a))) c)
      · exact Finset.sum_congr rfl fun c _ =>
          congrArg _ (congrFun (congrArg _ (funext fun a => e1 (.inr a))) c)
  | h + 1, γ, m, z => by
      unfold SStg.sm
      rw [preP_succ]
      simp only [foldV_cons']
      rfl

theorem degLE_cons {k : ℕ} {d : Fin (k + 1) → ℕ} {g : (Fin (k + 1) → E) → E}
    (hg : Alg.DegLE d g) (γ : E) :
    Alg.DegLE (fun i : Fin k => d i.succ) fun z => g (Fin.cons γ z) := by
  intro z i
  obtain ⟨q, hq, he⟩ := hg (Fin.cons γ z) i.succ
  refine ⟨q, hq, fun t => ?_⟩
  show g (Fin.cons γ (Function.update z i t)) = _
  rw [← he, Fin.cons_update]

theorem SStg.Deg.next {k : ℕ} {S : SStg E Jc Jz (k + 1)} {N h : ℕ} (hS : S.Deg N h) (γ : E) :
    (S.next γ).Deg N (h - 1) := by
  intro m
  have h1 := degLE_cons (hS (dupM k h m)) γ
  have e : (fun z => S.sm h (dupM k h m) (Fin.cons γ z)) = (S.next γ).sm (h - 1) m := by
    funext z
    rw [← sm_next, foldM_dup]
  rwa [e] at h1

theorem sSumAll_poly (n N : ℕ) :
    ∀ (k : ℕ) (F : E → HPt (sVars E n k) → E),
      (∀ xs, ∃ p : E[X], p.natDegree ≤ N ∧ ∀ x, F x xs = p.eval x) →
      ∃ p : E[X], p.natDegree ≤ N ∧ ∀ x, hSumAll (sVars E n k) (F x) = p.eval x := by
  intro k
  induction k with
  | zero => intro F hF; exact hF ()
  | succ k ih =>
      intro F hF
      obtain ⟨p0, d0, e0⟩ := ih (fun x xs => F x (0, xs)) fun xs => hF (0, xs)
      obtain ⟨p1, d1, e1⟩ := ih (fun x xs => F x (1, xs)) fun xs => hF (1, xs)
      refine ⟨p0 + p1, (natDegree_add_le _ _).trans (max_le d0 d1), fun x => ?_⟩
      show (HVar.plain E n).sum (fun a => hSumAll (sVars E n k) fun xs => F x (a, xs)) = _
      rw [plain_sum, eval_add, ← e0, ← e1]

/-- The round polynomial of any three tables. -/
theorem SStg.poly (n : ℕ) {k : ℕ} (S : SStg E Jc Jz (k + 1)) {N h : ℕ}
    (hS : S.Deg N h) (m : SMsg E Jc Jz (k + 1) h) :
    ∃ p : E[X],
      p.natDegree ≤ N ∧
      p.eval 0 + p.eval 1 = S.val n h m ∧
      ∀ γ, p.eval γ = (S.next γ).val n (h - 1) (foldM k h γ m) := by
  obtain ⟨p, dp, ep⟩ := sSumAll_poly n N k (fun x xs => S.sm h m (Fin.cons x (sPt n k xs))) fun xs => by
    obtain ⟨q, hq, he⟩ := hS m (Fin.cons 0 (sPt n k xs)) 0
    exact ⟨q, hq, fun x => by rw [← he, Fin.update_cons_zero]⟩
  refine ⟨p, dp, ?_, fun γ => ?_⟩
  · rw [← ep, ← ep]
    exact (plain_sum (E := E) n fun x =>
      hSumAll (sVars E n k) fun xs => S.sm h m (Fin.cons x (sPt n k xs))).symm
  · rw [← ep]
    exact congrArg _ (funext fun xs => (sm_next S h γ m _).symm)

/-- with no variable left -/
theorem SStg.val_zero (n : ℕ) (S : SStg E Jc Jz 0) (h : ℕ) (m : SMsg E Jc Jz 0 h) (z : Fin 0 → E) :
    S.val n h m =
      ∑ c, S.Af z c * m (.inl (fun _ => false, c)) +
        (∑ c, S.As z c * m (.inr (.inl (fun _ => false, c))) +
          ∑ c, S.Aw z c * m (.inr (.inr (fun _ => false, c)))) := by
  have ez : sPt n 0 () = z := Subsingleton.elim _ _
  have e1 : z = fun _ => (0 : E) := Subsingleton.elim _ _
  have e2 : preP 0 h z = fun _ => (0 : E) := funext fun i => by simp [preP]
  show S.sm h m (sPt n 0 ()) = _
  rw [ez]
  unfold SStg.sm
  rw [e2]
  simp only [foldV_zero']
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun c _ => ?_) rfl
  conv_lhs => rw [e1]
  rw [foldV_zero', ← e1]

omit [Fintype Jc] [Fintype Jz] in
/-- a vector of coefficients as a polynomial -/
theorem hev_poly {n : ℕ} (c : Fin (n + 1) → E) :
    ∃ p : E[X], p.natDegree ≤ n ∧ ∀ x, hev c x = p.eval x := by
  refine ⟨∑ t : Fin (n + 1), C (c t) * X ^ (t : ℕ), ?_, fun x => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun t _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  · simp only [hev, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _

end
end Cb
