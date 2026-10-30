-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumStepClosed.lean: folding the rows of a table one variable at a time, through all its
variables, gives the same as one sum over the cube's corners with the eq kernel at the whole point.

Statements and proofs.

The chain `stgChain C Z Zw k h` of Cb/Ld/LdSumStepChain.lean folds the first variable, then the
second, and so on; the masks take part in the first h rounds (in all, if h > k). A protocol states
its new oracles and its new witness at once, by the kernel of the cube (`foldV` of Cb/Ld/LdRel.lean:
the sum over the corners b of eq(γ, b) times the row b). For h ≤ k the two are the same:
  `Spec.ldx_fold_closed`: the word after all k rounds, its one-row tables read as words
    (`Rename.last`, at a proof `h0` of `endH k h = 0`, which h ≤ k gives (`Spec.ldh_endH`,
    Cb/Ld/LdSumStepChain.lean)), is the triple: main table folded at γ, the two mask tables folded
    at the first h coordinates of γ;
  `Spec.ldx_foldW_closed`: the same for (message, randomness).

Limits: this file says nothing for h > k. The masks then still have rows at the end.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSumStepChainProofs

set_option autoImplicit false

namespace Cb
open Prob LdCode

section Kernel
variable {E J : Type} [Field E]

theorem foldV_zero (γ : Fin 0 → E) (v : (Fin 0 → Bool) × J → E) (r : Fin 0 → Bool) (c : J) :
    foldV γ v c = v (r, c) := by
  unfold foldV
  rw [Fintype.sum_subsingleton _ r]
  simp [Alg.eqk]

theorem foldV_cons {k : ℕ} (t : E) (z : Fin k → E) (v : (Fin (k + 1) → Bool) × J → E) (c : J) :
    foldV (Fin.cons t z : Fin (k + 1) → E) v c =
      foldV z (fun n => (1 - t) * v (Fin.cons false n.1, n.2) + t * v (Fin.cons true n.1, n.2))
        c := by
  have h := Alg.mle_cons (fun b => v (b, c)) t z
  show Alg.mle (fun b => v (b, c)) (Fin.cons t z : Fin (k + 1) → E)
    = Alg.mle (fun b => (1 - t) * v (Fin.cons false b, c) + t * v (Fin.cons true b, c)) z
  rw [h]
  unfold Alg.mle
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem foldV_succ {k : ℕ} (γ : Fin (k + 1) → E) (v : (Fin (k + 1) → Bool) × J → E) (c : J) :
    foldV γ v c =
      foldV (Fin.tail γ)
        (fun n => (1 - γ 0) * v (Fin.cons false n.1, n.2) + γ 0 * v (Fin.cons true n.1, n.2))
        c := by
  have h := foldV_cons (γ 0) (Fin.tail γ) v c
  rwa [Fin.cons_self_tail] at h

omit [Field E] in
/-- the first h + 1 coordinates of a point: the first, and the first h of the rest -/
theorem pre_succ {k h : ℕ} (hk : h + 1 ≤ k + 1) (γ : Fin (k + 1) → E) :
    (fun i : Fin (h + 1) => γ (Fin.castLE hk i)) =
      Fin.cons (γ 0) fun i : Fin h => Fin.tail γ (Fin.castLE (Nat.le_of_succ_le_succ hk) i) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · rfl
  · rfl

end Kernel

namespace Spec
variable (E : Type) [Field E] (P : Type)

def ldx_fold_closed : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h : ℕ) (hk : h ≤ k) (h0 : endH k h = 0)
      (γ : Fin k → E) (f : (stg C Z Zw k h).Word),
    (Rename.last C Z Zw h0).word ((stgChain C Z Zw k h).foldAll (stgPt C Z Zw k h γ) f) =
      mkW (C₁ := C) (C₂ := Z.pair Zw) (fun p => foldV γ (fstW f p))
        (mkW (C₁ := Z) (C₂ := Zw) (fun p => foldV (fun i => γ (Fin.castLE hk i)) (fstW (sndW f) p))
          (fun p => foldV (fun i => γ (Fin.castLE hk i)) (sndW (sndW f) p)))

def ldx_foldW_closed : Prop :=
  ∀ (C Z Zw : LdCode E P) (k h : ℕ) (hk : h ≤ k) (h0 : endH k h = 0)
      (γ : Fin k → E) (w : (stg C Z Zw k h).MR),
    (Rename.last C Z Zw h0).mr ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w) =
      mkM (C₁ := C) (C₂ := Z.pair Zw) (foldV γ (fstM w).1, foldV γ (fstM w).2)
        (mkM (C₁ := Z) (C₂ := Zw)
          (foldV (fun i => γ (Fin.castLE hk i)) (fstM (sndM w)).1,
            foldV (fun i => γ (Fin.castLE hk i)) (fstM (sndM w)).2)
          (foldV (fun i => γ (Fin.castLE hk i)) (sndM (sndM w)).1,
            foldV (fun i => γ (Fin.castLE hk i)) (sndM (sndM w)).2))

end Spec

section
variable (E : Type) [Field E] (P : Type)

theorem fold_closed_aux (C Z Zw : LdCode E P) :
    ∀ (k h : ℕ) (hk : h ≤ k) (γ : Fin k → E) (f : (stg C Z Zw k h).Word),
      (∀ p r s, fstW ((stgChain C Z Zw k h).foldAll (stgPt C Z Zw k h γ) f) p (r, s) =
        foldV γ (fstW f p) s) ∧
      (∀ p r s, fstW (sndW ((stgChain C Z Zw k h).foldAll (stgPt C Z Zw k h γ) f)) p (r, s) =
        foldV (fun i => γ (Fin.castLE hk i)) (fstW (sndW f) p) s) ∧
      (∀ p r s, sndW (sndW ((stgChain C Z Zw k h).foldAll (stgPt C Z Zw k h γ) f)) p (r, s) =
        foldV (fun i => γ (Fin.castLE hk i)) (sndW (sndW f) p) s) := by
  intro k
  induction k with
  | zero =>
    intro h hk γ f
    obtain rfl : h = 0 := by omega
    exact ⟨fun p r s => (foldV_zero γ _ r s).symm,
      fun p r s => (foldV_zero _ _ r s).symm,
      fun p r s => (foldV_zero _ _ r s).symm⟩
  | succ k ih =>
    intro h hk γ f
    cases h with
    | zero =>
      obtain ⟨i1, i2, i3⟩ :=
        ih 0 (Nat.zero_le k) (Fin.tail γ) ((Halving.step C Z Zw k 0).fold (γ 0) f)
      refine ⟨fun p r s => (i1 p r s).trans (foldV_succ γ (fstW f p) s).symm,
        fun p r s => (i2 p r s).trans ?_,
        fun p r s => (i3 p r s).trans ?_⟩
      · rw [foldV_zero _ _ (fun _ => false) s, foldV_zero _ _ (fun _ => false) s]
        show (1 - γ 0) * fstW (sndW f) p (_, s) + γ 0 * fstW (sndW f) p (_, s) = _
        ring
      · rw [foldV_zero _ _ (fun _ => false) s, foldV_zero _ _ (fun _ => false) s]
        show (1 - γ 0) * sndW (sndW f) p (_, s) + γ 0 * sndW (sndW f) p (_, s) = _
        ring
    | succ h =>
      obtain ⟨i1, i2, i3⟩ :=
        ih h (Nat.le_of_succ_le_succ hk) (Fin.tail γ) ((Halving.step C Z Zw k (h + 1)).fold (γ 0) f)
      refine ⟨fun p r s => (i1 p r s).trans (foldV_succ γ (fstW f p) s).symm,
        fun p r s => (i2 p r s).trans ?_,
        fun p r s => (i3 p r s).trans ?_⟩
      · rw [pre_succ hk γ, foldV_cons]
        rfl
      · rw [pre_succ hk γ, foldV_cons]
        rfl

theorem ldx_fold_closed : Spec.ldx_fold_closed E P := by
  intro C Z Zw k h hk h0 γ f
  obtain ⟨i1, i2, i3⟩ := fold_closed_aux E P C Z Zw k h hk γ f
  funext p
  rcases p with p | p | p
  · exact funext fun s => i1 p _ s
  · exact funext fun s => i2 p _ s
  · exact funext fun s => i3 p _ s

theorem foldW_closed_aux (C Z Zw : LdCode E P) :
    ∀ (k h : ℕ) (hk : h ≤ k) (γ : Fin k → E) (w : (stg C Z Zw k h).MR),
      ((∀ r j, (fstM ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w)).1 (r, j) =
          foldV γ (fstM w).1 j) ∧
        (∀ r q, (fstM ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w)).2 (r, q) =
          foldV γ (fstM w).2 q)) ∧
      ((∀ r j, (fstM (sndM ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w))).1 (r, j) =
          foldV (fun i => γ (Fin.castLE hk i)) (fstM (sndM w)).1 j) ∧
        (∀ r q, (fstM (sndM ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w))).2 (r, q) =
          foldV (fun i => γ (Fin.castLE hk i)) (fstM (sndM w)).2 q)) ∧
      ((∀ r j, (sndM (sndM ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w))).1 (r, j) =
          foldV (fun i => γ (Fin.castLE hk i)) (sndM (sndM w)).1 j) ∧
        (∀ r q, (sndM (sndM ((stgChain C Z Zw k h).foldAllW (stgPt C Z Zw k h γ) w))).2 (r, q) =
          foldV (fun i => γ (Fin.castLE hk i)) (sndM (sndM w)).2 q)) := by
  intro k
  induction k with
  | zero =>
    intro h hk γ w
    obtain rfl : h = 0 := by omega
    exact ⟨⟨fun r j => (foldV_zero γ _ r j).symm, fun r q => (foldV_zero γ _ r q).symm⟩,
      ⟨fun r j => (foldV_zero _ _ r j).symm, fun r q => (foldV_zero _ _ r q).symm⟩,
      ⟨fun r j => (foldV_zero _ _ r j).symm, fun r q => (foldV_zero _ _ r q).symm⟩⟩
  | succ k ih =>
    intro h hk γ w
    cases h with
    | zero =>
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ :=
        ih 0 (Nat.zero_le k) (Fin.tail γ) ((Halving.step C Z Zw k 0).foldW (γ 0) w)
      refine ⟨⟨fun r j => (a1 r j).trans (foldV_succ γ (fstM w).1 j).symm,
          fun r q => (a2 r q).trans (foldV_succ γ (fstM w).2 q).symm⟩,
        ⟨fun r j => (b1 r j).trans ?_, fun r q => (b2 r q).trans ?_⟩,
        ⟨fun r j => (c1 r j).trans ?_, fun r q => (c2 r q).trans ?_⟩⟩
      · rw [foldV_zero _ _ (fun _ => false) j, foldV_zero _ _ (fun _ => false) j]
        show (1 - γ 0) * (fstM (sndM w)).1 (_, j) + γ 0 * (fstM (sndM w)).1 (_, j) = _
        ring
      · rw [foldV_zero _ _ (fun _ => false) q, foldV_zero _ _ (fun _ => false) q]
        show (1 - γ 0) * (fstM (sndM w)).2 (_, q) + γ 0 * (fstM (sndM w)).2 (_, q) = _
        ring
      · rw [foldV_zero _ _ (fun _ => false) j, foldV_zero _ _ (fun _ => false) j]
        show (1 - γ 0) * (sndM (sndM w)).1 (_, j) + γ 0 * (sndM (sndM w)).1 (_, j) = _
        ring
      · rw [foldV_zero _ _ (fun _ => false) q, foldV_zero _ _ (fun _ => false) q]
        show (1 - γ 0) * (sndM (sndM w)).2 (_, q) + γ 0 * (sndM (sndM w)).2 (_, q) = _
        ring
    | succ h =>
      obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ :=
        ih h (Nat.le_of_succ_le_succ hk) (Fin.tail γ)
          ((Halving.step C Z Zw k (h + 1)).foldW (γ 0) w)
      refine ⟨⟨fun r j => (a1 r j).trans (foldV_succ γ (fstM w).1 j).symm,
          fun r q => (a2 r q).trans (foldV_succ γ (fstM w).2 q).symm⟩,
        ⟨fun r j => (b1 r j).trans ?_, fun r q => (b2 r q).trans ?_⟩,
        ⟨fun r j => (c1 r j).trans ?_, fun r q => (c2 r q).trans ?_⟩⟩
      all_goals
        rw [pre_succ hk γ, foldV_cons]
        rfl

theorem ldx_foldW_closed : Spec.ldx_foldW_closed E P := by
  intro C Z Zw k h hk h0 γ w
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩, ⟨c1, c2⟩⟩ := foldW_closed_aux E P C Z Zw k h hk γ w
  refine Prod.ext (funext fun j => ?_) (funext fun q => ?_)
  · rcases j with j | j | j
    · exact a1 _ j
    · exact b1 _ j
    · exact c1 _ j
  · rcases q with q | q | q
    · exact a2 _ q
    · exact b2 _ q
    · exact c2 _ q

end
end Cb
