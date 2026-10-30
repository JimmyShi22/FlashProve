-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSumRun.lean: facts on round polynomials and on a prover given in closed form, for the proof
that, for 2 ≤ n, the honest prover of the zero-knowledge sumcheck is the sumcheck prover.

Definitions, lemmas and their proofs. All but `hRounds_cons` are used in the proofs of
`Spec.ld_sum_run` and `Spec.ld_sum_rounds` (Cb/Ld/LdSum.lean), which are in Cb/Ld/LdSumHon.lean.

Main names:
  `hRounds_cons`: round polynomials of any summand are consistent with its sum, and the verifier
    ends with the summand's value at the challenges.
  `HRounds.add_smul`: if q and q' hold the round polynomials of f and f' at the same challenges,
    then q + a q' holds those of f + a f'.
  `sTr_rounds`: for 2 ≤ n, `sTr` holds the round polynomials of the inner product of two folded
    tables (`sCl`).
  `sStrat_run`: a prover made from messages in closed form (the set of challenges non-empty) sends
    them, if each round's part does not depend on later challenges (`SCausal`).
-/
import Cb.Ld.LdSum
import Cb.Ld.LdHideProofs
import Alg.Mle

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section General
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem hRounds_cons :
    ∀ (l : List (HVar R)) (f : HPt l → M) (q : RIdx l → M) (γ : HPt l),
      HRounds l f q γ → HCons l (hSumAll l f) q γ ∧ hFin l (hSumAll l f) q γ = f γ := by
  intro l
  induction l with
  | nil => intro f q γ _; exact ⟨trivial, rfl⟩
  | cons v l ih =>
      intro f q γ h
      obtain ⟨i1, i2⟩ := ih _ _ _ h.2
      have e : hev (fun t : Fin (v.n + 1) => q (.inl t)) γ.1 = hSumAll l fun xs => f (γ.1, xs) :=
        h.1 γ.1
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact congrArg v.sum (funext h.1)
      · show HCons l (hev (fun t : Fin (v.n + 1) => q (.inl t)) γ.1) _ _
        rw [e]; exact i1
      · show hFin l (hev (fun t : Fin (v.n + 1) => q (.inl t)) γ.1) _ _ = _
        rw [e]; exact i2

theorem hev_smul {n : ℕ} (a : R) (c : Fin (n + 1) → M) (x : R) :
    hev (fun t => a • c t) x = a • hev c x := by
  simp only [hev, Finset.smul_sum, smul_comm a]

theorem HVar.sum_smul (v : HVar R) (a : R) (g : R → M) :
    v.sum (fun x => a • g x) = a • v.sum g := by
  simp only [HVar.sum, Finset.smul_sum, smul_comm a]

theorem hSumAll_add_smul :
    ∀ (l : List (HVar R)) (f f' : HPt l → M) (a : R),
      hSumAll l (fun x => f x + a • f' x) = hSumAll l f + a • hSumAll l f' := by
  intro l
  induction l with
  | nil => intro _ _ _; rfl
  | cons v l ih =>
      intro f f' a
      show v.sum (fun x => hSumAll l fun xs => f (x, xs) + a • f' (x, xs)) = v.sum _ + a • v.sum _
      rw [← HVar.sum_smul, ← HVar.sum_add]
      exact congrArg v.sum (funext fun x => ih _ _ _)

theorem HRounds.add_smul :
    ∀ (l : List (HVar R)) {f f' : HPt l → M} {q q' : RIdx l → M} {γ : HPt l} (a : R),
      HRounds l f q γ → HRounds l f' q' γ →
      HRounds l (fun x => f x + a • f' x) (fun i => q i + a • q' i) γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ _ _ _; trivial
  | cons v l ih =>
      intro f f' q q' γ a h h'
      refine ⟨fun x => ?_, ih a h.2 h'.2⟩
      rw [hev_add (fun t => q (.inl t)) (fun t => a • q' (.inl t)), hev_smul,
        h.1, h'.1, hSumAll_add_smul]

theorem HRounds.congr :
    ∀ (l : List (HVar R)) {f f' : HPt l → M} {q : RIdx l → M} {γ : HPt l},
      (∀ x, f x = f' x) → HRounds l f q γ → HRounds l f' q γ := by
  intro l f f' q γ h hr
  rwa [← funext h]

end General

section Rounds
variable {E Ch : Type} [Field E] [Fintype Ch] [Nonempty Ch] (val : Ch → E) (n : ℕ)

theorem sVars_ok (hn : 1 ≤ n) (k : ℕ) : ∀ v ∈ sVars E n k, v.OK := fun v hv => by
  rw [List.eq_of_mem_replicate hv]; exact plain_ok E n hn

/-- each round's part does not depend on later challenges -/
def SCausal : (k : ℕ) → (HPt (sVars E n k) → RIdx (sVars E n k) → E) → Prop
  | 0, _ => True
  | k + 1, q =>
    (∀ γ γ' t, q γ (.inl t) = q γ' (.inl t)) ∧ ∀ x, SCausal k fun γ i => q (x, γ) (.inr i)

theorem sStrat_run {β : Type} :
    ∀ (k : ℕ) (q : HPt (sVars E n k) → RIdx (sVars E n k) → E) (res : HPt (sVars E n k) → β),
      SCausal n k q →
      ∀ ρ : Rho (List.replicate k (sRound E Ch n)),
        sQ n k ((sStrat val n k q res).run ρ).1.plains = q (sG val n k ρ) ∧
        ((sStrat val n k q res).run ρ).1.rho = ρ ∧
        ((sStrat val n k q res).run ρ).2 = res (sG val n k ρ) := by
  intro k
  induction k with
  | zero => intro q res _ ρ; exact ⟨funext fun i => i.elim, rfl, rfl⟩
  | succ k ih =>
      intro q res hq ρ
      obtain ⟨i1, i2, i3⟩ :=
        ih (fun γ i => q (val ρ.1, γ) (.inr i)) (fun γ => res (val ρ.1, γ)) (hq.2 _) ρ.2
      refine ⟨funext fun i => ?_, ?_, i3⟩
      · cases i with
        | inl t => exact hq.1 _ _ t
        | inr i => exact congrFun i1 i
      · exact Prod.ext rfl i2

theorem hTr_causal :
    ∀ (k : ℕ) (Λ : E) (W : HIdx (sVars E n k) → E), SCausal n k (hTr (sVars E n k) Λ W) := by
  intro k
  induction k with
  | zero => intro _ _; trivial
  | succ k ih =>
      intro Λ W
      exact ⟨fun _ _ _ => rfl,
        fun x =>
          ih (hev (HVar.plain E n).psi x • Λ +
              hev (Fin.cons 0 fun t => W (.inl t) : Fin ((HVar.plain E n).n + 1) → E) x)
            fun i => W (.inr i)⟩

variable {J : Type} [Fintype J]

theorem sTr_causal : ∀ (k : ℕ) (L m : (Fin k → Bool) → J → E), SCausal n k (sTr n k L m) := by
  intro k
  induction k with
  | zero => intro _ _; trivial
  | succ k ih => intro L m; exact ⟨fun _ _ _ => rfl, fun x => ih (sFold1 x L) (sFold1 x m)⟩

theorem SCausal.add_mul :
    ∀ (k : ℕ) {q q' : HPt (sVars E n k) → RIdx (sVars E n k) → E} (a : E),
      SCausal n k q → SCausal n k q' → SCausal n k fun γ i => q γ i + a * q' γ i := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _; trivial
  | succ k ih =>
      intro q q' a h h'
      exact ⟨fun γ γ' t => by
        show q γ (.inl t) + a * q' γ (.inl t) = q γ' (.inl t) + a * q' γ' (.inl t)
        rw [h.1 γ γ' t, h'.1 γ γ' t], fun x => ih a (h.2 x) (h'.2 x)⟩

/-- the inner product of two tables, each folded at a point, as a function of that point -/
def sCl (k : ℕ) (L m : (Fin k → Bool) → J → E) (γ : HPt (sVars E n k)) : E :=
  ∑ c, (∑ b, Alg.eqk (sPt n k γ) b * L b c) * ∑ b, Alg.eqk (sPt n k γ) b * m b c

omit [Fintype J] in
theorem sFold_eqk {k : ℕ} (L : (Fin (k + 1) → Bool) → J → E) (x : E) (z : Fin k → E) (c : J) :
    ∑ b, Alg.eqk (Fin.cons x z : Fin (k + 1) → E) b * L b c =
      ∑ b, Alg.eqk z b * sFold1 x L b c := by
  rw [Alg.sum_cube_succ]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Alg.eqk_cons, Alg.eqk_cons]
  simp only [sFold1, sHalf, if_true, Bool.false_eq_true, if_false]
  ring

theorem sCl_succ (k : ℕ) (L m : (Fin (k + 1) → Bool) → J → E) (x : E) (xs : HPt (sVars E n k)) :
    sCl n (k + 1) L m (x, xs) = sCl n k (sFold1 x L) (sFold1 x m) xs := by
  unfold sCl
  refine Finset.sum_congr rfl fun c _ => ?_
  show (∑ b, Alg.eqk (Fin.cons x (sPt n k xs) : Fin (k + 1) → E) b * L b c) *
      (∑ b, Alg.eqk (Fin.cons x (sPt n k xs) : Fin (k + 1) → E) b * m b c) = _
  rw [sFold_eqk, sFold_eqk]

omit [Fintype J] in
theorem sFold1_zero {k : ℕ} (L : (Fin (k + 1) → Bool) → J → E) : sFold1 0 L = sHalf false L := by
  funext b c; simp [sFold1]
omit [Fintype J] in
theorem sFold1_one {k : ℕ} (L : (Fin (k + 1) → Bool) → J → E) : sFold1 1 L = sHalf true L := by
  funext b c; simp [sFold1]

theorem sBl_succ {k : ℕ} (L m : (Fin (k + 1) → Bool) → J → E) :
    sBl L m = sBl (sHalf false L) (sHalf false m) + sBl (sHalf true L) (sHalf true m) := by
  unfold sBl
  rw [Alg.sum_cube_succ, Finset.sum_add_distrib]
  rfl

theorem plain_sum (g : E → E) : (HVar.plain E n).sum g = g 0 + g 1 := by
  show ∑ b : Bool, (1 : E) • g (if b then (1 : E) else 0) = _
  rw [Fintype.sum_bool]
  simp [add_comm]

theorem sCl_sum :
    ∀ (k : ℕ) (L m : (Fin k → Bool) → J → E), hSumAll (sVars E n k) (sCl n k L m) = sBl L m := by
  intro k
  induction k with
  | zero =>
      intro L m
      show sCl n 0 L m () = _
      simp [sCl, sBl, Alg.eqk]
  | succ k ih =>
      intro L m
      show (HVar.plain E n).sum
          (fun x => hSumAll (sVars E n k) fun xs => sCl n (k + 1) L m (x, xs)) = _
      rw [plain_sum, funext (sCl_succ n k L m 0), funext (sCl_succ n k L m 1), ih, ih, sFold1_zero,
        sFold1_zero, sFold1_one, sFold1_one, sBl_succ]

theorem hev_quad (hn : 2 ≤ n) (c0 c1 c2 x : E) :
    hev (fun t : Fin (n + 1) =>
          if (t : ℕ) = 0 then c0 else if (t : ℕ) = 1 then c1 else if (t : ℕ) = 2 then c2 else 0) x =
      c0 + x * c1 + x ^ 2 * c2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  unfold hev
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Finset.sum_eq_zero]
  · have h2 : 2 % (m + 2 + 1) = 2 := Nat.mod_eq_of_lt (by omega)
    simp [h2]
    ring
  · intro t _
    simp

theorem sBl_fold {k : ℕ} (L m : (Fin (k + 1) → Bool) → J → E) (x : E) :
    sBl (sFold1 x L) (sFold1 x m) =
      sBl (sHalf false L) (sHalf false m) +
        x * (sBl (sHalf false L) (sHalf true m - sHalf false m) +
            sBl (sHalf true L - sHalf false L) (sHalf false m)) +
        x ^ 2 * sBl (sHalf true L - sHalf false L) (sHalf true m - sHalf false m) := by
  simp only [sBl, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [sFold1, Pi.sub_apply]
  ring

theorem sTr_rounds (hn : 2 ≤ n) :
    ∀ (k : ℕ) (L m : (Fin k → Bool) → J → E) (γ : HPt (sVars E n k)),
      HRounds (sVars E n k) (sCl n k L m) (sTr n k L m γ) γ := by
  intro k
  induction k with
  | zero => intro _ _ _; trivial
  | succ k ih =>
      intro L m γ
      refine ⟨fun x => ?_, ?_⟩
      · rw [funext (sCl_succ n k L m x), sCl_sum, sBl_fold]
        exact hev_quad n hn _ _ _ x
      · show HRounds (sVars E n k) (fun xs => sCl n (k + 1) L m (γ.1, xs))
          (sTr n k (sFold1 γ.1 L) (sFold1 γ.1 m) γ.2) γ.2
        rw [funext (sCl_succ n k L m γ.1)]
        exact ih _ _ _

end Rounds
end Cb
