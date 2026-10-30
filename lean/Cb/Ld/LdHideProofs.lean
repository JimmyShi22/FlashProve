-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdHideProofs.lean: the proofs of the statements of Cb/Ld/LdHide.lean.

Main names (statements and hypotheses: Cb/Ld/LdHide.lean):
  `hide_dec`: the closed forms `hMu`, `hTr` against the sum and the round polynomials.
  `hide_cons`, `hide_inv_left`, `hide_inv_right`: the bijection from coefficients to consistent
    messages, with its inverse `hInv`.
  `hide_end`: the value with which the verifier ends. `hide_form`: the value at a point as a linear
    form. `hide_add`: additivity of the map.
  `hide_card`, `hide_fibre`: the number of consistent tuples; preimages for coefficients in R.
  `hide_pass`, `hide_law`: see their statements in Cb/Ld/LdHide.lean.
-/
import Cb.Ld.LdHide

set_option autoImplicit false

namespace Cb
open Prob

section Lemmas
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem hev_add {n : ℕ} (c c' : Fin (n + 1) → M) (x : R) :
    hev (fun t => c t + c' t) x = hev c x + hev c' x := by
  simp only [hev, smul_add, Finset.sum_add_distrib]

theorem hev_sub {n : ℕ} (c c' : Fin (n + 1) → M) (x : R) :
    hev (fun t => c t - c' t) x = hev c x - hev c' x := by
  simp only [hev, smul_sub, Finset.sum_sub_distrib]

theorem hev_smul_right {n : ℕ} (p : Fin (n + 1) → R) (Λ : M) (x : R) :
    hev (fun t => p t • Λ) x = hev p x • Λ := by
  simp only [hev, Finset.sum_smul, smul_smul, smul_eq_mul]

theorem hev_const {n : ℕ} (κ : M) (x : R) :
    hev (fun t : Fin (n + 1) => if t = 0 then κ else 0) x = κ := by
  unfold hev
  rw [Finset.sum_eq_single 0]
  · simp
  · intro t _ ht
    simp [ht]
  · simp

theorem hev_rc (v : HVar R) (Λ : M) (W : Fin v.n → M) (κ : M) (x : R) :
    hev (hRc v Λ W κ) x = hev v.psi x • Λ + hev (Fin.cons 0 W : Fin (v.n + 1) → M) x + κ := by
  unfold hRc
  rw [hev_add (fun t => v.psi t • Λ + (Fin.cons 0 W : Fin (v.n + 1) → M) t)
        (fun t => if t = 0 then κ else 0) x,
    hev_add (fun t => v.psi t • Λ) (Fin.cons 0 W : Fin (v.n + 1) → M) x, hev_smul_right, hev_const]

theorem HVar.sum_add (v : HVar R) (g g' : R → M) :
    v.sum (fun x => g x + g' x) = v.sum g + v.sum g' := by
  simp only [HVar.sum, smul_add, Finset.sum_add_distrib]

theorem HVar.sum_sub (v : HVar R) (g g' : R → M) :
    v.sum (fun x => g x - g' x) = v.sum g - v.sum g' := by
  simp only [HVar.sum, smul_sub, Finset.sum_sub_distrib]

theorem HVar.sum_smul_right (v : HVar R) (p : R → R) (Λ : M) :
    v.sum (fun x => p x • Λ) = v.sum p • Λ := by
  simp only [HVar.sum, Finset.sum_smul, smul_smul, smul_eq_mul]

theorem HVar.sum_const (v : HVar R) (κ : M) : v.sum (fun _ => κ) = v.tot • κ := by
  simp only [HVar.sum, HVar.tot, Finset.sum_smul]

theorem HVar.phi_add (v : HVar R) (c c' : Fin (v.n + 1) → M) :
    v.phi (fun t => c t + c' t) = v.phi c + v.phi c' := by
  unfold HVar.phi
  rw [← HVar.sum_add]
  exact congrArg v.sum (funext fun x => hev_add c c' x)

theorem HVar.phi_sub (v : HVar R) (c c' : Fin (v.n + 1) → M) :
    v.phi (fun t => c t - c' t) = v.phi c - v.phi c' := by
  unfold HVar.phi
  rw [← HVar.sum_sub]
  exact congrArg v.sum (funext fun x => hev_sub c c' x)

theorem HVar.sum_rc (v : HVar R) (Λ : M) (c : Fin (v.n + 1) → M) (κ : M) :
    v.sum (fun x => hev v.psi x • Λ + hev c x + κ) = v.phi v.psi • Λ + v.phi c + v.tot • κ := by
  rw [HVar.sum_add (M := M) v (fun x => hev v.psi x • Λ + hev c x) (fun _ => κ),
    HVar.sum_add (M := M) v (fun x => hev v.psi x • Λ) (hev c), HVar.sum_smul_right, HVar.sum_const]
  rfl

theorem HVar.phi_rc (v : HVar R) (Λ : M) (W : Fin v.n → M) (κ : M) :
    v.phi (hRc v Λ W κ) =
      v.phi v.psi • Λ + v.phi (Fin.cons 0 W : Fin (v.n + 1) → M) + v.tot • κ := by
  rw [← HVar.sum_rc]
  exact congrArg v.sum (funext fun x => hev_rc v Λ W κ x)

theorem hRc_zero (v : HVar R) (Λ : M) (W : Fin v.n → M) (κ : M) :
    hRc v Λ W κ 0 = v.psi 0 • Λ + κ := by
  simp [hRc]

theorem hRc_succ (v : HVar R) (Λ : M) (W : Fin v.n → M) (κ : M) (t : Fin v.n) :
    hRc v Λ W κ t.succ = v.psi t.succ • Λ + W t := by
  simp [hRc, Fin.succ_ne_zero]

theorem hRc_of (v : HVar R) (Λ : M) (q : Fin (v.n + 1) → M) :
    hRc v Λ (fun t => q t.succ - v.psi t.succ • Λ) (q 0 - v.psi 0 • Λ) = q := by
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · rw [hRc_zero]; abel
  · rw [hRc_succ]; abel

end Lemmas

section Main
variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

theorem hide_cons : Spec.hide_cons R M := by
  intro l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons v l ih =>
      intro hOK Λ W γ
      have hv : v.phi v.psi = 1 := hOK v (List.mem_cons_self ..)
      refine ⟨?_, ?_⟩
      · show v.phi (hRc v Λ (fun t => W (.inl t)) (hMu l fun i => W (.inr i))) =
          Λ + (v.phi _ + v.tot • hMu l fun i => W (.inr i))
        rw [HVar.phi_rc, hv, one_smul, add_assoc]
      · show HCons l (hev (hRc v Λ (fun t => W (.inl t)) (hMu l fun i => W (.inr i))) γ.1)
          (hTr l _ (fun i => W (.inr i)) γ.2) γ.2
        rw [hev_rc]
        exact ih (fun u hu => hOK u (List.mem_cons_of_mem _ hu)) _ _ _

theorem hide_inv_left : Spec.hide_inv_left R M := by
  intro l
  induction l with
  | nil => intro _ W _; funext i; cases i; rfl
  | cons v l ih =>
      intro Λ W γ
      have h1 : (fun t : Fin v.n => hTr (v :: l) Λ W γ (.inl t.succ) - v.psi t.succ • Λ) =
          fun t => W (.inl t) := by
        funext t
        show hRc v Λ (fun t => W (.inl t)) _ t.succ - _ = _
        rw [hRc_succ]; abel
      have h0 : hTr (v :: l) Λ W γ (.inl 0) - v.psi 0 • Λ = hMu l fun i => W (.inr i) := by
        show hRc v Λ (fun t => W (.inl t)) _ 0 - _ = _
        rw [hRc_zero]; abel
      funext i
      cases i with
      | inl t => exact congrFun h1 t
      | inr i =>
          show hInv l (hev v.psi γ.1 • Λ +
                hev (Fin.cons 0 fun t : Fin v.n =>
                    hTr (v :: l) Λ W γ (.inl t.succ) - v.psi t.succ • Λ : Fin (v.n + 1) → M) γ.1)
              (hTr (v :: l) Λ W γ (.inl 0) - v.psi 0 • Λ)
              (fun i => hTr (v :: l) Λ W γ (.inr i)) γ.2 i = W (.inr i)
          rw [h1, h0]
          exact congrFun (ih _ (fun i => W (.inr i)) γ.2) i

theorem hide_inv_right : Spec.hide_inv_right R M := by
  intro l
  induction l with
  | nil => intro _ _ μ q _ _; exact ⟨rfl, funext fun i => i.elim⟩
  | cons v l ih =>
      intro hOK Λ μ q γ hq
      have hv : v.phi v.psi = 1 := hOK v (List.mem_cons_self ..)
      obtain ⟨hq1, hq2⟩ := hq
      have key := hRc_of v Λ (fun t => q (.inl t))
      rw [← key, hev_rc] at hq2
      rw [← key, HVar.phi_rc, hv, one_smul, add_assoc] at hq1
      obtain ⟨i1, i2⟩ := ih (fun u hu => hOK u (List.mem_cons_of_mem _ hu)) _ _ _ _ hq2
      refine ⟨?_, ?_⟩
      · show v.phi (Fin.cons 0 fun t : Fin v.n =>
                q (.inl t.succ) - v.psi t.succ • Λ : Fin (v.n + 1) → M) +
            v.tot • hMu l (hInv l _ _ (fun i => q (.inr i)) γ.2) = μ
        rw [i1]
        exact add_left_cancel hq1
      · funext i
        cases i with
        | inl t =>
            show hRc v Λ (fun t : Fin v.n => q (.inl t.succ) - v.psi t.succ • Λ)
                (hMu l (hInv l _ _ (fun i => q (.inr i)) γ.2)) t = q (.inl t)
            rw [i1]
            exact congrFun key t
        | inr i => exact congrFun i2 i

theorem hide_end : Spec.hide_end R M := by
  intro l
  induction l with
  | nil => intro Λ W _; show Λ + W () = (1 : R) • Λ + W (); rw [one_smul]
  | cons v l ih =>
      intro Λ W γ
      show hFin l (hev (hRc v Λ (fun t => W (.inl t)) (hMu l fun i => W (.inr i))) γ.1)
          (hTr l _ (fun i => W (.inr i)) γ.2) γ.2 =
        (hev v.psi γ.1 * hPsi l γ.2) • Λ +
          (hPsi l γ.2 • hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) γ.1 +
            hU l (fun i => W (.inr i)) γ.2)
      rw [hev_rc, ih]
      module

end Main

section More
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

omit [CommRing R] [Module R M] in
theorem HIdx.sum_cons {v : HVar R} {l : List (HVar R)} (f : HIdx (v :: l) → M) :
    ∑ i, f i = ∑ t : Fin v.n, f (.inl t) + ∑ i : HIdx l, f (.inr i) := Fintype.sum_sum_type f

theorem hev_cons0 {n : ℕ} (W : Fin n → M) (x : R) :
    hev (Fin.cons 0 W : Fin (n + 1) → M) x = ∑ t : Fin n, x ^ ((t : ℕ) + 1) • W t := by
  unfold hev
  rw [Fin.sum_univ_succ]
  simp

theorem cons0_add {n : ℕ} (a b : Fin n → M) :
    (Fin.cons 0 (fun t => a t + b t) : Fin (n + 1) → M) =
      fun t => (Fin.cons 0 a : Fin (n + 1) → M) t + (Fin.cons 0 b : Fin (n + 1) → M) t := by
  funext t
  refine Fin.cases ?_ (fun t => ?_) t <;> simp

theorem hstep (a p : R) (Λ c u : M) : (a * p) • Λ + (p • c + u) = p • (a • Λ + c) + u := by module

theorem hSumAll_U :
    ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
      ∀ (Λ : M) (W : HIdx l → M), hSumAll l (fun x => hPsi l x • Λ + hU l W x) = Λ + hMu l W := by
  intro l
  induction l with
  | nil => intro _ Λ W; show (1 : R) • Λ + W () = Λ + W (); rw [one_smul]
  | cons v l ih =>
      intro hOK Λ W
      have hv : v.phi v.psi = 1 := hOK v (List.mem_cons_self ..)
      have h1 : ∀ x : R, hSumAll l (fun xs => hPsi (v :: l) (x, xs) • Λ + hU (v :: l) W (x, xs)) =
          hev v.psi x • Λ + hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) x +
            hMu l fun i => W (.inr i) := by
        intro x
        rw [← ih (fun u hu => hOK u (List.mem_cons_of_mem _ hu))]
        exact congrArg (hSumAll l) (funext fun xs => hstep _ _ _ _ _)
      show v.sum (fun x => hSumAll l fun xs => hPsi (v :: l) (x, xs) • Λ + hU (v :: l) W (x, xs)) =
        Λ + (v.phi _ + v.tot • hMu l fun i => W (.inr i))
      rw [funext h1, HVar.sum_rc, hv, one_smul, add_assoc]

theorem hRounds_U :
    ∀ l : List (HVar R), (∀ v ∈ l, v.OK) →
      ∀ (Λ : M) (W : HIdx l → M) (γ : HPt l),
        HRounds l (fun x => hPsi l x • Λ + hU l W x) (hTr l Λ W γ) γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _; trivial
  | cons v l ih =>
      intro hOK Λ W γ
      have hOK' : ∀ u ∈ l, u.OK := fun u hu => hOK u (List.mem_cons_of_mem _ hu)
      refine ⟨fun x => ?_, ?_⟩
      · show hev (hRc v Λ (fun t => W (.inl t)) (hMu l fun i => W (.inr i))) x =
          hSumAll l fun xs => hPsi (v :: l) (x, xs) • Λ + hU (v :: l) W (x, xs)
        rw [hev_rc, ← hSumAll_U l hOK']
        exact congrArg (hSumAll l) (funext fun xs => (hstep _ _ _ _ _).symm)
      · have e : (fun xs => hPsi (v :: l) (γ.1, xs) • Λ + hU (v :: l) W (γ.1, xs))
            = fun xs =>
                hPsi l xs • (hev v.psi γ.1 • Λ +
                        hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) γ.1) +
                    hU l (fun i => W (.inr i)) xs :=
          funext fun xs => hstep _ _ _ _ _
        show HRounds l (fun xs => hPsi (v :: l) (γ.1, xs) • Λ + hU (v :: l) W (γ.1, xs))
          (hTr l _ (fun i => W (.inr i)) γ.2) γ.2
        rw [e]
        exact ih hOK' _ _ _

theorem hRc_add (v : HVar R) (Λ Λ' : M) (a b : Fin v.n → M) (κ κ' : M) :
    hRc v (Λ + Λ') (fun t => a t + b t) (κ + κ') = fun t => hRc v Λ a κ t + hRc v Λ' b κ' t := by
  funext t
  refine Fin.cases ?_ (fun t => ?_) t
  · simp only [hRc_zero, smul_add]; abel
  · simp only [hRc_succ, smul_add]; abel

theorem hMu_add :
    ∀ (l : List (HVar R)) (W W' : HIdx l → M), hMu l (W + W') = hMu l W + hMu l W' := by
  intro l
  induction l with
  | nil => intro W W'; rfl
  | cons v l ih =>
      intro W W'
      show v.phi (Fin.cons 0 fun t => W (.inl t) + W' (.inl t) : Fin (v.n + 1) → M) +
          v.tot • hMu l ((fun i => W (.inr i)) + fun i => W' (.inr i)) = _
      rw [ih, cons0_add, HVar.phi_add, smul_add]
      show _ = (v.phi _ + v.tot • _) + (v.phi _ + v.tot • _)
      abel

theorem hTr_add :
    ∀ (l : List (HVar R)) (Λ Λ' : M) (W W' : HIdx l → M) (γ : HPt l),
      hTr l (Λ + Λ') (W + W') γ = hTr l Λ W γ + hTr l Λ' W' γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _; funext i; exact i.elim
  | cons v l ih =>
      intro Λ Λ' W W' γ
      funext i
      cases i with
      | inl t =>
          show hRc v (Λ + Λ') (fun t => W (.inl t) + W' (.inl t))
              (hMu l ((fun i => W (.inr i)) + fun i => W' (.inr i))) t = _
          rw [hMu_add, hRc_add]
          rfl
      | inr i =>
          show hTr l (hev v.psi γ.1 • (Λ + Λ') +
                hev (Fin.cons 0 fun t => W (.inl t) + W' (.inl t) : Fin (v.n + 1) → M) γ.1)
              ((fun i => W (.inr i)) + fun i => W' (.inr i)) γ.2 i = _
          have e : hev v.psi γ.1 • (Λ + Λ') +
                hev (Fin.cons 0 fun t => W (.inl t) + W' (.inl t) : Fin (v.n + 1) → M) γ.1 =
              (hev v.psi γ.1 • Λ + hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) γ.1) +
                (hev v.psi γ.1 • Λ' +
                  hev (Fin.cons 0 fun t => W' (.inl t) : Fin (v.n + 1) → M) γ.1) := by
            rw [cons0_add, hev_add, smul_add]; abel
          rw [e, ih]
          rfl

theorem HCons.add :
    ∀ (l : List (HVar R)) {σ σ' : M} {q q' : RIdx l → M} {γ : HPt l},
      HCons l σ q γ → HCons l σ' q' γ → HCons l (σ + σ') (q + q') γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons v l ih =>
      intro σ σ' q q' γ h h'
      refine ⟨?_, ?_⟩
      · show v.phi (fun t => q (.inl t) + q' (.inl t)) = _
        rw [HVar.phi_add, h.1, h'.1]
      · show HCons l (hev (fun t => q (.inl t) + q' (.inl t)) γ.1)
          ((fun i => q (.inr i)) + fun i => q' (.inr i)) γ.2
        rw [hev_add]
        exact ih h.2 h'.2

theorem HCons.sub :
    ∀ (l : List (HVar R)) {σ σ' : M} {q q' : RIdx l → M} {γ : HPt l},
      HCons l σ q γ → HCons l σ' q' γ → HCons l (σ - σ') (q - q') γ := by
  intro l
  induction l with
  | nil => intro _ _ _ _ _ _ _; trivial
  | cons v l ih =>
      intro σ σ' q q' γ h h'
      refine ⟨?_, ?_⟩
      · show v.phi (fun t => q (.inl t) - q' (.inl t)) = _
        rw [HVar.phi_sub, h.1, h'.1]
      · show HCons l (hev (fun t => q (.inl t) - q' (.inl t)) γ.1)
          ((fun i => q (.inr i)) - fun i => q' (.inr i)) γ.2
        rw [hev_sub]
        exact ih h.2 h'.2

end More

section Main2
variable (R : Type) [CommRing R] (M : Type) [AddCommGroup M] [Module R M]

theorem hide_dec : Spec.hide_dec R M := fun l hOK Λ W γ =>
  ⟨hSumAll_U l hOK Λ W, hRounds_U l hOK Λ W γ⟩

theorem hide_add : Spec.hide_add R M := fun l Λ Λ' W W' γ => ⟨hMu_add l W W', hTr_add l Λ Λ' W W' γ⟩

theorem hide_form : Spec.hide_form R M := by
  intro l
  induction l with
  | nil =>
      intro W _
      show W () = ∑ i : Unit, (1 : R) • W i
      simp
  | cons v l ih =>
      intro W γ
      show hPsi l γ.2 • hev (Fin.cons 0 fun t => W (.inl t) : Fin (v.n + 1) → M) γ.1 +
          hU l (fun i => W (.inr i)) γ.2 = _
      rw [HIdx.sum_cons, hev_cons0, Finset.smul_sum, ih]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun t _ => ?_) rfl
      rw [smul_smul]
      rfl

variable {R M}

/-- The bijection from the coefficients to the consistent tuples (sum, round polynomials) at γ, if
every variable has `HVar.OK` (`hOK`). -/
def hEquiv (l : List (HVar R)) (hOK : ∀ v ∈ l, v.OK) (γ : HPt l) :
    (HIdx l → M) ≃ {p : M × (RIdx l → M) // HCons l p.1 p.2 γ} where
  toFun W := ⟨(hMu l W, hTr l 0 W γ), by have h := hide_cons R M l hOK 0 W γ; rwa [zero_add] at h⟩
  invFun p := hInv l 0 p.1.1 p.1.2 γ
  left_inv W := hide_inv_left R M l 0 W γ
  right_inv p := by
    obtain ⟨h1, h2⟩ := hide_inv_right R M l hOK 0 p.1.1 p.1.2 γ (by rw [zero_add]; exact p.2)
    exact Subtype.ext (Prod.ext h1 h2)

theorem hMsg_eq_iff (l : List (HVar R)) (hOK : ∀ v ∈ l, v.OK) (γ : HPt l) (p : M × (RIdx l → M))
    (hp : HCons l p.1 p.2 γ) (W : HIdx l → M) :
    (hMu l W, hTr l 0 W γ) = p ↔ W = hInv l 0 p.1 p.2 γ := by
  constructor
  · rintro rfl
    exact (hide_inv_left R M l 0 W γ).symm
  · rintro rfl
    obtain ⟨h1, h2⟩ := hide_inv_right R M l hOK 0 p.1 p.2 γ (by rw [zero_add]; exact hp)
    exact Prod.ext h1 h2

/-- Coefficients in R: `hAgg m` as an additive map. -/
def hAggHom {r : ℕ} (m : Fin r → M) (l : List (HVar R)) : (HIdx l → Fin r → R) →+ (HIdx l → M) where
  toFun := hAgg m
  map_zero' := by funext i; simp [hAgg]
  map_add' := by intro a b; funext i; simp [hAgg, add_smul, Finset.sum_add_distrib]

theorem hAgg_surj {r : ℕ} (m : Fin r → M)
    (hm : ∀ x : M, ∃ a : Fin r → R, ∑ u, a u • m u = x) (l : List (HVar R)) :
    Function.Surjective (hAggHom m l) := by
  intro W
  choose a ha using hm
  exact ⟨fun i => a (W i), funext fun i => ha (W i)⟩

variable (R M)

theorem hide_card [Fintype M] : Spec.hide_card R M := by
  intro l hOK γ
  unfold cnt
  rw [Nat.card_congr (hEquiv l hOK γ).symm, Nat.card_eq_fintype_card, Fintype.card_fun]

theorem hide_fibre [Fintype R] [Fintype M] : Spec.hide_fibre R M := by
  intro l hOK r m hm γ p
  refine ⟨fun hp => ?_, fun hp w hw => hp ?_⟩
  · have e : (fun w : HIdx l → Fin r → R => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ) = p) =
        fun w => hAggHom m l w = hInv l 0 p.1 p.2 γ :=
      funext fun w => propext (hMsg_eq_iff l hOK γ p hp (hAgg m w))
    have h := (map_unif_eq_unif_iff _).1
      (map_unif_addMonoidHom (hAggHom m l) (hAgg_surj m hm l)) (hInv l 0 p.1 p.2 γ)
    rw [e]
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul] at h
    exact h
  · rw [← hw]
    have h := hide_cons R M l hOK 0 (hAgg m w) γ
    rwa [zero_add] at h

theorem hide_pass [Fintype R] [Fintype M] : Spec.hide_pass R M := by
  intro l hOK r m hm γ σ u hu p
  have hiff : HCons l (p.1 + σ) p.2 γ ↔ HCons l p.1 (p.2 - u) γ := by
    constructor
    · intro h
      have := HCons.sub l h hu
      rwa [add_sub_cancel_right] at this
    · intro h
      have := HCons.add l h hu
      rwa [sub_add_cancel] at this
  have e : ∀ w : HIdx l → Fin r → R,
      ((hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u) = p) ↔
      ((hMu l (hAgg m w), hTr l 0 (hAgg m w) γ) = (p.1, p.2 - u)) := by
    intro w
    constructor
    · rintro rfl
      simp
    · intro h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext h1
        (by show _ + u = p.2; rw [show hTr l 0 (hAgg m w) γ = p.2 - u from h2, sub_add_cancel])
  obtain ⟨f1, f2⟩ := hide_fibre R M l hOK r m hm γ (p.1, p.2 - u)
  refine ⟨fun hp => ?_, fun hp w hw => f2 (fun h => hp (hiff.2 h)) w ((e w).1 hw)⟩
  rw [funext fun w => propext (e w)]
  exact f1 (hiff.1 hp)

theorem hide_law [Fintype R] [Nonempty R] : Spec.hide_law R M := by
  intro l hOK r m hm γ σ u u' hu hu'
  have h0 : HCons l (0 + 0) (u - u') γ := by
    have := HCons.sub l hu hu'
    rwa [sub_self, ← add_zero (0 : M)] at this
  obtain ⟨i1, i2⟩ := hide_inv_right R M l hOK 0 0 (u - u') γ h0
  obtain ⟨w₀, hw₀⟩ := hAgg_surj m hm l (hInv l 0 0 (u - u') γ)
  have hw₀' : hAgg m w₀ = hInv l 0 0 (u - u') γ := hw₀
  have e : (fun w : HIdx l → Fin r → R => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u))
      = (fun w => (hMu l (hAgg m w), hTr l 0 (hAgg m w) γ + u')) ∘ Equiv.addRight w₀ := by
    funext w
    have ha : hAgg m (w + w₀) = hAgg m w + hAgg m w₀ := (hAggHom m l).map_add w w₀
    have ht := hTr_add l 0 0 (hAgg m w) (hAgg m w₀) γ
    rw [add_zero] at ht
    show _ = (hMu l (hAgg m (w + w₀)), hTr l 0 (hAgg m (w + w₀)) γ + u')
    rw [ha, hMu_add, ht, hw₀', i1, i2, add_zero]
    congr 1
    abel
  rw [e, ← PMF.map_comp, map_unif_equiv (Equiv.addRight w₀)]

theorem plain_phi : Spec.plain_phi R M := by
  intro n c
  show ∑ b : Bool, (1 : R) • hev c (if b then (1 : R) else 0) = _
  rw [Fintype.sum_bool]
  simp [add_comm]

theorem plain_psi : Spec.plain_psi R := by
  intro n x hn
  show ∑ t : Fin (n + 1), x ^ (t : ℕ) • (if (t : ℕ) = 1 then (1 : R) else 0) = x
  rw [Finset.sum_eq_single (⟨1, by omega⟩ : Fin (n + 1))]
  · simp
  · intro t _ ht
    have : (t : ℕ) ≠ 1 := fun h => ht (Fin.ext h)
    simp [this]
  · simp

theorem plain_ok : Spec.plain_ok R := by
  intro n hn
  unfold HVar.OK
  rw [plain_phi R R]
  exact (congrArg₂ (· + ·) (plain_psi R n 0 hn) (plain_psi R n 1 hn)).trans (zero_add 1)

theorem plain_card : Spec.plain_card R := by
  intro k n
  induction k with
  | zero => show Fintype.card Unit = _; simp
  | succ k ih =>
      show Fintype.card (Fin n ⊕ HIdx (List.replicate k (HVar.plain R n))) = _
      rw [Fintype.card_sum, ih, Fintype.card_fin]
      ring

end Main2
end Cb
