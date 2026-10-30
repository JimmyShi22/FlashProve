-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdSwitchPrivProofs.lean: the proofs of the statements of Cb/Ld/LdSwitchPriv.lean (private
sample maps over one finite field), and of `Spec.ldSwitch_blind_of_private` and
`Spec.ldSwitch_blind_of_sim`, which Cb/Ld/LdSwitch.lean states.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Why the bound `ldPriv_fibre` holds. Fix r ≠ 0 and write N t for the number of onto matrices that
send r to t. Each onto matrix is counted in exactly one N t. For every t and every t' ≠ 0,
N t ≤ N t' (`fibre_le`), by an injection:
 * t ≠ 0: M ↦ L M, where L y = y + (ψ · y)(t' - t) with a functional ψ such that ψ · t = 1 and
   ψ · t' ≠ 0; L is injective, so onto, and sends t to t';
 * t = 0: M ↦ M + t' φ, with a functional φ such that φ · r = 1; since M r = 0, M is already onto
   on the kernel of φ, where the two matrices agree.
So (number of t' ≠ 0) · N t is at most the sum of the N t' over t' ≠ 0, which is at most the number
of onto matrices.

Everything before the theorems "ldPriv_*" is glue, which no statement reads.

Main names (statements and hypotheses: Cb/Ld/LdSwitchPriv.lean):
  `ldPriv_nonempty`: there is an onto matrix if and only if |S| ≤ |Qo|.
  `ldPriv_le_mxErr`, `ldPriv_mxErr_le`: for r ≠ 0 and every t the number of onto M with M r = t is
    at most mxErr; mxErr is at most every k that bounds all these numbers.
  `ldPriv_fibre`: the bound: for r ≠ 0 and every t: (number of onto M with M r = t) · (|E|^|S| - 1)
    ≤ number of onto matrices.
  `ldPriv_mxErr_bound`: so mxErr · (|E|^|S| - 1) ≤ number of onto matrices.
  `ldPriv_val_boot`: the answers of `Z.boot Qo`. It needs that there is an onto matrix (an instance
    argument, in this and the four statements on `Z.boot` below; `ldPriv_nonempty` says when).
  `ldPriv_ok_boot`: if Z has the property of a sample map (`Sample.OK`, Cb/Gen/OodDec.lean), so has
    Z.boot.
  `ldPriv_frac_boot`: its number (`err`) against the number of seeds: the fraction is at most the
    larger of the error of Z and 1 / (|E|^|S| - 1). (for |S| = 0: see Limits in the head of
    Cb/Ld/LdSwitchPriv.lean)
  `ldPriv_private_boot`, `ldPriv_sim_boot`: see their statements in Cb/Ld/LdSwitchPriv.lean.
  `ldSwitch_blind_of_private`, `ldSwitch_blind_of_sim`: see their statements in Cb/Ld/LdSwitch.lean.

Limits: see the head of Cb/Ld/LdSwitchPriv.lean.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdSwitchPriv
import Cb.Ld.LdSwitch
import Cb.Gen.OodDecPadProofs

set_option autoImplicit false

namespace Cb
open Prob Cb.Ood Finset

namespace Ood.Priv
variable {E S Qo : Type} [Field E]

theorem sum_single_mul {A : Type} [Fintype A] [DecidableEq A] (a : A) (c : E) (u : A → E) :
    ∑ s, (Pi.single a c : A → E) s * u s = c * u a := by
  rw [sum_eq_single a]
  · rw [Pi.single_eq_same]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

/-- a functional that is 1 at a vector other than 0 -/
theorem exists_dual_one {A : Type} [Fintype A] (r : A → E) (hr : r ≠ 0) :
    ∃ φ : A → E, ∑ q, φ q * r q = 1 := by
  classical
  obtain ⟨q₀, h₀⟩ := Function.ne_iff.mp hr
  exact ⟨Pi.single q₀ (r q₀)⁻¹, by rw [sum_single_mul]; exact inv_mul_cancel₀ h₀⟩

/-- a functional that is 1 at t and not 0 at t' -/
theorem exists_dual_two {A : Type} [Fintype A] (t t' : A → E) (ht : t ≠ 0) (ht' : t' ≠ 0) :
    ∃ ψ : A → E, ∑ s, ψ s * t s = 1 ∧ ∑ s, ψ s * t' s ≠ 0 := by
  classical
  obtain ⟨s₀, h₀⟩ := Function.ne_iff.mp ht
  obtain ⟨s₁, h₁⟩ := Function.ne_iff.mp ht'
  have h₀' : t s₀ ≠ 0 := h₀
  have h₁' : t' s₁ ≠ 0 := h₁
  by_cases ha : t' s₀ = 0
  · by_cases hb : t s₁ = 0
    · refine ⟨Pi.single s₀ (t s₀)⁻¹ + Pi.single s₁ 1, ?_, ?_⟩
      · simp only [Pi.add_apply, add_mul, sum_add_distrib, sum_single_mul]
        rw [hb, mul_zero, add_zero]
        exact inv_mul_cancel₀ h₀'
      · simp only [Pi.add_apply, add_mul, sum_add_distrib, sum_single_mul]
        rw [ha, mul_zero, zero_add, one_mul]
        exact h₁'
    · exact ⟨Pi.single s₁ (t s₁)⁻¹,
        by rw [sum_single_mul]; exact inv_mul_cancel₀ hb,
        by rw [sum_single_mul]; exact mul_ne_zero (inv_ne_zero hb) h₁'⟩
  · exact ⟨Pi.single s₀ (t s₀)⁻¹,
      by rw [sum_single_mul]; exact inv_mul_cancel₀ h₀',
      by rw [sum_single_mul]; exact mul_ne_zero (inv_ne_zero h₀') ha⟩

/-- y + (ψ · y) d -/
def lv [Fintype S] (ψ d y : S → E) : S → E := fun s => y s + d s * ∑ s', ψ s' * y s'

theorem lv_inj [Fintype S] (ψ d : S → E) (h : 1 + ∑ s, ψ s * d s ≠ 0) :
    Function.Injective (lv ψ d) := by
  intro y y' hyy
  have hs : ∀ s, y s + d s * ∑ s', ψ s' * y s' = y' s + d s * ∑ s', ψ s' * y' s' := fun s =>
    congrFun hyy s
  have e : ∀ u : S → E, ∑ s, ψ s * (u s + d s * ∑ s', ψ s' * u s') =
      (1 + ∑ s, ψ s * d s) * ∑ s', ψ s' * u s' := fun u => by
    simp only [mul_add, sum_add_distrib, ← mul_assoc, ← sum_mul]
    ring
  have hc : ∑ s', ψ s' * y s' = ∑ s', ψ s' * y' s' :=
    mul_left_cancel₀ h ((e y).symm.trans ((sum_congr rfl fun s _ => by rw [hs s]).trans (e y')))
  funext s
  have := hs s
  rw [hc] at this
  exact add_right_cancel this

/-- the matrix of y ↦ lv ψ d (M y) -/
def lft [Fintype S] (ψ d : S → E) (M : S → Qo → E) : S → Qo → E := fun s q =>
  lv ψ d (fun s' => M s' q) s

theorem mxApp_lft [Fintype S] [Fintype Qo] (ψ d : S → E) (M : S → Qo → E) (x : Qo → E) :
    mxApp (lft ψ d M) x = lv ψ d (mxApp M x) := by
  funext s
  simp only [mxApp, lft, lv, add_mul, sum_add_distrib, mul_sum, sum_mul]
  refine congrArg₂ (· + ·) rfl ?_
  rw [sum_comm]
  exact sum_congr rfl fun s' _ => sum_congr rfl fun q _ => by ring

theorem lft_inj [Fintype S] (ψ d : S → E) (h : 1 + ∑ s, ψ s * d s ≠ 0) :
    Function.Injective (lft (Qo := Qo) ψ d) := by
  intro M M' hMM
  have hq : ∀ q, (fun s' => M s' q) = fun s' => M' s' q := fun q =>
    lv_inj ψ d h (funext fun s => congrFun (congrFun hMM s) q)
  funext s q
  exact congrFun (hq q) s

theorem lft_onto [Fintype E] [Fintype S] [Fintype Qo] (ψ d : S → E) (h : 1 + ∑ s, ψ s * d s ≠ 0)
    {M : S → Qo → E} (hM : MxOnto M) : MxOnto (lft ψ d M) := by
  intro y
  obtain ⟨y₀, hy₀⟩ := Finite.surjective_of_injective (lv_inj ψ d h) y
  obtain ⟨x, hx⟩ := hM y₀
  exact ⟨x, by rw [mxApp_lft, hx, hy₀]⟩

/-- M + t' φ -/
def rgt (φ : Qo → E) (t' : S → E) (M : S → Qo → E) : S → Qo → E := fun s q => M s q + t' s * φ q

theorem mxApp_rgt [Fintype Qo] (φ : Qo → E) (t' : S → E) (M : S → Qo → E) (x : Qo → E) (s : S) :
    mxApp (rgt φ t' M) x s = mxApp M x s + t' s * ∑ q, φ q * x q := by
  simp only [mxApp, rgt, add_mul, sum_add_distrib, mul_sum, mul_assoc]

theorem rgt_inj (φ : Qo → E) (t' : S → E) : Function.Injective (rgt φ t') := by
  intro M M' h
  funext s q
  exact add_right_cancel (congrFun (congrFun h s) q)

theorem rgt_onto [Fintype Qo] (φ r : Qo → E) (t' : S → E) (hφ : ∑ q, φ q * r q = 1) {M : S → Qo → E}
    (hM : MxOnto M) (h0 : mxApp M r = 0) : MxOnto (rgt φ t' M) := by
  intro y
  obtain ⟨x, hx⟩ := hM y
  refine ⟨fun q => x q - (∑ q', φ q' * x q') * r q, funext fun s => ?_⟩
  rw [mxApp_rgt]
  have h1 : mxApp M (fun q => x q - (∑ q', φ q' * x q') * r q) s = y s := by
    have e : mxApp M (fun q => x q - (∑ q', φ q' * x q') * r q) s =
        mxApp M x s - (∑ q', φ q' * x q') * mxApp M r s := by
      simp only [mxApp, mul_sub, sum_sub_distrib, mul_sum]
      exact congrArg₂ (· - ·) rfl (sum_congr rfl fun q _ => by ring)
    rw [e, hx, h0, Pi.zero_apply, mul_zero, sub_zero]
  have h2 : ∑ q, φ q * (x q - (∑ q', φ q' * x q') * r q) = 0 := by
    have e : ∑ q, φ q * (x q - (∑ q', φ q' * x q') * r q) =
        ∑ q, φ q * x q - (∑ q', φ q' * x q') * ∑ q, φ q * r q := by
      simp only [mul_sub, sum_sub_distrib, mul_sum]
      exact congrArg₂ (· - ·) rfl (sum_congr rfl fun q _ => by ring)
    rw [e, hφ, mul_one, sub_self]
  rw [h1, h2, mul_zero, add_zero]

/-- a count is at most another, by an injection between the sets that are counted -/
theorem cnt_le_of_inj {α β : Type} [Finite α] [Finite β] {P : α → Prop} {Q : β → Prop}
    (f : {a // P a} → {b // Q b}) (hf : Function.Injective f) : cnt P ≤ cnt Q :=
  Nat.card_le_card_of_injective f hf

variable [Fintype E] [Fintype S] [Fintype Qo]

/-- for r ≠ 0, the number of onto matrices that send r to t is at most the number of those that send
r to t', if t' ≠ 0 -/
theorem fibre_le (r : Qo → E) (hr : r ≠ 0) (t t' : S → E) (ht' : t' ≠ 0) :
    cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t) ≤
      cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t') := by
  by_cases ht : t = 0
  · subst ht
    obtain ⟨φ, hφ⟩ := exists_dual_one r hr
    refine cnt_le_of_inj
      (fun M => ⟨⟨rgt φ t' M.1.1, rgt_onto φ r t' hφ M.1.2 M.2⟩, funext fun s => ?_⟩)
      fun M M' h => ?_
    · show mxApp (rgt φ t' M.1.1) r s = t' s
      rw [mxApp_rgt, M.2, hφ, Pi.zero_apply, zero_add, mul_one]
    · exact Subtype.ext
        (Subtype.ext
          (rgt_inj φ t' (congrArg (fun z : {M : OntoMx E S Qo // mxApp M.1 r = t'} => z.1.1) h)))
  · obtain ⟨ψ, h1, h2⟩ := exists_dual_two t t' ht ht'
    have hne : 1 + ∑ s, ψ s * (t' - t) s ≠ 0 := by
      have e : ∑ s, ψ s * (t' - t) s = ∑ s, ψ s * t' s - ∑ s, ψ s * t s := by
        simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]
      rw [e, h1, add_sub_cancel]
      exact h2
    refine cnt_le_of_inj
      (fun M => ⟨⟨lft ψ (t' - t) M.1.1, lft_onto ψ (t' - t) hne M.1.2⟩, ?_⟩) fun M M' h => ?_
    · show mxApp (lft ψ (t' - t) M.1.1) r = t'
      rw [mxApp_lft, M.2]
      funext s
      show t s + (t' - t) s * ∑ s', ψ s' * t s' = t' s
      rw [h1, mul_one, Pi.sub_apply, add_sub_cancel]
    · exact Subtype.ext
        (Subtype.ext
          (lft_inj ψ (t' - t) hne
            (congrArg (fun z : {M : OntoMx E S Qo // mxApp M.1 r = t'} => z.1.1) h)))

omit [Fintype S] [Fintype E] in
theorem mxApp_add (M : S → Qo → E) (x y : Qo → E) : mxApp M (x + y) = mxApp M x + mxApp M y := by
  funext s
  simp only [mxApp, Pi.add_apply, mul_add, sum_add_distrib]

omit [Fintype S] [Fintype E] in
theorem mxApp_zero (M : S → Qo → E) : mxApp M 0 = 0 := by
  funext s
  simp only [mxApp, Pi.zero_apply, mul_zero, sum_const_zero]

omit [Fintype S] in
/-- an onto matrix carries a uniform vector, shifted, to a uniform vector -/
theorem map_affine_unif (iC : Fintype (Qo → E)) (iD : Fintype (S → E)) (M : S → Qo → E)
    (hM : MxOnto M) (t₀ : S → E) :
    (unif (Qo → E)).map (fun c => t₀ + mxApp M c) = unif (S → E) := by
  rw [map_unif_eq_unif_iff]
  intro d
  have heq : ∀ d', cnt (fun c : Qo → E => t₀ + mxApp M c = d') =
      cnt (fun c : Qo → E => t₀ + mxApp M c = d) := fun d' => by
    obtain ⟨c₀, hc₀⟩ := hM (d' - d)
    rw [← cnt_equiv (Equiv.addRight c₀) fun c : Qo → E => t₀ + mxApp M c = d']
    refine cnt_congr fun c => ?_
    show t₀ + mxApp M (c + c₀) = d' ↔ t₀ + mxApp M c = d
    rw [mxApp_add, hc₀, ← add_assoc]
    constructor
    · intro h
      have h' : t₀ + mxApp M c + (d' - d) = d + (d' - d) := by rw [h]; abel
      exact add_right_cancel h'
    · intro h
      rw [h]
      abel
  have hsum := sum_cnt_fiber fun c : Qo → E => t₀ + mxApp M c
  rw [sum_congr rfl fun d' _ => heq d', sum_const, card_univ, smul_eq_mul] at hsum
  rw [mul_comm]
  exact hsum

end Ood.Priv

open Ood.Priv

theorem ldPriv_nonempty : Spec.ldPriv_nonempty := by
  intro E S Qo _ _ _ _
  classical
  constructor
  · rintro ⟨M, hM⟩
    have h := Fintype.card_le_of_surjective _ hM
    rw [Fintype.card_fun, Fintype.card_fun] at h
    exact (Nat.pow_le_pow_iff_right Fintype.one_lt_card).mp h
  · intro h
    obtain ⟨ι⟩ := Function.Embedding.nonempty_of_card_le h
    refine ⟨fun s q => if ι s = q then 1 else 0,
      fun t => ⟨fun q => ∑ s, if ι s = q then t s else 0, funext fun s => ?_⟩⟩
    show ∑ q, (if ι s = q then (1 : E) else 0) * (∑ s', if ι s' = q then t s' else 0) = t s
    rw [sum_eq_single (ι s)]
    · rw [if_pos rfl, one_mul, sum_eq_single s]
      · rw [if_pos rfl]
      · intro s' _ hs'
        rw [if_neg fun h => hs' (ι.injective h)]
      · intro h
        exact absurd (mem_univ _) h
    · intro q _ hq
      rw [if_neg fun h => hq h.symm, zero_mul]
    · intro h
      exact absurd (mem_univ _) h

theorem ldPriv_le_mxErr : Spec.ldPriv_le_mxErr := by
  intro E S Qo _ _ _ _ r t hr
  classical
  unfold mxErr
  refine le_trans ?_ (Finset.le_sup (mem_univ (r, t)))
  show _ ≤ if r = 0 then 0 else cnt fun M : OntoMx E S Qo => mxApp M.1 r = t
  rw [if_neg hr]

theorem ldPriv_mxErr_le : Spec.ldPriv_mxErr_le := by
  intro E S Qo _ _ _ _ k h
  classical
  unfold mxErr
  refine Finset.sup_le fun x _ => ?_
  by_cases hx : x.1 = 0
  · rw [if_pos hx]
    exact Nat.zero_le k
  · rw [if_neg hx]
    exact h x.1 x.2 hx

theorem ldPriv_fibre : Spec.ldPriv_fibre := by
  intro E S Qo _ _ _ _ r t hr
  classical
  have hsum := sum_cnt_fiber fun M : OntoMx E S Qo => mxApp M.1 r
  have hcard : (univ.erase (0 : S → E)).card = Fintype.card E ^ Fintype.card S - 1 := by
    rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun]
  have h1 : (univ.erase (0 : S → E)).card • cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t) ≤
      ∑ t' ∈ univ.erase (0 : S → E), cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t') :=
    card_nsmul_le_sum _ _ _ fun t' ht' => fibre_le r hr t t' (ne_of_mem_erase ht')
  have h2 : ∑ t' ∈ univ.erase (0 : S → E), cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t') ≤
      ∑ t' : S → E, cnt (fun M : OntoMx E S Qo => mxApp M.1 r = t') :=
    sum_le_sum_of_subset (erase_subset _ _)
  rw [hcard, smul_eq_mul] at h1
  rw [mul_comm]
  exact h1.trans (h2.trans (le_of_eq hsum))

theorem ldPriv_mxErr_bound : Spec.ldPriv_mxErr_bound := by
  intro E S Qo _ _ _ _
  rcases Nat.eq_zero_or_pos (Fintype.card E ^ Fintype.card S - 1) with h0 | h0
  · rw [h0, mul_zero]
    exact Nat.zero_le _
  · have h := ldPriv_mxErr_le E S Qo (Fintype.card (OntoMx E S Qo) / (Fintype.card E ^ Fintype.card S - 1)) fun r t hr =>
      (Nat.le_div_iff_mul_le h0).mpr (ldPriv_fibre E S Qo r t hr)
    exact (Nat.le_div_iff_mul_le h0).mp h

theorem ldPriv_val_boot : Spec.ldPriv_val_boot := by
  intro E J₀ Qo _ _ _ _ Z _ ρ M a r
  funext s
  show ∑ n : J₀ ⊕ Qo, Sum.elim (Z.mat ρ s) (M.1 s) n * Sum.elim a r n = _
  rw [Fintype.sum_sum_type]
  rfl

theorem ldPriv_ok_boot : Spec.ldPriv_ok_boot := by
  intro E J₀ Qo _ _ _ _ Z _ hZ v hv
  have hv' : v = Sum.elim (fun j => v (Sum.inl j)) fun q => v (Sum.inr q) :=
    funext fun n => by cases n <;> rfl
  show cnt (fun x : Z.D × OntoMx E Z.S Qo => (Z.boot Qo).val x v = 0) ≤
    max (Z.err * Fintype.card (OntoMx E Z.S Qo)) (Fintype.card Z.D * mxErr E Z.S Qo)
  have hval : ∀ x : Z.D × OntoMx E Z.S Qo, (Z.boot Qo).val x v = 0 →
      Z.val x.1 (fun j => v (Sum.inl j)) + mxApp x.2.1 (fun q => v (Sum.inr q)) =
        0 := fun x hx => by
    rw [← ldPriv_val_boot E J₀ Qo Z x.1 x.2, ← hv']
    exact hx
  by_cases hr : (fun q => v (Sum.inr q)) = 0
  · have ha : (fun j => v (Sum.inl j)) ≠ 0 := fun h => hv (funext fun n => by
      cases n with
      | inl j => exact congrFun h j
      | inr q => exact congrFun hr q)
    refine le_trans ?_ (le_max_left _ _)
    refine (cnt_mono (Q := fun x : Z.D × OntoMx E Z.S Qo => Z.val x.1 (fun j => v (Sum.inl j)) = 0)
      fun x hx => ?_).trans ?_
    · have := hval x hx
      rwa [hr, mxApp_zero, add_zero] at this
    · rw [cnt_fst (D := OntoMx E Z.S Qo) fun ρ : Z.D => Z.val ρ (fun j => v (Sum.inl j)) = 0]
      exact Nat.mul_le_mul_right _ (hZ _ ha)
  · refine le_trans ?_ (le_max_right _ _)
    refine cnt_prod_le _ _ fun ρ =>
      (cnt_mono fun M hM => ?_).trans
        (ldPriv_le_mxErr E Z.S Qo _ (- Z.val ρ fun j => v (Sum.inl j)) hr)
    exact eq_neg_of_add_eq_zero_right (hval (ρ, M) hM)

theorem ldPriv_frac_boot : Spec.ldPriv_frac_boot := by
  intro E J₀ Qo _ _ _ Z _
  show max (Z.err * Fintype.card (OntoMx E Z.S Qo)) (Fintype.card Z.D * mxErr E Z.S Qo) *
      (Fintype.card E ^ Fintype.card Z.S - 1) ≤
    max (Z.err * (Fintype.card E ^ Fintype.card Z.S - 1)) (Fintype.card Z.D) *
      Fintype.card (OntoMx E Z.S Qo)
  have hA : Z.err * Fintype.card (OntoMx E Z.S Qo) * (Fintype.card E ^ Fintype.card Z.S - 1) ≤
      max (Z.err * (Fintype.card E ^ Fintype.card Z.S - 1)) (Fintype.card Z.D) *
        Fintype.card (OntoMx E Z.S Qo) := by
    rw [Nat.mul_right_comm]
    exact Nat.mul_le_mul_right _ (le_max_left _ _)
  have hB : Fintype.card Z.D * mxErr E Z.S Qo * (Fintype.card E ^ Fintype.card Z.S - 1) ≤
      max (Z.err * (Fintype.card E ^ Fintype.card Z.S - 1)) (Fintype.card Z.D) *
        Fintype.card (OntoMx E Z.S Qo) := by
    rw [Nat.mul_assoc]
    exact (Nat.mul_le_mul_left _ (ldPriv_mxErr_bound E Z.S Qo)).trans
      (Nat.mul_le_mul_right _ (le_max_right _ _))
  rcases le_total (Z.err * Fintype.card (OntoMx E Z.S Qo))
    (Fintype.card Z.D * mxErr E Z.S Qo) with h | h
  · rw [max_eq_right h]
    exact hB
  · rw [max_eq_left h]
    exact hA

theorem ldPriv_private_boot : Spec.ldPriv_private_boot := by
  intro E J₀ Qo _ _ _ _ Z _ x _ a
  have hfun : (fun c : Qo → E => (Z.boot Qo).val x (withPad (F := E) a c)) =
      fun c => Z.val x.1 a + mxApp x.2.1 c :=
    funext fun c => ldPriv_val_boot E J₀ Qo Z x.1 x.2 a c
  refine (congrArg (fun g => PMF.map g _) hfun).trans ?_
  exact map_affine_unif _ _ x.2.1 x.2.2 _

theorem ldPriv_sim_boot : Spec.ldPriv_sim_boot := by
  intro E J₀ Qo _ _ _ _ Z _
  exact ood_privateSim E E J₀ Qo (Z.boot Qo) (ldPriv_private_boot E J₀ Qo Z)

/-! ## The proofs of two statements of Cb/Ld/LdSwitch.lean -/

theorem ldSwitch_blind_of_private : Spec.ldSwitch_blind_of_private := by
  intro E J₀ Qo _ _ _ _ iQ Z good h ρ hρ v v'
  have hi : iQ = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst hi
  exact (h ρ hρ v).trans (h ρ hρ v').symm

/-- glue: the fibre of a pair (first component, function of both) over (ρ, y) has as many members as
the fibre of the function at ρ over y -/
theorem Ood.cnt_pair_fibre {D C Y : Type} [Fintype D] [Fintype C] (g : D → C → Y) (ρ : D) (y : Y) :
    cnt (fun x : D × C => (x.1, g x.1 x.2) = (ρ, y)) = cnt (fun c => g ρ c = y) := by
  rw [cnt_prod_eq_sum, sum_eq_single ρ]
  · exact cnt_congr fun c => ⟨fun h => (Prod.mk.inj h).2, fun h => by
      show (ρ, g ρ c) = (ρ, y)
      rw [h]⟩
  · intro ρ' _ hne
    exact cnt_false fun c hc => hne (Prod.mk.inj hc).1
  · intro h
    exact absurd (mem_univ _) h

theorem ldSwitch_blind_of_sim : Spec.ldSwitch_blind_of_sim := by
  intro E J₀ Qo _ _ _ _ iQ Z h ρ _ v v'
  have hi : iQ = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst hi
  classical
  obtain ⟨sim, hsim⟩ := h
  have h1 := (map_unif_eq_map_unif_iff _ _).mp ((hsim v).trans (hsim v').symm)
  refine (map_unif_eq_map_unif_iff _ _).mpr fun y => ?_
  have h2 := h1 (ρ, y)
  rw [cnt_pair_fibre (fun ρ c => Z.val ρ (withPad (F := E) v c)) ρ y,
    cnt_pair_fibre (fun ρ c => Z.val ρ (withPad (F := E) v' c)) ρ y] at h2
  have hpos : 0 < Fintype.card (Z.D × (Qo → E)) := Fintype.card_pos
  have h3 := Nat.eq_of_mul_eq_mul_right hpos h2
  exact congrArg (· * _) h3

end Cb
