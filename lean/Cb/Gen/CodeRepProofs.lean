-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/CodeRepProofs.lean: the proofs of the statements of Cb/Gen/CodeRep.lean. Nothing is assumed
beyond the hypotheses of the statements and whatever the arguments hold as proofs.

All lemmas for an even reading use one count (`cnt_comp_even`): if every position of a component is
read exactly m times, then a set Q of its positions is read at exactly m |Q| long positions.
  Projection of a decoding (`decodesTo_comp'`): the long positions at which the component a is off
    are among those at which the group is off.
  Projection of a set S of long positions (`image_large`): a position of a that is read at no
    element of S has all its m long positions outside S; so the image of S omits at most
    (what S omits) / m positions.
  Agreement: all components agree with codewords on S if and only if each does on the image of S
    (`onCode_iff`); an exceptional θ of the group is exceptional for some component, on the image of
    the same S.
-/
import Mathlib.Logic.Equiv.Fin.Basic
import Cb.Gen.CodeRep
import Cb.Gen.CodeListRows

set_option autoImplicit false

namespace Cb
open Prob Blocks

namespace CodeRep

/-- If every value of g is taken exactly m times, a set Q of values is hit exactly m |Q| times. -/
theorem cnt_comp_even {P Y : Type} [Fintype P] [Fintype Y] (g : P → Y) (m : ℕ)
    (h : ∀ y, cnt (fun x => g x = y) = m) (Q : Y → Prop) :
    cnt (fun x => Q (g x)) = m * cnt Q := by
  classical
  rw [cnt_eq_card_filter, cnt_eq_card_filter]
  have h1 : (Finset.univ.filter fun x => Q (g x)).card =
      ∑ y ∈ Finset.univ.filter Q, (Finset.univ.filter fun x => g x = y).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := g) (t := Finset.univ.filter Q)
        (fun x hx =>
          Finset.mem_coe.mpr
            (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, (Finset.mem_filter.mp (Finset.mem_coe.mp hx)).2⟩))]
    refine Finset.sum_congr rfl fun y hy => congrArg Finset.card (Finset.ext fun x => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun hx => hx.2, fun hx => ⟨by rw [hx]; exact (Finset.mem_filter.mp hy).2, hx⟩⟩
  have h2 : ∀ y ∈ Finset.univ.filter Q,
      (Finset.univ.filter fun x => g x = y).card = m := fun y _ => by
    rw [← cnt_eq_card_filter]
    exact h y
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]

/-- Among the numbers below m n, exactly m leave the remainder y on division by n. -/
theorem cnt_mod_mul (m n : ℕ) (y : Fin n) : cnt (fun x : Fin (m * n) => x.val % n = y.val) = m := by
  rw [← cnt_equiv finProdFinEquiv (fun x : Fin (m * n) => x.val % n = y.val)]
  have h : ∀ c : Fin m × Fin n, ((finProdFinEquiv c).val % n = y.val) ↔ c.2 = y := by
    intro c
    rw [finProdFinEquiv_apply_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt c.2.2]
    exact Fin.ext_iff.symm
  rw [cnt_congr h, cnt_snd (C := Fin m) (fun b : Fin n => b = y), cnt_eq_const,
    Fintype.card_fin, Nat.mul_one]

theorem cnt_mod {N n : ℕ} (h : n ∣ N) (y : Fin n) :
    cnt (fun x : Fin N => x.val % n = y.val) = N / n := by
  obtain ⟨m, rfl⟩ := exists_eq_mul_left_of_dvd h
  rw [Nat.mul_div_cancel m y.pos]
  exact cnt_mod_mul m n y

section
variable {F A : Type} [Field F] {C : A → Code.Enc F} {T : Reading C} {E : Type} [Field E]
  [Algebra F E] {R : A → Type}

theorem decodesTo_comp' (hT : T.Even) {e : ℕ} {f : ∀ a, R a → Fin (C a).n → E}
    {M : ∀ a, R a → Fin (C a).k → E} (h : T.DecodesTo E e f M) (a : A) :
    DecodesTo ((C a).GE E) (e / T.mult a) (f a) (M a) := by
  unfold DecodesTo
  rw [Nat.le_div_iff_mul_le (hT a).1, mul_comm, ← cnt_comp_even (T.pos a) (T.mult a) (hT a).2]
  exact (cnt_mono fun x hx => ⟨a, hx⟩).trans h

theorem onCode_iff (f : ∀ a, R a → Fin (C a).n → E) (S : Finset T.P) :
    T.OnCode E f S ↔ ∀ a, (C a).OnCode E (f a) (S.image (T.pos a)) := by
  constructor
  · rintro ⟨M, h⟩ a
    refine ⟨M a, fun j hj r => ?_⟩
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
    exact h x hx a r
  · intro h
    choose M hM using h
    exact ⟨M, fun x hx a r => hM a _ (Finset.mem_image_of_mem _ hx) r⟩

omit [Field F] in
theorem image_large (hT : T.Even) {e : ℕ} {S : Finset T.P}
    (hS : Fintype.card T.P ≤ S.card + e) (a : A) :
    (C a).n ≤ (S.image (T.pos a)).card + e / T.mult a := by
  have h1 := cnt_comp_even (T.pos a) (T.mult a) (hT a).2 (fun y => ¬ y ∈ S.image (T.pos a))
  have h2 := cnt_add_card_le (P := fun x => ¬ T.pos a x ∈ S.image (T.pos a)) (S := S)
    (fun x hx hc => hc (Finset.mem_image_of_mem _ hx))
  have h3 : cnt (fun y => ¬ y ∈ S.image (T.pos a)) ≤ e / T.mult a := by
    rw [Nat.le_div_iff_mul_le (hT a).1, mul_comm, ← h1]
    omega
  have h4 := cnt_add_cnt_not (fun y => y ∈ S.image (T.pos a))
  have h5 : cnt (fun y => y ∈ S.image (T.pos a)) ≤ (S.image (T.pos a)).card :=
    cnt_le_of_forall_finset fun Y hY => Finset.card_le_card hY
  rw [Fintype.card_fin] at h4
  omega

theorem dist_under' (hT : T.Even) (hd : ∀ a, HasDist (C a).G (C a).d) {D : ℕ}
    (hD : ∀ a, D ≤ T.mult a * (C a).d) {M M' : ∀ a, R a → Fin (C a).k → E} (hne : M ≠ M') :
    D ≤ cnt fun x =>
        ∃ a r,
            ((C a).GE E).mulVec (M a r) (T.pos a x) ≠ ((C a).GE E).mulVec (M' a r) (T.pos a x) := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
  obtain ⟨r, hr⟩ := Function.ne_iff.mp ha
  have h1 := (HasDist.map (E := E) (hd a)).le_cnt_ne hr
  have h2 := cnt_comp_even (T.pos a) (T.mult a) (hT a).2
    (fun j => ((C a).GE E).mulVec (M a r) j ≠ ((C a).GE E).mulVec (M' a r) j)
  calc D ≤ T.mult a * (C a).d := hD a
    _ ≤ T.mult a * cnt (fun j => ((C a).GE E).mulVec (M a r) j ≠ ((C a).GE E).mulVec (M' a r) j) :=
      Nat.mul_le_mul_left _ h1
    _ = cnt (fun x =>
          ((C a).GE E).mulVec (M a r) (T.pos a x) ≠ ((C a).GE E).mulVec (M' a r) (T.pos a x)) :=
      h2.symm
    _ ≤ _ := cnt_mono fun x hx => ⟨a, r, hx⟩

end
end CodeRep

open CodeRep CodeListRows

theorem one_even : Spec.one_even := fun _ _ _ => ⟨Nat.one_pos, fun y => cnt_eq_const y⟩

theorem rep_even : Spec.rep_even := by
  intro F A C N h hN a
  refine ⟨Nat.div_pos (Nat.le_of_dvd hN (h a)) (Nat.pos_of_dvd_of_pos (h a) hN), fun y => ?_⟩
  refine Eq.trans (cnt_congr fun x => ?_) (cnt_mod (h a) y)
  exact Fin.ext_iff

section
variable (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]

theorem one_decodesTo : Spec.one_decodesTo F E := by
  intro C₀ R₀ e f M
  have h : ∀ x,
      (Reading.one C₀).Off E (R := fun _ => R₀) (fun _ => f) (fun _ => M) x ↔ Off (C₀.GE E) f M x :=
    fun x => ⟨fun ⟨_, h⟩ => h, fun h => ⟨(), h⟩⟩
  exact Eq.to_iff (congrArg (fun c => c ≤ e) (cnt_congr h))

theorem one_onCode : Spec.one_onCode F E := fun _ _ _ _ =>
  ⟨fun ⟨M, h⟩ => ⟨M (), fun j hj r => h j hj () r⟩,
    fun ⟨M, h⟩ => ⟨fun _ => M, fun j hj _ r => h j hj r⟩⟩

theorem one_listAt [Finite E] : Spec.one_listAt F E := by
  intro C₀ R₀ _ e L
  constructor
  · intro h f
    refine le_trans
      (cnt_le_cnt_of_injective (fun (M : R₀ → Fin C₀.k → E) (_ : Unit) => M)
        (fun _ _ hab => congrFun hab ()) ?_) (h fun _ => f)
    exact fun M hM => (one_decodesTo F E C₀ R₀ e f M).mpr hM
  · intro h f
    refine le_trans
      (cnt_le_cnt_of_injective (fun (M : Unit → R₀ → Fin C₀.k → E) => M ())
        (fun _ _ hab => funext fun _ => hab) ?_) (h (f ()))
    exact fun M hM => (one_decodesTo F E C₀ R₀ e (f ()) (M ())).mp hM

theorem one_mcaAt [Finite E] : Spec.one_mcaAt F E := by
  intro C₀ R₀ _ e bad
  have key : ∀ (f₀ f₁ : R₀ → Fin C₀.n → E) (θ : E),
      (∃ S : Finset (Reading.one C₀).P,
        Fintype.card (Reading.one C₀).P ≤ S.card + e ∧
        (Reading.one C₀).OnCode E (R := fun _ => R₀) (fun _ r j => f₀ r j + θ * f₁ r j) S ∧
        ¬ ((Reading.one C₀).OnCode E (R := fun _ => R₀) (fun _ => f₀) S ∧
          (Reading.one C₀).OnCode E (R := fun _ => R₀) (fun _ => f₁) S)) ↔
      (∃ S : Finset (Fin C₀.n),
        C₀.n ≤ S.card + e ∧
        C₀.OnCode E (fun r j => f₀ r j + θ * f₁ r j) S ∧
        ¬ (C₀.OnCode E f₀ S ∧ C₀.OnCode E f₁ S)) := by
    intro f₀ f₁ θ
    refine exists_congr fun S => ?_
    rw [one_onCode F E C₀ R₀, one_onCode F E C₀ R₀, one_onCode F E C₀ R₀]
    have hc : Fintype.card (Reading.one C₀).P = C₀.n := Fintype.card_fin _
    rw [hc]
    exact Iff.rfl
  constructor
  · intro h f₀ f₁
    rw [← cnt_congr (key f₀ f₁)]
    exact h (fun _ => f₀) (fun _ => f₁)
  · intro h f₀ f₁
    exact (le_of_eq (cnt_congr (key (f₀ ()) (f₁ ())))).trans (h (f₀ ()) (f₁ ()))

theorem decodesTo_comp : Spec.decodesTo_comp F E := fun _ _ _ hT _ _ _ _ h a =>
  decodesTo_comp' hT h a

theorem list_le_prod [Finite E] : Spec.list_le_prod F E := by
  intro A _ C T hT R _ e L hL f
  classical
  cases nonempty_fintype E
  haveI : ∀ a, Fintype (R a) := fun a => Fintype.ofFinite (R a)
  calc
    cnt (fun M : ∀ a, R a → Fin (C a).k → E => T.DecodesTo E e f M) ≤
        cnt (fun M : ∀ a,
          R a → Fin (C a).k → E => ∀ a, DecodesTo ((C a).GE E) (e / T.mult a) (f a) (M a)) :=
        cnt_mono fun M h a => decodesTo_comp' hT h a
    _ = ∏ a,
          cnt (fun Ma : R a → Fin (C a).k → E => DecodesTo ((C a).GE E) (e / T.mult a) (f a) Ma) :=
        cnt_forall_pi fun a (Ma : R a → Fin (C a).k → E) =>
          DecodesTo ((C a).GE E) (e / T.mult a) (f a) Ma
    _ ≤ ∏ a, L a := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) fun a _ => hL a (f a)

theorem mca_le_sum [Finite E] : Spec.mca_le_sum F E := by
  intro A _ C T hT R _ e bad h f₀ f₁
  cases nonempty_fintype E
  refine le_trans (cnt_mono ?_)
    ((cnt_exists_le fun (a : A) (θ : E) =>
        ∃ S : Finset (Fin (C a).n),
          (C a).n ≤ S.card + e / T.mult a ∧
          (C a).OnCode E (fun r j => f₀ a r j + θ * f₁ a r j) S ∧
          ¬ ((C a).OnCode E (f₀ a) S ∧ (C a).OnCode E (f₁ a) S)).trans
      (Finset.sum_le_sum fun a _ => h a (f₀ a) (f₁ a)))
  rintro θ ⟨S, hS, h1, h2⟩
  by_contra hno
  have key : ∀ a,
      (C a).OnCode E (f₀ a) (S.image (T.pos a)) ∧
      (C a).OnCode E (f₁ a) (S.image (T.pos a)) := fun a =>
    by_contra fun hc =>
      hno ⟨a, S.image (T.pos a), image_large hT hS a, (onCode_iff _ S).mp h1 a, hc⟩
  exact h2 ⟨(onCode_iff f₀ S).mpr fun a => (key a).1, (onCode_iff f₁ S).mpr fun a => (key a).2⟩

theorem dist_under : Spec.dist_under F E := fun _ _ _ hT hd _ hD _ _ _ hne =>
  dist_under' hT hd hD hne

theorem list_le_johnson [Finite E] : Spec.list_le_johnson F E := by
  intro A _ C T hT hd D hD e hJ R _ f
  refine cnt_le_of_forall_finset fun Y hY => ?_
  refine JohnsonList.family_aux (I := ∀ a, R a → Fin (C a).k → E) (A := ∀ a, R a → E)
    (fun M x a r => ((C a).GE E).mulVec (M a r) (T.pos a x)) D e hJ
    (fun x a r => f a r (T.pos a x)) Y ?_ ?_
  · intro M _ M' _ hne
    exact (dist_under' hT hd hD hne).trans
      (cnt_mono fun x ⟨a, r, hx⟩ heq => hx (congrFun (congrFun heq a) r))
  · intro M hM
    refine le_trans (cnt_mono fun x hx => ?_) (hY M hM)
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hx
    obtain ⟨r, hr⟩ := Function.ne_iff.mp ha
    exact ⟨a, r, fun h => hr h.symm⟩

theorem prox_of_comps [Finite E] : Spec.prox_of_comps F E := fun A _ C T hT R _ _ _ _ h =>
  { list := fun e he => list_le_prod F E A C T hT R e _ fun a => (h a).list _ (he a) (R a)
    mca := fun e he => mca_le_sum F E A C T hT R e _ fun a => (h a).mca _ (he a) (R a) }

theorem prox_johnson_of_comps [Finite E] :
    Spec.prox_johnson_of_comps F E := fun A _ C T hT hd D hD R _ _ _ _ h =>
  { list := fun e he => list_le_johnson F E A C T hT hd D hD e he.1 R
    mca := fun e he => mca_le_sum F E A C T hT R e _ fun a => (h a).mca _ (he.2 a) (R a) }

end
end Cb
