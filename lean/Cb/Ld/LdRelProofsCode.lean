-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelProofsCode.lean: the proofs of the statements of Cb/Ld/LdRel.lean on codes read under a
transformation (rows of the generator; laws of interleavings, pairs and families; transparency of
interleavings, pairs and one code; Near of pairs; distance of pairs and interleavings; lists and
agreement of pairs and families), and the example of a statement with two witnesses
(Spec.ld_conL_two).
-/
import Cb.Ld.LdRel
import Prob.Count
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop

section
variable (E : Type) [Field E] (P : Type)

theorem ld_row_spec : Spec.ld_row_spec E P := by
  intro C h m r x α
  let L : ((C.J → E) × (C.Q → E)) →ₗ[E] (P → C.Aa → E) := (h.tLin.mk' _).comp (h.encLin.mk' _)
  have hm : (m, r) =
      ∑ j, m j • ((Pi.single j 1, 0) : (C.J → E) × (C.Q → E)) +
        ∑ q, r q • ((0, Pi.single q 1) : (C.J → E) × (C.Q → E)) := by
    refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  calc C.T (C.enc m r) x α = L (m, r) x α := rfl
    _ = L (∑ j, m j • ((Pi.single j 1, 0) : (C.J → E) × (C.Q → E)) +
            ∑ q, r q • ((0, Pi.single q 1) : (C.J → E) × (C.Q → E)))
          x α := by rw [← hm]
    _ = ∑ j, m j * L (Pi.single j 1, 0) x α + ∑ q, r q * L (0, Pi.single q 1) x α := by
        simp only [map_add, map_sum, map_smul, Pi.add_apply, Finset.sum_apply,
          Pi.smul_apply, smul_eq_mul]
    _ = _ := by
        congr 1 <;> exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem ld_laws_il : Spec.ld_laws_il E P := by
  intro C R _ _ h
  refine ⟨⟨fun a b => ?_, fun c a => ?_⟩, ⟨fun f g => ?_, fun c f => ?_⟩,
    fun m r h0 => ?_, fun f g x hfg => ?_⟩
  · funext p s
    exact congrFun
      (congrFun (h.encLin.map_add (fun j => a.1 (s.1, j), fun q => a.2 (s.1, q))
          (fun j => b.1 (s.1, j), fun q => b.2 (s.1, q))) p) s.2
  · funext p s
    exact congrFun
      (congrFun (h.encLin.map_smul c (fun j => a.1 (s.1, j), fun q => a.2 (s.1, q))) p) s.2
  · funext x α
    exact congrFun
      (congrFun (h.tLin.map_add (fun p s => f p (α.1, s)) (fun p s => g p (α.1, s))) x) α.2
  · funext x α
    exact congrFun (congrFun (h.tLin.map_smul c (fun p s => f p (α.1, s))) x) α.2
  · have hr : ∀ i, (fun j => m (i, j)) = 0 ∧ (fun q => r (i, q)) = 0 := fun i =>
      h.inj _ _ (funext fun p => funext fun s => congrFun (congrFun h0 p) (i, s))
    exact ⟨funext fun n => congrFun (hr n.1).1 n.2, funext fun n => congrFun (hr n.1).2 n.2⟩
  · funext α
    exact congrFun
      (h.loc (fun p s => f p (α.1, s)) (fun p s => g p (α.1, s)) x fun p hp =>
        funext fun s => congrFun (hfg p hp) (α.1, s)) α.2

theorem ld_laws_pair : Spec.ld_laws_pair E P := by
  intro C₁ C₂ h₁ h₂
  refine ⟨⟨fun a b => ?_, fun c a => ?_⟩, ⟨fun f g => ?_, fun c f => ?_⟩,
    fun m r h0 => ?_, fun f g x hfg => ?_⟩
  · funext p
    cases p with
    | inl p =>
      exact congrFun
        (h₁.encLin.map_add (fun j => a.1 (.inl j), fun q => a.2 (.inl q))
          (fun j => b.1 (.inl j), fun q => b.2 (.inl q))) p
    | inr p =>
      exact congrFun
        (h₂.encLin.map_add (fun j => a.1 (.inr j), fun q => a.2 (.inr q))
          (fun j => b.1 (.inr j), fun q => b.2 (.inr q))) p
  · funext p
    cases p with
    | inl p =>
      exact congrFun (h₁.encLin.map_smul c (fun j => a.1 (.inl j), fun q => a.2 (.inl q))) p
    | inr p =>
      exact congrFun (h₂.encLin.map_smul c (fun j => a.1 (.inr j), fun q => a.2 (.inr q))) p
  · funext x α
    cases α with
    | inl α =>
      exact congrFun (congrFun (h₁.tLin.map_add (fun p => f (.inl p)) (fun p => g (.inl p))) x) α
    | inr α =>
      exact congrFun (congrFun (h₂.tLin.map_add (fun p => f (.inr p)) (fun p => g (.inr p))) x) α
  · funext x α
    cases α with
    | inl α => exact congrFun (congrFun (h₁.tLin.map_smul c (fun p => f (.inl p))) x) α
    | inr α => exact congrFun (congrFun (h₂.tLin.map_smul c (fun p => f (.inr p))) x) α
  · have a₁ :=
      h₁.inj (fun j => m (.inl j)) (fun q => r (.inl q)) (funext fun p => congrFun h0 (.inl p))
    have a₂ :=
      h₂.inj (fun j => m (.inr j)) (fun q => r (.inr q)) (funext fun p => congrFun h0 (.inr p))
    refine ⟨funext fun n => ?_, funext fun n => ?_⟩
    · cases n with
      | inl j => exact congrFun a₁.1 j
      | inr j => exact congrFun a₂.1 j
    · cases n with
      | inl j => exact congrFun a₁.2 j
      | inr j => exact congrFun a₂.2 j
  · funext α
    cases α with
    | inl α =>
      exact congrFun
        (h₁.loc (fun p => f (.inl p)) (fun p => g (.inl p)) x fun p hp =>
          hfg (.inl p) (Finset.inl_mem_disjSum.2 hp)) α
    | inr α =>
      exact congrFun
        (h₂.loc (fun p => f (.inr p)) (fun p => g (.inr p)) x fun p hp =>
          hfg (.inr p) (Finset.inr_mem_disjSum.2 hp)) α

theorem ld_laws_fam : Spec.ld_laws_fam E P := by
  intro A _ _ C h
  refine ⟨⟨fun a b => ?_, fun c a => ?_⟩, ⟨fun f g => ?_, fun c f => ?_⟩,
    fun m r h0 => ?_, fun f g x hfg => ?_⟩
  · funext p
    exact congrFun
      ((h p.1).encLin.map_add (fun j => a.1 ⟨p.1, j⟩, fun q => a.2 ⟨p.1, q⟩)
        (fun j => b.1 ⟨p.1, j⟩, fun q => b.2 ⟨p.1, q⟩)) p.2
  · funext p
    exact congrFun ((h p.1).encLin.map_smul c (fun j => a.1 ⟨p.1, j⟩, fun q => a.2 ⟨p.1, q⟩)) p.2
  · funext x α
    exact congrFun
      (congrFun ((h α.1).tLin.map_add (fun p => f ⟨α.1, p⟩) (fun p => g ⟨α.1, p⟩)) x) α.2
  · funext x α
    exact congrFun (congrFun ((h α.1).tLin.map_smul c (fun p => f ⟨α.1, p⟩)) x) α.2
  · have hr : ∀ a, (fun j => m ⟨a, j⟩) = 0 ∧ (fun q => r ⟨a, q⟩) = 0 := fun a =>
      (h a).inj _ _ (funext fun p => congrFun h0 ⟨a, p⟩)
    exact ⟨funext fun n => congrFun (hr n.1).1 n.2, funext fun n => congrFun (hr n.1).2 n.2⟩
  · funext α
    exact congrFun
      ((h α.1).loc (fun p => f ⟨α.1, p⟩) (fun p => g ⟨α.1, p⟩) x fun p hp =>
        hfg ⟨α.1, p⟩ (Finset.mem_sigma.2 ⟨Finset.mem_univ _, hp⟩)) α.2

omit [Field E] in
theorem ld_transp_il : Spec.ld_transp_il E P := by
  intro C R _ _ ⟨bk, h⟩
  refine ⟨fun x g p s => bk x (fun α => g (s.1, α)) p s.2, fun m r x p hp => funext fun s => ?_⟩
  exact congrFun (h (fun j => m (s.1, j)) (fun q => r (s.1, q)) x p hp) s.2

omit [Field E] in
theorem ld_transp_pair : Spec.ld_transp_pair E P := by
  intro C₁ C₂ ⟨bk₁, h₁⟩ ⟨bk₂, h₂⟩
  refine ⟨fun x g p => match p with
    | .inl p => bk₁ x (fun α => g (.inl α)) p
    | .inr p => bk₂ x (fun α => g (.inr α)) p, fun m r x p hp => ?_⟩
  cases p with
  | inl p => exact h₁ (fun j => m (.inl j)) (fun q => r (.inl q)) x p (Finset.inl_mem_disjSum.1 hp)
  | inr p => exact h₂ (fun j => m (.inr j)) (fun q => r (.inr q)) x p (Finset.inr_mem_disjSum.1 hp)

theorem ld_transp_ofEnc : Spec.ld_transp_ofEnc E P := by
  intro F _ _ C₀ pos
  refine ⟨fun _ g _ _ => g (), fun m r x p hp => ?_⟩
  rw [Finset.mem_singleton.1 hp]

variable [Fintype P]

omit [Field E] in
theorem ld_near_pair : Spec.ld_near_pair E P := by
  intro C₁ C₂ e f g h
  exact ⟨le_trans (cnt_mono fun x hx hh => hx (funext fun α => congrFun hh (.inl α))) h,
    le_trans (cnt_mono fun x hx hh => hx (funext fun α => congrFun hh (.inr α))) h⟩

theorem ld_dist_pair : Spec.ld_dist_pair E P := by
  intro C₁ C₂ d h₁ h₂ m r hne
  by_cases a₁ : (fun j => m (.inl j)) = 0 ∧ (fun q => r (.inl q)) = 0
  · have a₂ : ¬ ((fun j => m (.inr j)) = 0 ∧ (fun q => r (.inr q)) = 0) := by
      intro a₂
      refine hne ⟨funext fun n => ?_, funext fun n => ?_⟩
      · cases n with
        | inl j => exact congrFun a₁.1 j
        | inr j => exact congrFun a₂.1 j
      · cases n with
        | inl j => exact congrFun a₁.2 j
        | inr j => exact congrFun a₂.2 j
    exact le_trans (h₂ _ _ a₂) (cnt_mono fun x hx hh => hx (funext fun α => congrFun hh (.inr α)))
  · exact le_trans (h₁ _ _ a₁) (cnt_mono fun x hx hh => hx (funext fun α => congrFun hh (.inl α)))

theorem ld_dist_il : Spec.ld_dist_il E P := by
  intro C R _ _ d h m r hne
  have : ∃ i, ¬ ((fun j => m (i, j)) = 0 ∧ (fun q => r (i, q)) = 0) := by
    by_contra hn
    have hn' : ∀ i, (fun j => m (i, j)) = 0 ∧ (fun q => r (i, q)) = 0 := fun i =>
      by_contra fun hi => hn ⟨i, hi⟩
    exact hne ⟨funext fun n => congrFun (hn' n.1).1 n.2, funext fun n => congrFun (hn' n.1).2 n.2⟩
  obtain ⟨i, hi⟩ := this
  exact le_trans (h _ _ hi) (cnt_mono fun x hx hh => hx (funext fun α => congrFun hh (i, α)))

omit [Field E] in
/-- Near, for a family: every component is near. -/
theorem near_fam {A : Type} [Fintype A] [DecidableEq A] (C : A → LdCode E P) (e : ℕ)
    (f g : (LdCode.fam C).Word) (h : (LdCode.fam C).Near e f g) (a : A) :
    (C a).Near e (fun p => f ⟨a, p⟩) (fun p => g ⟨a, p⟩) :=
  le_trans (cnt_mono fun _ hx hh => hx (funext fun α => congrFun hh ⟨a, α⟩)) h

omit [Field E] [Fintype P] in
/-- On the code, for a pair: on both sides. -/
theorem onCode_pair (C₁ C₂ : LdCode E P) (g : P → (C₁.pair C₂).Aa → E) (S : Finset P) :
    (C₁.pair C₂).OnCode g S ↔
    C₁.OnCode (fun x α => g x (.inl α)) S ∧ C₂.OnCode (fun x α => g x (.inr α)) S := by
  constructor
  · rintro ⟨m, r, h⟩
    exact ⟨⟨fun j => m (.inl j),
        fun q => r (.inl q),
        fun x hx => funext fun α => congrFun (h x hx) (.inl α)⟩,
      ⟨fun j => m (.inr j),
        fun q => r (.inr q),
        fun x hx => funext fun α => congrFun (h x hx) (.inr α)⟩⟩
  · rintro ⟨⟨m₁, r₁, h₁⟩, ⟨m₂, r₂, h₂⟩⟩
    refine ⟨Sum.elim m₁ m₂, Sum.elim r₁ r₂, fun x hx => funext fun α => ?_⟩
    cases α with
    | inl α => exact congrFun (h₁ x hx) α
    | inr α => exact congrFun (h₂ x hx) α

omit [Field E] [Fintype P] in
/-- On the code, for a family: in every component. -/
theorem onCode_fam {A : Type} [Fintype A] [DecidableEq A] (C : A → LdCode E P)
    (g : P → (LdCode.fam C).Aa → E) (S : Finset P) :
    (LdCode.fam C).OnCode g S ↔ ∀ a, (C a).OnCode (fun x α => g x ⟨a, α⟩) S := by
  constructor
  · rintro ⟨m, r, h⟩ a
    exact ⟨fun j => m ⟨a, j⟩,
      fun q => r ⟨a, q⟩,
      fun x hx => funext fun α => congrFun (h x hx) ⟨a, α⟩⟩
  · intro h
    choose m r hmr using h
    exact ⟨fun n => m n.1 n.2,
      fun n => r n.1 n.2,
      fun x hx => funext fun α => congrFun (hmr α.1 x hx) α.2⟩

variable [Finite E]

omit [Field E] in
theorem ld_list_pair : Spec.ld_list_pair E P := by
  intro C₁ C₂ e L₁ L₂ h₁ h₂ f
  let φ : {w : ((C₁.pair C₂).J → E) × ((C₁.pair C₂).Q → E) //
        (C₁.pair C₂).Near e f ((C₁.pair C₂).enc w.1 w.2)} →
      {w : (C₁.J → E) × (C₁.Q → E) // C₁.Near e (LdCode.fstW f) (C₁.enc w.1 w.2)} ×
        {w : (C₂.J → E) × (C₂.Q → E) // C₂.Near e (LdCode.sndW f) (C₂.enc w.1 w.2)} :=
    fun w =>
      (⟨(fun j => w.1.1 (.inl j), fun q => w.1.2 (.inl q)), (ld_near_pair E P C₁ C₂ e f _ w.2).1⟩,
        ⟨(fun j => w.1.1 (.inr j), fun q => w.1.2 (.inr q)), (ld_near_pair E P C₁ C₂ e f _ w.2).2⟩)
  have hφ : Function.Injective φ := by
    intro w w' h
    have a₁ := congrArg (fun z => z.1.1) h
    have a₂ := congrArg (fun z => z.2.1) h
    refine Subtype.ext (Prod.ext (funext fun n => ?_) (funext fun n => ?_))
    · cases n with
      | inl j => exact congrFun (congrArg Prod.fst a₁) j
      | inr j => exact congrFun (congrArg Prod.fst a₂) j
    · cases n with
      | inl j => exact congrFun (congrArg Prod.snd a₁) j
      | inr j => exact congrFun (congrArg Prod.snd a₂) j
  calc
    _ ≤ Nat.card ({w : (C₁.J → E) × (C₁.Q → E) // C₁.Near e (LdCode.fstW f) (C₁.enc w.1 w.2)} ×
            {w : (C₂.J → E) × (C₂.Q → E) // C₂.Near e (LdCode.sndW f) (C₂.enc w.1 w.2)}) :=
        Nat.card_le_card_of_injective φ hφ
    _ = _ := Nat.card_prod _ _
    _ ≤ L₁ * L₂ := Nat.mul_le_mul (h₁ _) (h₂ _)

omit [Field E] in
theorem ld_list_fam : Spec.ld_list_fam E P := by
  intro A _ _ C e L h f
  let φ : {w : ((LdCode.fam C).J → E) × ((LdCode.fam C).Q → E) //
        (LdCode.fam C).Near e f ((LdCode.fam C).enc w.1 w.2)} →
      ∀ a, {w : ((C a).J → E) × ((C a).Q → E) //
        (C a).Near e (fun p => f ⟨a, p⟩) ((C a).enc w.1 w.2)} :=
    fun w a => ⟨(fun j => w.1.1 ⟨a, j⟩, fun q => w.1.2 ⟨a, q⟩), near_fam E P C e f _ w.2 a⟩
  have hφ : Function.Injective φ := by
    intro w w' h
    have ha : ∀ a, (φ w a).1 = (φ w' a).1 := fun a => congrArg (fun z => (z a).1) h
    exact Subtype.ext
      (Prod.ext (funext fun n => congrFun (congrArg Prod.fst (ha n.1)) n.2)
        (funext fun n => congrFun (congrArg Prod.snd (ha n.1)) n.2))
  calc
    _ ≤ Nat.card (∀ a, {w : ((C a).J → E) × ((C a).Q → E) //
            (C a).Near e (fun p => f ⟨a, p⟩) ((C a).enc w.1 w.2)}) :=
        Nat.card_le_card_of_injective φ hφ
    _ = ∏ a, Nat.card
          {w : ((C a).J → E) × ((C a).Q → E) //
            (C a).Near e (fun p => f ⟨a, p⟩) ((C a).enc w.1 w.2)} := Nat.card_pi
    _ ≤ ∏ a, L a := Finset.prod_le_prod' fun a _ => h a _

theorem ld_mca_pair : Spec.ld_mca_pair E P := by
  intro C₁ C₂ e b₁ b₂ h₁ h₂ f₀ f₁
  cases nonempty_fintype E
  refine le_trans (cnt_le_add fun θ hθ => ?_)
    (Nat.add_le_add (h₁ (LdCode.fstW f₀) (LdCode.fstW f₁)) (h₂ (LdCode.sndW f₀) (LdCode.sndW f₁)))
  obtain ⟨S, hS, hl, hn⟩ := hθ
  have a := (onCode_pair E P C₁ C₂ _ S).1 hl
  by_cases c₁ : C₁.OnCode (C₁.T (LdCode.fstW f₀)) S ∧ C₁.OnCode (C₁.T (LdCode.fstW f₁)) S
  · refine Or.inr
      ⟨S, hS, a.2,
        fun c₂ =>
          hn ⟨(onCode_pair E P C₁ C₂ _ S).2 ⟨c₁.1, c₂.1⟩,
              (onCode_pair E P C₁ C₂ _ S).2 ⟨c₁.2, c₂.2⟩⟩⟩
  · exact Or.inl ⟨S, hS, a.1, c₁⟩

theorem ld_mca_fam : Spec.ld_mca_fam E P := by
  intro A _ _ C e b h f₀ f₁
  cases nonempty_fintype E
  refine le_trans
    (le_trans (cnt_mono fun θ hθ => ?_)
      (cnt_exists_le fun (a : A) (θ : E) =>
        ∃ S : Finset P,
          Fintype.card P ≤ S.card + e ∧
          (C a).OnCode ((C a).T (fun p => f₀ ⟨a, p⟩) + θ • (C a).T (fun p => f₁ ⟨a, p⟩)) S ∧
          ¬ ((C a).OnCode ((C a).T fun p => f₀ ⟨a, p⟩) S ∧
            (C a).OnCode ((C a).T fun p => f₁ ⟨a, p⟩) S)))
    (Finset.sum_le_sum fun a _ => h a _ _)
  obtain ⟨S, hS, hl, hn⟩ := hθ
  have a := (onCode_fam E P C _ S).1 hl
  by_contra hc
  have hall : ∀ a,
      (C a).OnCode ((C a).T fun p => f₀ ⟨a, p⟩) S ∧ (C a).OnCode ((C a).T fun p => f₁ ⟨a, p⟩) S :=
    fun i => by_contra fun hi => hc ⟨i, S, hS, a i, hi⟩
  exact hn
    ⟨(onCode_fam E P C _ S).2 fun i => (hall i).1, (onCode_fam E P C _ S).2 fun i => (hall i).2⟩

end

/-! ## A statement with two witnesses -/

/-- The code of length two that repeats its one symbol, read as it stands. -/
@[reducible] def twoCode (E : Type) : LdCode E Bool where
  NP := Bool
  NS := fun _ => Unit
  J := Unit
  Q := Empty
  enc := fun m _ _ _ => m ()
  Aa := Unit
  T := fun f x _ => f x ()
  src := fun x => {x}

theorem ld_conL_two : Spec.ld_conL_two := by
  refine ⟨ZMod 2, Bool, inferInstance, inferInstance, inferInstance,
    twoCode (ZMod 2), 2, 1, (0, ()), fun p _ => if p then 1 else 0, (0, 0),
    (fun _ => 1, 0), ?_, ?_, by norm_num, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine ⟨⟨fun _ _ => rfl, fun _ _ => rfl⟩,
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩,
      fun m r h => ⟨funext fun _ => congrFun (congrFun h true) (), funext fun q => q.elim⟩,
      fun f g x h => funext fun _ => congrFun (h x (Finset.mem_singleton_self x)) ()⟩
  · intro m r hne
    have hm : m () ≠ 0 := fun h0 => hne ⟨funext fun _ => h0, funext fun q => q.elim⟩
    have := card_le_cnt
      (P := fun x : Bool => (twoCode (ZMod 2)).T ((twoCode (ZMod 2)).enc m r) x ≠ 0)
      Finset.univ fun x _ h => hm (congrFun h ())
    simpa using this
  · intro h
    exact zero_ne_one (congrFun h ())
  · refine cnt_le_one fun a b ha hb => ?_
    cases a
    · exact absurd rfl ha
    · cases b
      · exact absurd rfl hb
      · rfl
  · simp [Slf.Holds, Slf.zero]
  · refine cnt_le_one fun a b ha hb => ?_
    cases a
    · cases b
      · rfl
      · exact absurd rfl hb
    · exact absurd rfl ha
  · simp [Slf.Holds, Slf.zero]

end Cb
