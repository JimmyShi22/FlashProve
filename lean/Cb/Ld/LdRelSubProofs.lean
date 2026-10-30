-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelSubProofs.lean: the proofs of the statements of Cb/Ld/LdRelSub.lean (agreement of a
subcode: at most that of the whole code plus the list of two rows of the whole code, under the
hypotheses of `Spec.ld_sub_mca`).

A count used in the proof:
  `cnt_le_of_rel`: the a that have a partner b with Q are no more than the b with Q, if no b is the
    partner of two (`h2`).
-/
import Cb.Ld.LdRelSub
import Cb.Ld.LdRelRowsProofs
import Mathlib.Tactic.Module

set_option autoImplicit false

namespace Cb
open Prob

theorem cnt_le_of_rel {α β : Type} [Finite α] [Finite β] (Q : β → Prop) (Rel : α → β → Prop)
    (h2 : ∀ a a' b, Rel a b → Rel a' b → a = a') :
    cnt (fun a => ∃ b, Q b ∧ Rel a b) ≤ cnt Q := by
  classical
  choose g hg using fun x : {a // ∃ b, Q b ∧ Rel a b} => x.2
  refine Nat.card_le_card_of_injective (fun x => (⟨g x, (hg x).1⟩ : {b // Q b}))
    fun x y hxy => Subtype.ext (h2 _ _ (g x) (hg x).2 ?_)
  have e : g x = g y := congrArg Subtype.val hxy
  rw [e]
  exact (hg y).2

namespace LdCode
variable {E P : Type} [Field E]

/-- the transformed codeword of (message, randomness) -/
def cw (C : LdCode E P) (w : (C.J → E) × (C.Q → E)) : P → C.Aa → E := C.T (C.enc w.1 w.2)

theorem cw_lin {C : LdCode E P} (hL : C.Laws) (a b : E) (w₁ w₂ : (C.J → E) × (C.Q → E)) :
    C.cw (a • w₁ + b • w₂) = a • C.cw w₁ + b • C.cw w₂ := by
  have e : C.enc (a • w₁ + b • w₂).1 (a • w₁ + b • w₂).2 =
      a • C.enc w₁.1 w₁.2 + b • C.enc w₂.1 w₂.2 := by
    rw [hL.encLin.map_add, hL.encLin.map_smul, hL.encLin.map_smul]
  unfold cw
  rw [e, hL.tLin.map_add, hL.tLin.map_smul, hL.tLin.map_smul]

/-- Under `hL` and `hD`: two transformed codewords that agree off fewer positions than the distance
are one. -/
theorem cw_eq_of_on [Fintype P] {C : LdCode E P} (hL : C.Laws) {d e : ℕ} (hD : C.Dist d)
    (he : e < d) (S : Finset P) (hS : Fintype.card P ≤ S.card + e)
    (w w' : (C.J → E) × (C.Q → E)) (h : ∀ x ∈ S, C.cw w x = C.cw w' x) : C.cw w = C.cw w' := by
  by_contra hne
  have e1 : C.cw ((1 : E) • w + (-1 : E) • w') = (1 : E) • C.cw w + (-1 : E) • C.cw w' :=
    cw_lin hL 1 (-1) w w'
  have hz : ¬ (((1 : E) • w + (-1 : E) • w').1 = 0 ∧ ((1 : E) • w + (-1 : E) • w').2 = 0) := by
    intro h0
    have z0 : (1 : E) • w + (-1 : E) • w' = 0 := Prod.ext h0.1 h0.2
    have z1 : w = w' := by
      have : w - w' = 0 := by rw [← z0]; module
      exact sub_eq_zero.1 this
    exact hne (by rw [z1])
  have hd := hD _ _ hz
  have hv : ∀ x ∈ S,
      ¬ (C.T (C.enc ((1 : E) • w + (-1 : E) • w').1 ((1 : E) • w + (-1 : E) • w').2) x ≠ 0) := by
    intro x hx
    refine not_not.2 ?_
    show C.cw ((1 : E) • w + (-1 : E) • w') x = 0
    rw [e1]
    show (1 : E) • C.cw w x + (-1 : E) • C.cw w' x = 0
    rw [h x hx]
    module
  have hcard := cnt_add_card_le hv
  omega

/-- g, read through φ, is a transformed codeword of C' -/
def InS (C' : LdCode E P) {A : Type} (φ : C'.Aa → A) (g : P → A → E) : Prop :=
  ∃ w', ∀ x α, C'.cw w' x α = g x (φ α)

theorem inS_lin {C' : LdCode E P} (hL' : C'.Laws) {A : Type} (φ : C'.Aa → A)
    (a b : E) (g₁ g₂ : P → A → E) :
    C'.InS φ g₁ → C'.InS φ g₂ → C'.InS φ (a • g₁ + b • g₂) := by
  rintro ⟨w₁, e₁⟩ ⟨w₂, e₂⟩
  refine ⟨a • w₁ + b • w₂, fun x α => ?_⟩
  rw [cw_lin hL']
  show a • C'.cw w₁ x α + b • C'.cw w₂ x α = a • g₁ x (φ α) + b • g₂ x (φ α)
  rw [e₁, e₂]

/-- Under `hL'`: for one pair (c₀, c₁), not both in the subcode, c₀ + θ c₁ lies in the subcode for
at most one θ. -/
theorem inS_one {C' : LdCode E P} (hL' : C'.Laws) {A : Type} (φ : C'.Aa → A)
    (c₀ c₁ : P → A → E) (θ θ' : E) (a1 : C'.InS φ (c₀ + θ • c₁))
    (a2 : C'.InS φ (c₀ + θ' • c₁)) (n1 : ¬ (C'.InS φ c₀ ∧ C'.InS φ c₁)) : θ = θ' := by
  by_contra hne
  have hne' : θ - θ' ≠ 0 := sub_ne_zero.2 hne
  have hc1 : C'.InS φ c₁ := by
    have h := inS_lin hL' φ (θ - θ')⁻¹ (-(θ - θ')⁻¹) _ _ a1 a2
    have e1 : (θ - θ')⁻¹ • (c₀ + θ • c₁) + (-(θ - θ')⁻¹) • (c₀ + θ' • c₁) =
        ((θ - θ')⁻¹ * (θ - θ')) • c₁ := by module
    rw [e1, inv_mul_cancel₀ hne', one_smul] at h
    exact h
  have hc0 : C'.InS φ c₀ := by
    have h := inS_lin hL' φ 1 (-θ) _ _ a1 hc1
    have e1 : (1 : E) • (c₀ + θ • c₁) + (-θ) • c₁ = c₀ := by module
    rw [e1] at h
    exact h
  exact n1 ⟨hc0, hc1⟩

/-- a row of a pair (message, randomness) of two rows; two rows from two pairs -/
def row2 (C : LdCode E P) (b : Bool) (w : ((C.il Bool).J → E) × ((C.il Bool).Q → E)) :
    (C.J → E) × (C.Q → E) :=
  (fun j => w.1 (b, j), fun q => w.2 (b, q))
def two (C : LdCode E P) (w₀ w₁ : (C.J → E) × (C.Q → E)) :
    ((C.il Bool).J → E) × ((C.il Bool).Q → E) :=
  (fun j => if j.1 then w₁.1 j.2 else w₀.1 j.2, fun q => if q.1 then w₁.2 q.2 else w₀.2 q.2)
def twoW (C : LdCode E P) (f₀ f₁ : C.Word) : (C.il Bool).Word := fun p s =>
  if s.1 then f₁ p s.2 else f₀ p s.2

omit [Field E] in
/-- two words that agree on S with two codewords: the word of two rows is within e long positions of
the codeword of two rows, if S leaves out at most e (`hS`). -/
theorem two_near [Fintype P] (C : LdCode E P) (e : ℕ) (S : Finset P)
    (hS : Fintype.card P ≤ S.card + e) (f₀ f₁ : C.Word) (w₀ w₁ : (C.J → E) × (C.Q → E))
    (a₀ : ∀ x ∈ S, C.T f₀ x = C.cw w₀ x) (a₁ : ∀ x ∈ S, C.T f₁ x = C.cw w₁ x) :
    (C.il Bool).Near e (C.twoW f₀ f₁) ((C.il Bool).enc (C.two w₀ w₁).1 (C.two w₀ w₁).2) := by
  have hz : ∀ x ∈ S, ¬ ((C.il Bool).T (C.twoW f₀ f₁) x ≠
      (C.il Bool).T ((C.il Bool).enc (C.two w₀ w₁).1 (C.two w₀ w₁).2) x) := by
    intro x hx
    refine not_not.2 (funext fun α => ?_)
    obtain ⟨b, α⟩ := α
    cases b
    · exact congrFun (a₀ x hx) α
    · exact congrFun (a₁ x hx) α
  have hcard := cnt_add_card_le hz
  show cnt _ ≤ e
  omega

end LdCode

section
variable (E P : Type) [Field E] [Finite E] [Fintype P]

theorem ld_sub_mca : Spec.ld_sub_mca E P := by
  classical
  intro C C' φ d e bad L2 hS hL hL' hD he hm hl f₀' f₁'
  cases nonempty_fintype E
  obtain ⟨f₀, h₀⟩ := hS.word f₀'
  obtain ⟨f₁, h₁⟩ := hS.word f₁'
  refine (cnt_le_add
      (Q := fun θ =>
          ∃ S : Finset P,
            Fintype.card P ≤ S.card + e ∧
            C.OnCode (C.T f₀ + θ • C.T f₁) S ∧
            ¬ (C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S))
      (R := fun θ =>
          ∃ w,
            (C.il Bool).Near e (C.twoW f₀ f₁) ((C.il Bool).enc w.1 w.2) ∧
            (C'.InS φ (C.cw (C.row2 false w) + θ • C.cw (C.row2 true w)) ∧
              ¬ (C'.InS φ (C.cw (C.row2 false w)) ∧ C'.InS φ (C.cw (C.row2 true w))))) ?_).trans
    (add_le_add (hm f₀ f₁)
      ((cnt_le_of_rel (fun w => (C.il Bool).Near e (C.twoW f₀ f₁) ((C.il Bool).enc w.1 w.2))
          (fun θ w =>
            C'.InS φ (C.cw (C.row2 false w) + θ • C.cw (C.row2 true w)) ∧
            ¬ (C'.InS φ (C.cw (C.row2 false w)) ∧ C'.InS φ (C.cw (C.row2 true w))))
          (fun θ θ' w r1 r2 => LdCode.inS_one hL' φ _ _ θ θ' r1.1 r2.1 r1.2)).trans
        (hl (C.twoW f₀ f₁))))
  rintro θ ⟨S, hS', ⟨m', r', hc⟩, hn⟩
  by_cases hb : ∃ S : Finset P,
    Fintype.card P ≤ S.card + e ∧
    C.OnCode (C.T f₀ + θ • C.T f₁) S ∧
    ¬ (C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S)
  · exact Or.inl hb
  right
  obtain ⟨m, r, hmr⟩ := hS.code m' r'
  have o1 : ∀ x ∈ S, C.T f₀ x + θ • C.T f₁ x = C.T (C.enc m r) x := by
    intro x hx
    funext β
    obtain ⟨α, rfl⟩ := hS.onto β
    have e1 : C'.T f₀' x α + θ • C'.T f₁' x α = C'.T (C'.enc m' r') x α := congrFun (hc x hx) α
    show C.T f₀ x (φ α) + θ • C.T f₁ x (φ α) = C.T (C.enc m r) x (φ α)
    rw [← h₀, ← h₁, ← hmr]
    exact e1
  have both : C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S := by
    by_contra hnb
    exact hb ⟨S, hS', ⟨m, r, o1⟩, hnb⟩
  obtain ⟨⟨m₀, r₀, a₀⟩, ⟨m₁, r₁, a₁⟩⟩ := both
  have key : C.cw (m, r) = C.cw (m₀, r₀) + θ • C.cw (m₁, r₁) := by
    have k1 : C.cw (m, r) = C.cw ((1 : E) • (m₀, r₀) + θ • (m₁, r₁)) := by
      refine LdCode.cw_eq_of_on hL hD he S hS' _ _ fun x hx => ?_
      rw [LdCode.cw_lin hL]
      show C.T (C.enc m r) x = (1 : E) • C.T (C.enc m₀ r₀) x + θ • C.T (C.enc m₁ r₁) x
      rw [← a₀ x hx, ← a₁ x hx, one_smul, o1 x hx]
    rw [k1, LdCode.cw_lin hL, one_smul]
  refine ⟨C.two (m₀, r₀) (m₁, r₁),
    LdCode.two_near C e S hS' f₀ f₁ (m₀, r₀) (m₁, r₁) a₀ a₁,
    ⟨(m', r'), fun x α => ?_⟩,
    ?_⟩
  · show C'.T (C'.enc m' r') x α = (C.cw (m₀, r₀) + θ • C.cw (m₁, r₁)) x (φ α)
    rw [← key]
    exact hmr x α
  · rintro ⟨⟨w₀', e₀⟩, ⟨w₁', e₁⟩⟩
    refine hn ⟨⟨w₀'.1, w₀'.2, fun x hx => funext fun α => ?_⟩,
        ⟨w₁'.1, w₁'.2, fun x hx => funext fun α => ?_⟩⟩
    · rw [h₀, a₀ x hx]
      exact (e₀ x α).symm
    · rw [h₁, a₁ x hx]
      exact (e₁ x α).symm

omit [Field E] [Finite E] [Fintype P] in
theorem ld_sub_il : Spec.ld_sub_il E P := fun C C' φ R _ _ h =>
  { onto := fun β => by
      obtain ⟨α, hα⟩ := h.onto β.2
      exact ⟨(β.1, α), Prod.ext rfl hα⟩
    word := fun f' => by
      choose g hg using fun i : R => h.word fun p s => f' p (i, s)
      exact ⟨fun p s => g s.1 p s.2, fun x α => hg α.1 x α.2⟩
    code := fun m' r' => by
      choose gm gr hg using fun i : R => h.code (fun j => m' (i, j)) fun q => r' (i, q)
      exact ⟨fun j => gm j.1 j.2, fun q => gr q.1 q.2, fun x α => hg α.1 x α.2⟩ }

theorem ld_sub_rows : Spec.ld_sub_rows E P := fun C C' φ d e bad L2 h hL hL' hD he hm hl R _ _ =>
  ld_sub_mca E P (C.il R) (C'.il R) _ d e bad L2 (ld_sub_il E P C C' φ R h) (ld_laws_il E P C R hL)
    (ld_laws_il E P C' R hL') (ld_dist_il E P C R d hD) he (hm R) (hl R)

end

/-- the full input of the generator does not change if the randomness is filled up with zeros -/
theorem fm_setR {F : Type} (C₀ : Code.Enc F) (r' : ℕ) (h : C₀.r ≤ r') {K : Type} [Zero K]
    (μ : Fin C₀.msg → K) (ρ : Fin C₀.r → K) :
    (C₀.setR r').fm μ (fun q : Fin r' => if hq : q.val < C₀.r then ρ ⟨q.val, hq⟩ else 0) =
      C₀.fm μ ρ := by
  funext i
  show (if h1 : i.val < C₀.msg then μ ⟨i.val, h1⟩
      else if h2 : i.val - C₀.msg < r' then
        (if hq : i.val - C₀.msg < C₀.r then ρ ⟨i.val - C₀.msg, hq⟩ else 0)
      else 0) =
    if h1 : i.val < C₀.msg then μ ⟨i.val, h1⟩
    else if h2 : i.val - C₀.msg < C₀.r then ρ ⟨i.val - C₀.msg, h2⟩
    else 0
  by_cases h1 : i.val < C₀.msg
  · rw [dif_pos h1, dif_pos h1]
  · rw [dif_neg h1, dif_neg h1]
    by_cases h2 : i.val - C₀.msg < C₀.r
    · rw [dif_pos (lt_of_lt_of_le h2 h), dif_pos h2]
    · rw [dif_neg h2]
      by_cases h3 : i.val - C₀.msg < r'
      · rw [dif_pos h3]
      · rw [dif_neg h3]

theorem ld_sub_ld (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] :
    Spec.ld_sub_ld F E := fun A _ _ C r' P _ pos mult R _ _ h =>
  { onto := fun β => ⟨β, rfl⟩
    word := fun f' => ⟨f', fun _ _ => rfl⟩
    code := fun m' ρ' => ⟨m', fun q => if hq : q.2.2.val < (C q.1).r then ρ' ⟨q.1, (q.2.1, ⟨q.2.2.val, hq⟩)⟩ else 0, fun x α => by
      show ((C α.1).GE E).mulVec
          ((C α.1).fm (fun j => m' ⟨α.1, (α.2.1, j)⟩) fun q => ρ' ⟨α.1, (α.2.1, q)⟩) (pos α.1 x) =
        ((C α.1).GE E).mulVec
          (((C α.1).setR (r' α.1)).fm (fun j => m' ⟨α.1, (α.2.1, j)⟩) fun q : Fin (r' α.1) =>
            if hq : q.val < (C α.1).r then ρ' ⟨α.1, (α.2.1, ⟨q.val, hq⟩)⟩ else 0) (pos α.1 x)
      exact congrArg (fun v => ((C α.1).GE E).mulVec v (pos α.1 x))
        (fm_setR (C α.1) (r' α.1) (h α.1) (fun j => m' ⟨α.1, (α.2.1, j)⟩) fun q =>
          ρ' ⟨α.1, (α.2.1, q)⟩).symm⟩ }

end Cb
