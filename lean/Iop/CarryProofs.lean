-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Iop/CarryProofs.lean: the proofs of the statements of Iop/Carry.lean: "the prover has lost" is
carried back along maps of messages, round by round.

By recursion on the two shapes. In one round: a verifier message c of s after which the prover has
not lost has an image c' after which the prover has not lost in s' (else all later transcripts are
in the goal, or the recursion applies); at most e values c' are such, and at most w values c go to
each (`cnt_some_le`).

Main names: one theorem for each statement, of the same name; `Carry.doomed` is the rule with the
shapes implicit.

Limits: those in the head of Iop/Carry.lean.

Terms: lean/GLOSSARY.md.

-/
import Iop.Carry
import Iop.Compose
import Prob.Count

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

namespace Carry

/-- The image of a transcript, one round unfolded. -/
theorem tr_cons {r r' : Round} {s s' : Shape} (fm : r.Msg → r'.Msg)
    (fc : r.Msg → r.Chal → Option r'.Chal) (k : r.Msg → r.Chal → Carry s s') (m : r.Msg)
    (c : r.Chal) (τ : Tr s) :
    tr (s := r :: s) (s' := r' :: s') (fm, fc, k) (m, c, τ) =
      (fc m c).bind fun c' => (tr (k m c) τ).map fun τ' => (fm m, c', τ') := rfl

end Carry

/-- If at most w elements go to one value, then a set of values has at most w times as many
elements that go into it. Elements without a value are not counted. -/
theorem cnt_some_le {U K : Type} [Fintype U] [Fintype K] (φ : U → Option K) {w : ℕ}
    (hw : ∀ c, cnt (fun a => φ a = some c) ≤ w) (P : K → Prop) :
    cnt (fun a => ∃ c, φ a = some c ∧ P c) ≤ cnt P * w := by
  classical
  have h1 : cnt (fun a => ∃ c, φ a = some c ∧ P c)
      ≤ cnt (fun a => ∃ c ∈ Finset.univ.filter P, φ a = some c) :=
    cnt_mono fun _ ⟨c, hc, hP⟩ => ⟨c, Finset.mem_filter.2 ⟨Finset.mem_univ c, hP⟩, hc⟩
  have h2 : cnt (fun a => ∃ c ∈ Finset.univ.filter P, φ a = some c)
      ≤ ∑ c ∈ Finset.univ.filter P, cnt (fun a => φ a = some c) :=
    cnt_exists_mem_le (Finset.univ.filter P) (fun c a => φ a = some c)
  have h3 : ∑ c ∈ Finset.univ.filter P, cnt (fun a => φ a = some c)
      ≤ ∑ _c ∈ Finset.univ.filter P, w := Finset.sum_le_sum fun c _ => hw c
  have h4 : (Finset.univ.filter P).card = cnt P := (cnt_eq_card_filter P).symm
  rw [Finset.sum_const, smul_eq_mul, h4] at h3
  exact h1.trans (h2.trans h3)

/-- The rule, the shapes implicit. -/
theorem Carry.doomed : ∀ {s s' : Shape} (F : Carry s s') (ws : Err s), F.Fib ws → ∀ (ε : Err s')
    (bad : Tr s → Prop) (bad' : Tr s' → Prop), (∀ τ, F.tr τ = none → bad τ) →
    (∀ τ τ', F.tr τ = some τ' → bad' τ' → bad τ) → Doomed s' ε bad' →
    Doomed s (mulErr s s' ws ε) bad
  | [], [], _, _, _, _, _, _, _, h, hd => h () () rfl hd
  | r :: s, r' :: s', (fm, fc, k), (w, ws), hF, (e, ε), bad, bad', h0, h, hd => fun m => by
      show cnt (fun c : r.Chal => ¬ Doomed s (mulErr s s' ws ε) (fun τ => bad (m, c, τ))) ≤ e * w
      have key : ∀ c : r.Chal, ¬ Doomed s (mulErr s s' ws ε) (fun τ => bad (m, c, τ)) →
          ∃ c', fc m c = some c' ∧ ¬ Doomed s' ε (fun τ' => bad' (fm m, c', τ')) := by
        intro c hc
        cases hfc : fc m c with
        | none =>
          refine absurd (Doomed.of_forall s _ fun τ => h0 (m, c, τ) ?_) hc
          rw [Carry.tr_cons, hfc]
          rfl
        | some c' =>
          refine ⟨c', rfl, fun hd' => hc ?_⟩
          refine Carry.doomed (k m c) ws (hF.2 m c) ε _ _ ?_ ?_ hd'
          · intro τ hτ
            refine h0 (m, c, τ) ?_
            rw [Carry.tr_cons, hfc, hτ]
            rfl
          · intro τ τ' hτ hb
            refine h (m, c, τ) (fm m, c', τ') ?_ hb
            rw [Carry.tr_cons, hfc, hτ]
            rfl
      exact (cnt_mono key).trans
        ((cnt_some_le (fc m) (hF.1 m) _).trans (Nat.mul_le_mul_right w (hd (fm m))))
  | [], _ :: _, F, _, _, _, _, _, _, _, _ => nomatch F
  | _ :: _, [], F, _, _, _, _, _, _, _, _ => nomatch F

theorem carry_doomed : Spec.carry_doomed := fun _ _ F ws hF ε bad bad' h0 h hd =>
  Carry.doomed F ws hF ε bad bad' h0 h hd

theorem carry_sound : Spec.carry_sound :=
  fun _ _ _ _ Q Q' F ws hF fx fy _ _ ε hL hacc h x y hn =>
  Carry.doomed (F x y) ws (hF x y) ε (fun τ => Q.accept x y τ = false)
    (fun τ' => Q'.accept (fx x) (fy y) τ' = false)
    (fun τ hτ => by
      show Q.accept x y τ = false
      cases ha : Q.accept x y τ with
      | false => rfl
      | true =>
        obtain ⟨τ', h1, _⟩ := hacc x y τ ha
        rw [hτ] at h1
        cases h1)
    (fun τ τ' hτ hb => by
      show Q.accept x y τ = false
      have hb' : Q'.accept (fx x) (fy y) τ' = false := hb
      cases ha : Q.accept x y τ with
      | false => rfl
      | true =>
        obtain ⟨τ'', h1, h2⟩ := hacc x y τ ha
        rw [hτ] at h1
        cases h1
        rw [hb'] at h2
        cases h2)
    (h (fx x) (fy y) fun hl => hn (hL x y hl))

theorem carry_below : Spec.carry_below
  | [], _, _, _, _, _, _, _ => trivial
  | _ :: s, [], (_, ws), k, c, _, _, _ =>
      ⟨by simp, carry_below s [] ws k c () (by cases s <;> trivial) trivial⟩
  | r :: s, r' :: s', (w, ws), k, c, (e, ε), hR, hB => by
      refine ⟨?_, carry_below s s' ws k c ε hR.2 hB.2⟩
      have h1 : (e : ℝ≥0∞) ≤ c * (Fintype.card r'.Chal : ℝ≥0∞) := hB.1
      have h2 : (w : ℝ≥0∞) * (Fintype.card r'.Chal : ℝ≥0∞)
          ≤ k * (Fintype.card r.Chal : ℝ≥0∞) := hR.1
      calc ((e * w : ℕ) : ℝ≥0∞) = (e : ℝ≥0∞) * (w : ℝ≥0∞) := Nat.cast_mul e w
        _ ≤ (c * (Fintype.card r'.Chal : ℝ≥0∞)) * (w : ℝ≥0∞) := by gcongr
        _ = c * ((w : ℝ≥0∞) * (Fintype.card r'.Chal : ℝ≥0∞)) := by ring
        _ ≤ c * (k * (Fintype.card r.Chal : ℝ≥0∞)) := by gcongr
        _ = k * c * (Fintype.card r.Chal : ℝ≥0∞) := by ring

namespace Carry

/-- every transcript is its own image -/
theorem tr_id : ∀ (s : Shape) (τ : Tr s), (Carry.id s).tr τ = some τ
  | [], () => rfl
  | r :: s, (m, c, τ) => by
      show (some c).bind (fun c' => (tr (Carry.id s) τ).map fun τ' => (m, c', τ')) = _
      rw [tr_id s τ]
      rfl

/-- one verifier message goes to one -/
theorem fib_id : ∀ s : Shape, (Carry.id s).Fib (Err.ones s)
  | [] => trivial
  | _ :: s =>
      ⟨fun _ _ => cnt_le_one fun _ _ ha hb => Option.some.inj (ha.trans hb.symm),
        fun _ _ => fib_id s⟩

/-- the image under `F.app G` -/
theorem tr_app : ∀ {s₁ s₁' s₂ s₂' : Shape} (F : Carry s₁ s₁') (G : Tr s₁ → Carry s₂ s₂')
    (τ₁ : Tr s₁) (τ₂ : Tr s₂), (F.app G).tr (Tr.app τ₁ τ₂) =
      (F.tr τ₁).bind fun τ₁' => ((G τ₁).tr τ₂).map fun τ₂' => Tr.app τ₁' τ₂'
  | [], [], _, _, _, G, (), τ₂ => by
      show (G ()).tr τ₂ = ((G ()).tr τ₂).map fun τ₂' => τ₂'
      rw [Option.map_id']
  | r :: s₁, r' :: s₁', s₂, s₂', (fm, fc, k), G, (m, c, τ₁), τ₂ => by
      show (fc m c).bind (fun c' =>
          (tr (app (k m c) fun τ => G (m, c, τ)) (Tr.app τ₁ τ₂)).map fun τ' => (fm m, c', τ')) = _
      rw [tr_app (k m c) (fun τ => G (m, c, τ)) τ₁ τ₂, tr_cons]
      cases fc m c with
      | none => rfl
      | some c' =>
        cases tr (k m c) τ₁ with
        | none => rfl
        | some τ₁' =>
          cases tr (G (m, c, τ₁)) τ₂ with
          | none => rfl
          | some τ₂' => rfl
  | [], _ :: _, _, _, F, _, _, _ => nomatch F
  | _ :: _, [], _, _, F, _, _, _ => nomatch F

/-- the fibres of `F.app G` -/
theorem fib_app : ∀ {s₁ s₁' s₂ s₂' : Shape} (F : Carry s₁ s₁') (G : Tr s₁ → Carry s₂ s₂')
    (ws₁ : Err s₁) (ws₂ : Err s₂), F.Fib ws₁ → (∀ τ, (G τ).Fib ws₂) →
    (F.app G).Fib (Err.app ws₁ ws₂)
  | [], [], _, _, _, _, _, _, _, hG => hG ()
  | _ :: _, _ :: _, _, _, (_, _, k), G, (_, ws₁), ws₂, hF, hG =>
      ⟨hF.1, fun m c => fib_app (k m c) (fun τ => G (m, c, τ)) ws₁ ws₂ (hF.2 m c)
        fun τ => hG (m, c, τ)⟩
  | [], _ :: _, _, _, F, _, _, _, _, _ => nomatch F
  | _ :: _, [], _, _, F, _, _, _, _, _ => nomatch F

end Carry

/-- at w = 1 in each round the errors are unchanged -/
theorem mulErr_ones : ∀ (s : Shape) (ε : Err s), mulErr s s (Err.ones s) ε = ε
  | [], () => rfl
  | _ :: s, (e, ε) => by
      show (e * 1, mulErr s s (Err.ones s) ε) = (e, ε)
      rw [Nat.mul_one, mulErr_ones s ε]

/-- errors in a row, between shapes with a `Carry` -/
theorem mulErr_app : ∀ {s₁ s₁' : Shape} (_ : Carry s₁ s₁') (s₂ s₂' : Shape) (ws₁ : Err s₁)
    (ws₂ : Err s₂) (ε₁ : Err s₁') (ε₂ : Err s₂'),
    mulErr (s₁ ++ s₂) (s₁' ++ s₂') (Err.app ws₁ ws₂) (Err.app ε₁ ε₂) =
      Err.app (mulErr s₁ s₁' ws₁ ε₁) (mulErr s₂ s₂' ws₂ ε₂)
  | [], [], _, _, _, _, _, _, _ => rfl
  | r :: s₁, r' :: s₁', (fm, fc, k), s₂, s₂', (w, ws₁), ws₂, (e, ε₁), ε₂ => by
      show (e * w, mulErr (s₁ ++ s₂) (s₁' ++ s₂') (Err.app ws₁ ws₂) (Err.app ε₁ ε₂)) = _
      rw [mulErr_app (k (r.dOrc, r.dPlain) (Classical.arbitrary r.Chal)) s₂ s₂' ws₁ ws₂ ε₁ ε₂]
      rfl
  | [], _ :: _, F, _, _, _, _, _, _ => nomatch F
  | _ :: _, [], F, _, _, _, _, _, _ => nomatch F

theorem carry_id : Spec.carry_id := fun s => ⟨Carry.tr_id s, Carry.fib_id s, mulErr_ones s⟩

theorem carry_app : Spec.carry_app := fun _ _ s₂ s₂' F G =>
  ⟨Carry.tr_app F G, Carry.fib_app F G, mulErr_app F s₂ s₂'⟩

end Iop
