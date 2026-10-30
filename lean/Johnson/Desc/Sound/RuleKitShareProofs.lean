-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKitShareProofs.lean: the proof of `KitShare` of
Johnson/Desc/Sound/RuleKit.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleKit

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open TypedOracleCompiler.Run.PQ (RD)
open _root_.Run (Vals DVal bsRound EV NZ zF)
open scoped ENNReal

theorem card_vals_cons (f : Fmt.Fld) (d : Fmt.Draw) (ds : List Fmt.Draw) :
    Nat.card (Vals f (d :: ds)) = Nat.card (DVal f d) * Nat.card (Vals f ds) :=
  Nat.card_prod (DVal f d) (Vals f ds)

theorem card_ev (f : Fmt.Fld) : Nat.card (EV f) = f.p ^ 3 := by
  show Nat.card (Fin f.p × Fin f.p × Fin f.p) = _
  rw [Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_fin]
  ring

theorem card_nz (f : Fmt.Fld) : f.p ^ 3 - 1 ≤ Nat.card (NZ f) := by
  classical
  have hinj : Function.Injective (fun e : EV f =>
      if h : e = (zF f, zF f, zF f) then (none : Option (NZ f)) else some ⟨e, h⟩) := by
    intro a b hab
    by_cases ha : a = (zF f, zF f, zF f)
    · by_cases hb : b = (zF f, zF f, zF f)
      · rw [ha, hb]
      · simp [ha, hb] at hab
    · by_cases hb : b = (zF f, zF f, zF f)
      · simp [ha, hb] at hab
      · simpa [ha, hb] using hab
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Finite.card_option, card_ev] at h
  omega

theorem elem_card_ge (f : Fmt.Fld) (d : Fmt.Draw) (hd : isElem d = true) :
    f.p ^ 3 - 1 ≤ Nat.card (DVal f d) := by
  cases d with
  | elem =>
    show _ ≤ Nat.card (EV f)
    rw [card_ev]
    exact Nat.sub_le _ _
  | elemNZ => exact card_nz f
  | pos k => simp [isElem] at hd
  | trits m => simp [isElem] at hd
  | sealed => simp [isElem] at hd

theorem others_mul_le (f : Fmt.Fld) (ds : List Fmt.Draw) :
    others f ds * (f.p ^ 3 - 1) ≤ Nat.card (Vals f ds) := by
  induction ds with
  | nil => simp [others]
  | cons d ds ih =>
    rw [card_vals_cons]
    have big : Nat.card (DVal f d) * others f ds * (f.p ^ 3 - 1) ≤
        Nat.card (DVal f d) * Nat.card (Vals f ds) := by
      calc Nat.card (DVal f d) * others f ds * (f.p ^ 3 - 1)
          = Nat.card (DVal f d) * (others f ds * (f.p ^ 3 - 1)) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ ih
    by_cases hd : isElem d = true
    · have hc := elem_card_ge f d hd
      have e : others f (d :: ds) =
          max (Nat.card (Vals f ds)) (Nat.card (DVal f d) * others f ds) := by
        simp [others, hd]
      rw [e]
      rcases le_total (Nat.card (Vals f ds)) (Nat.card (DVal f d) * others f ds) with h | h
      · rw [max_eq_right h]
        exact big
      · rw [max_eq_left h]
        calc Nat.card (Vals f ds) * (f.p ^ 3 - 1)
            ≤ Nat.card (Vals f ds) * Nat.card (DVal f d) := Nat.mul_le_mul_left _ hc
          _ = _ := by ring
    · have e : others f (d :: ds) = Nat.card (DVal f d) * others f ds := by
        simp [others, hd]
      rw [e]
      exact big

theorem kitShare : KitShare := by
  intro f d h
  have G := (_root_.Run.planDraws_law f d.entry d.kind h).1
  have o := others_mul_le f (Fmt.dsOf d.entry d.kind)
  have n1 : kitF f d * (f.p ^ 3 - 1) ≤ 2 ^ d.entry.work *
      ((bsRound f d.entry d.kind).w * Nat.card (Vals f (Fmt.dsOf d.entry d.kind))) := by
    unfold kitF
    calc 2 ^ d.entry.work * ((bsRound f d.entry d.kind).w * others f (Fmt.dsOf d.entry d.kind)) *
          (f.p ^ 3 - 1)
        = 2 ^ d.entry.work * ((bsRound f d.entry d.kind).w *
          (others f (Fmt.dsOf d.entry d.kind) * (f.p ^ 3 - 1))) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ o)
  have r := G.ratio
  calc (kitF f d : ℝ≥0∞) * ((f.p ^ 3 - 1 : ℕ) : ℝ≥0∞)
      = ((kitF f d * (f.p ^ 3 - 1) : ℕ) : ℝ≥0∞) := (Nat.cast_mul _ _).symm
    _ ≤ ((2 ^ d.entry.work * ((bsRound f d.entry d.kind).w *
          Nat.card (Vals f (Fmt.dsOf d.entry d.kind))) : ℕ) : ℝ≥0∞) := Nat.cast_le.2 n1
    _ = ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) * (((bsRound f d.entry d.kind).w : ℝ≥0∞) *
          (Nat.card (Vals f (Fmt.dsOf d.entry d.kind)) : ℝ≥0∞)) := by
        rw [Nat.cast_mul, Nat.cast_mul]
    _ ≤ ((2 ^ d.entry.work : ℕ) : ℝ≥0∞) * (_root_.Iop.kapSl 128 ^ (bsRound f d.entry d.kind).b *
          (Fintype.card (Fin (bsRound f d.entry d.kind).b → _root_.Iop.Dig 256) : ℝ≥0∞)) :=
        mul_le_mul_right r _
    _ = _ := by
        rw [Nat.cast_mul]
        ring

end VerifiableInference.Desc.Sound
