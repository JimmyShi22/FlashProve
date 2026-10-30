-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdBldMsgProofs.lean: the proofs of the statements of Cb/Ld/LdBldMsg.lean (a builder of
sendings for variable codes and numbers). Nothing assumed beyond the hypotheses of the statements
and whatever the arguments hold as proofs.
What is said and what is not: the head of that file.

Main names (statements and hypotheses: Cb/Ld/LdBldMsg.lean):
  `bld_binC`: corners by binary digits. `bld_lay`: words, layout, format and sample of each member.
  `bld_seed`, `bld_fair`: a member's part of the joint seed; fair seeds.
  `bld_smpNum`, `bld_sendNum`: the sample's numbers; the sending's error.
-/
import Cb.Ld.LdBldMsg

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR

theorem bld_binC : Spec.bld_binC := by
  intro X _ c h x y hxy
  apply (Fintype.equivFin X).injective
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < c
  · exact congrFun hxy ⟨i, hi⟩
  · have hz : ∀ z : Fin (Fintype.card X), (z : ℕ).testBit i = false := fun z =>
      Nat.testBit_lt_two_pow (lt_of_lt_of_le
        z.isLt (le_trans h (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hi))))
    rw [hz, hz]

theorem bld_lay : Spec.bld_lay := by
  intro E _ _ _ F a
  refine ⟨fun _ _ => rfl, fun x η n => ?_, rfl, ?_,
    fun h x y e => (F.m a).sp.symm.injective (bld_binC _ _ h e)⟩
  · show withPad (F := E) x η ((F.m a).nu ((F.m a).nu.symm n)) = _
    rw [Equiv.apply_symm_apply]
  · show ({ D := (F.m a).M.Z₀.D, S := (F.m a).M.Z₀.S,
            mat := fun ρ s n => (F.m a).M.Z₀.mat ρ s (splitAt (F.m a).pj ((F.m a).nu.symm n)),
            err := (F.m a).M.Z₀.err } : Sample E
          (({i : (F.m a).Ent // ¬ (F.m a).fr i.1} ⊕ {i : (F.m a).Ent // (F.m a).fr i.1}) ⊕ Unit)) =
      _
    congr 1
    funext ρ s n
    rcases n with x | u
    · show (F.m a).M.Z₀.mat ρ s
          (splitAt (F.m a).pj ((splitAt (F.m a).pj).symm (Sum.inl ((F.m a).sp.symm x)))) = _
      rw [Equiv.apply_symm_apply]
      rfl
    · show (F.m a).M.Z₀.mat ρ s (splitAt (F.m a).pj ((splitAt (F.m a).pj).symm (Sum.inr u))) = _
      rw [Equiv.apply_symm_apply]
      rfl

theorem bld_seed : Spec.bld_seed := by
  intro E _ _ _ F a s
  refine Prod.ext (funext fun i => ?_) rfl
  show s.1 ((finCongr (Nat.add_sub_cancel' (F.c_le a)).symm).symm (finSumFinEquiv (Sum.inl i))) =
    s.1 (Fin.castLE (F.c_le a) i)
  congr 1

theorem bld_fair : Spec.bld_fair := fun E _ _ _ F => ldSendFam_fair_parts E F.sig _ _ F.seedEq

/-- arithmetic -/
theorem bld_max_le (Q c X : ℕ) (h1 : c * X ≤ Q) (h2 : X ≤ Q - 1) :
    max (c * Q ^ (c - 1) * (Q - 1)) (Q ^ c) * X ≤ Q ^ c * (Q - 1) := by
  have ha : c * Q ^ (c - 1) * (Q - 1) * X ≤ Q ^ c * (Q - 1) := by
    cases c with
    | zero => simp
    | succ c =>
      calc
        (c + 1) * Q ^ (c + 1 - 1) * (Q - 1) * X = ((c + 1) * X) * (Q ^ c * (Q - 1)) := by
          rw [Nat.add_sub_cancel]; ring
        _ ≤ Q * (Q ^ c * (Q - 1)) := Nat.mul_le_mul_right _ h1
        _ = Q ^ (c + 1) * (Q - 1) := by ring
  have hb : Q ^ c * X ≤ Q ^ c * (Q - 1) := Nat.mul_le_mul_left _ h2
  rcases le_total (c * Q ^ (c - 1) * (Q - 1)) (Q ^ c) with h | h
  · rw [max_eq_right h]; exact hb
  · rw [max_eq_left h]; exact ha

theorem bld_smpNum : Spec.bld_smpNum := by
  intro E _ _ _ F a
  have hD : Fintype.card (F.sig.om a).Z.D = Fintype.card E ^ (F.m a).c * (Fintype.card E - 1) := by
    show Fintype.card ((Fin (F.m a).c → E) × Eˣ) = _
    rw [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_units]
  have hE : (F.sig.om a).Z.err =
      max ((F.m a).c * Fintype.card E ^ ((F.m a).c - 1) * (Fintype.card E - 1))
        (Fintype.card E ^ (F.m a).c) := by
    show max (Fintype.card (Fin (F.m a).c) *
          Fintype.card E ^ (Fintype.card (Fin (F.m a).c) - 1) * Fintype.card Eˣ)
        (Fintype.card E ^ Fintype.card (Fin (F.m a).c)) = _
    rw [Fintype.card_fin, Fintype.card_units]
  refine ⟨hD, hE, fun X h1 h2 => ?_⟩
  rw [hD, hE]
  exact bld_max_le _ _ X h1 h2

theorem bld_sendNum : Spec.bld_sendNum := by
  intro E _ _ _ F L X h1 h2
  have hterm : ∀ a, Fintype.card F.O * (F.Sd.mult a * ((L a).choose 2 * (F.sig.om a).Z.err) * X) ≤
      Fintype.card F.Sd.D := by
    intro a
    have h := (bld_smpNum E F a).2.2 ((L a).choose 2 * (Fintype.card F.O * X)) (h1 a) (h2 a)
    calc Fintype.card F.O * (F.Sd.mult a * ((L a).choose 2 * (F.sig.om a).Z.err) * X)
        = F.Sd.mult a * ((F.sig.om a).Z.err * ((L a).choose 2 * (Fintype.card F.O * X))) := by ring
      _ ≤ F.Sd.mult a * Fintype.card (F.sig.om a).Z.D := Nat.mul_le_mul_left _ h
      _ = Fintype.card F.Sd.D := (bld_fair E F).2 a
  rcases Nat.eq_zero_or_pos (Fintype.card F.O) with h0 | h0
  · haveI : IsEmpty F.O := Fintype.card_eq_zero_iff.1 h0
    have : ldSendFamErr F.sig F.Sd L = 0 := Finset.sum_eq_zero fun a _ => (IsEmpty.false a).elim
    rw [this, Nat.zero_mul]
    exact Nat.zero_le _
  · refine Nat.le_of_mul_le_mul_left ?_ h0
    calc Fintype.card F.O * (ldSendFamErr F.sig F.Sd L * X)
        = ∑ a, Fintype.card F.O * (F.Sd.mult a * ((L a).choose 2 * (F.sig.om a).Z.err) * X) := by
          unfold ldSendFamErr
          rw [Finset.sum_mul, Finset.mul_sum]
      _ ≤ ∑ _a : F.O, Fintype.card F.Sd.D := Finset.sum_le_sum fun a _ => hterm a
      _ = Fintype.card F.O * Fintype.card F.Sd.D := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

end Cb
