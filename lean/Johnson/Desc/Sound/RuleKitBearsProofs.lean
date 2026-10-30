-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Sound/RuleKitBearsProofs.lean: the proofs of the statements of
Johnson/Desc/Sound/RuleKitBears.lean. Theorems and the lemmas that they need.

Limits: those of that file.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.RuleKitBears
import Johnson.Desc.Sound.RuleKitMoreProofs
import Iop.DrawKap

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.Sound
open TypedOracleCompiler.Run.PQ (RD)
open scoped ENNReal

theorem kitBearsAt : KitBearsAt := by
  intro f d m e h hb hm
  have s := kitShareCard f d h
  have kp : _root_.Iop.kapSl 128 ^ (_root_.Run.bsRound f d.entry d.kind).b ≤ 2 := by
    have k0 := _root_.Iop.kapSl_pow_le (sl := 128)
      (n := (_root_.Run.bsRound f d.entry d.kind).b) (e := 0) (by simpa using hb)
    refine le_trans k0 (le_of_eq ?_)
    norm_num
  have n1 : kitF f d * (m * 2 ^ (e + 1)) ≤ kitF f d * (f.p ^ 3 - 1) := Nat.mul_le_mul_left _ hm
  have c1 : ((kitF f d * (m * 2 ^ (e + 1)) : ℕ) : ℝ≥0∞) ≤
      ((2 * Fintype.card (_root_.Iop.GChal d.entry.work
        ((_root_.Run.ckP f).Ch d.entry d.kind)) : ℕ) : ℝ≥0∞) := by
    calc ((kitF f d * (m * 2 ^ (e + 1)) : ℕ) : ℝ≥0∞)
        ≤ ((kitF f d * (f.p ^ 3 - 1) : ℕ) : ℝ≥0∞) := Nat.cast_le.2 n1
      _ = (kitF f d : ℝ≥0∞) * ((f.p ^ 3 - 1 : ℕ) : ℝ≥0∞) := Nat.cast_mul _ _
      _ ≤ _root_.Iop.kapSl 128 ^ (_root_.Run.bsRound f d.entry d.kind).b *
          (Fintype.card (_root_.Iop.GChal d.entry.work
            ((_root_.Run.ckP f).Ch d.entry d.kind)) : ℝ≥0∞) := s
      _ ≤ 2 * (Fintype.card (_root_.Iop.GChal d.entry.work
            ((_root_.Run.ckP f).Ch d.entry d.kind)) : ℝ≥0∞) := by gcongr
      _ = _ := by
          rw [Nat.cast_mul]
          rfl
  have c2 := Nat.cast_le.1 c1
  have c3 : 2 * (m * kitF f d * 2 ^ e) ≤ 2 * Fintype.card (_root_.Iop.GChal d.entry.work
      ((_root_.Run.ckP f).Ch d.entry d.kind)) := by
    calc 2 * (m * kitF f d * 2 ^ e) = kitF f d * (m * 2 ^ (e + 1)) := by ring
      _ ≤ _ := c2
  exact Nat.le_of_mul_le_mul_left c3 (by norm_num)

theorem kitBears : KitBears := fun f d m h hb hm => kitBearsAt f d m 128 h hb hm

end VerifiableInference.Desc.Sound
