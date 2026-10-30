-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DrawBSProofs.lean: the proofs of the statements of Run/DrawBS.lean (from a reader of a row of
words to a block sampler). Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

The theorems `drawBS_row`, `drawBS_good`, `drawBS_pow` prove the statements of the same names in
`Run.Spec`.
-/
import Run.DrawBS
import Run.DrawCount
import Iop.DrawProofs

set_option autoImplicit false

namespace Run
open Prob Iop
open scoped ENNReal

section
variable {W : Type}

/-- the blocks of a row -/
def unrow (e : Dig 64 ≃ W) (b : ℕ) (v : Fin (4 * b) → W) : Fin b → Dig 256 :=
  fun i s => e.symm (v ⟨4 * i.val + s.val / 64, by omega⟩) ⟨s.val % 64, by omega⟩

theorem unrow_row (e : Dig 64 ≃ W) (b : ℕ) (u : Fin b → Dig 256) : unrow e b (rowOf e b u) = u := by
  funext i s
  show e.symm (e (wordBits (u ⟨(4 * i.val + s.val / 64) / 4, _⟩) ⟨(4 * i.val + s.val / 64) % 4, _⟩))
      ⟨s.val % 64, _⟩ = u i s
  rw [Equiv.symm_apply_apply]
  show u ⟨(4 * i.val + s.val / 64) / 4, _⟩ ⟨64 * ((4 * i.val + s.val / 64) % 4) + s.val % 64, _⟩ =
    u i s
  have h1 : (⟨(4 * i.val + s.val / 64) / 4, by omega⟩ : Fin b) = i :=
    Fin.ext (by show (4 * i.val + s.val / 64) / 4 = i.val; omega)
  have h2 : (⟨64 * ((4 * i.val + s.val / 64) % 4) + s.val % 64, by omega⟩ : Fin 256) = s :=
    Fin.ext (by show 64 * ((4 * i.val + s.val / 64) % 4) + s.val % 64 = s.val; omega)
  rw [h1, h2]

theorem row_unrow (e : Dig 64 ≃ W) (b : ℕ) (v : Fin (4 * b) → W) : rowOf e b (unrow e b v) = v := by
  funext i
  show e (wordBits (unrow e b v ⟨i.val / 4, _⟩) ⟨i.val % 4, _⟩) = v i
  have h : wordBits (unrow e b v ⟨i.val / 4, by omega⟩) ⟨i.val % 4, by omega⟩ = e.symm (v i) := by
    funext t
    show e.symm (v ⟨4 * (i.val / 4) + (64 * (i.val % 4) + t.val) / 64, _⟩)
        ⟨(64 * (i.val % 4) + t.val) % 64, _⟩ = e.symm (v i) t
    have h1 : (⟨4 * (i.val / 4) + (64 * (i.val % 4) + t.val) / 64, by omega⟩ : Fin (4 * b)) = i :=
      Fin.ext (by show 4 * (i.val / 4) + (64 * (i.val % 4) + t.val) / 64 = i.val; omega)
    have h2 : (⟨(64 * (i.val % 4) + t.val) % 64, by omega⟩ : Fin 64) = t :=
      Fin.ext (by show (64 * (i.val % 4) + t.val) % 64 = t.val; omega)
    rw [h1, h2]
  rw [h, Equiv.apply_symm_apply]

/-- the row of b blocks, as a bijection -/
def rowEquiv (e : Dig 64 ≃ W) (b : ℕ) : (Fin b → Dig 256) ≃ (Fin (4 * b) → W) :=
  ⟨rowOf e b, unrow e b, unrow_row e b, row_unrow e b⟩

end

theorem drawBS_row : Spec.drawBS_row := fun _ e b => (rowEquiv e b).bijective

theorem card_word {W : Type} (e : Dig 64 ≃ W) : Nat.card W = 2 ^ 64 := by
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, BS.card_dig]

theorem drawBS_good : Spec.drawBS_good := by
  intro W C _ e d t K w κ h
  haveI : Fintype W := Fintype.ofFinite W
  have hb : K + (4 * ((K + 3) / 4) - K) = 4 * ((K + 3) / 4) := by omega
  have hQ : Fintype.card W = 2 ^ 64 := by rw [← Nat.card_eq_fintype_card]; exact card_word e
  -- the words after the K-th are free
  have g := Tr.good_pad d h (4 * ((K + 3) / 4) - K)
  rw [hb, hQ] at g
  refine ⟨fun c => ?_, ?_⟩
  · -- the rows of the blocks are all rows of 4 b words
    have h1 : cnt (fun a : Fin ((K + 3) / 4) → Dig 256 =>
          t.ev d (4 * ((K + 3) / 4)) (rowOf e ((K + 3) / 4) a) = c) =
        Tr.N d (4 * ((K + 3) / 4)) t c :=
      Nat.card_congr ((rowEquiv e ((K + 3) / 4)).subtypeEquiv fun _ => Iff.rfl)
    show cnt (fun a : Fin ((K + 3) / 4) → Dig 256 =>
        t.ev d (4 * ((K + 3) / 4)) (rowOf e ((K + 3) / 4) a) = c) ≤
      w * (2 ^ 64) ^ (4 * ((K + 3) / 4) - K)
    rw [h1]
    exact g.fib c
  · have hc : Fintype.card (Fin ((K + 3) / 4) → Dig 256) = Nat.card W ^ (4 * ((K + 3) / 4)) := by
      rw [Fintype.card_congr (rowEquiv e ((K + 3) / 4)), Fintype.card_fun,
        Fintype.card_fin, Nat.card_eq_fintype_card]
    show ((w * (2 ^ 64) ^ (4 * ((K + 3) / 4) - K) : ℕ) : ℝ≥0∞) * (Nat.card C : ℝ≥0∞) ≤
      κ * (Fintype.card (Fin ((K + 3) / 4) → Dig 256) : ℝ≥0∞)
    rw [hc, Nat.cast_pow]
    exact g.ratio

theorem drawBS_pow : Spec.drawBS_pow := fun W C _ e d t K w n κ₀ h1 hn h =>
  (drawBS_good W C e d t K w _ h).mono (pow_le_pow_right₀ h1 (show n ≤ (K + 3) / 4 by omega))

end Run
