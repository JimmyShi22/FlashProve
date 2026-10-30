-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoSmall.lean: in the lookup of a sub-proof every round's number of bad
challenges is below the number of that round's challenges.

Knowledge soundness with errors says nothing at a round whose error is at least the number of its
challenge values: one such round makes the clause on the game (KnowAt.know) true for free.
forB_small shuts that case for HoleC: under HoleC's own two premises on public numbers, each term of
the block's list of errors is below the size of its round's challenge set (at a round without a
verifier's message: 0 below 1).

Main theorems: forB_small, forB_small_gl (at the challenge field and the named filling of the short
sumcheck; one premise, FoNums.ok h = true).
Not claimed: that the quotients are small; the numbers are forEps
(OnBytes/Tie/Pv/Lookup/Forest/FoHole.lean).
Not claimed: anything on completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoAt
import OnBytes.Tie.Pv.Lookup.Shift.ShiftKArith
import Mathlib.FieldTheory.Finite.Basic

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp Cb.LdLkp.Kn TWhole TwRound

theorem forB_small (E : Type) [Field E] [Fintype E] (p : ℕ) [CharP E p] {St₀ J₀ : Type} [Fintype J₀]
    [DecidableEq J₀]
    (h : Sh) (L : Lay E St₀ J₀) (V : ∀ (Y : PscPar E) Ex, ShortK Y Ex)
        (VC : ∀ (Y : PscPar E) Ex, ShortKC Y Ex) (Ex : ExtSpec)
    (H : FoNums.ok h = true) (hp : 2 ^ h.d * (2 ^ 32 - 1) < p) :
    List.Forall₂ (· < ·) (errList (forB E h L V VC (Ex := Ex)).e)
      ((forB E h L V VC (Ex := Ex)).R.shape.map fun r => Nat.card r.Chal) := by
  obtain ⟨k, _, hq⟩ := FiniteField.card E p
  have hpq : p ≤ Fintype.card E := by
    rw [hq]
    exact Nat.le_self_pow k.ne_zero p
  obtain ⟨⟨_, _, _, _, a5, _⟩, _⟩ := ok_parts H
  have hd1 : h.d + 1 ≤ 2 ^ h.d := Nat.lt_two_pow_self
  have hv : 2 ^ (FoNums.v' h + 1) < 2 ^ 32 := by
    rw [← ok_v H]
    exact Nat.pow_lt_pow_right (by norm_num) a5
  obtain ⟨X, hX⟩ : ∃ X, X = 2 ^ h.d := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = 2 ^ (FoNums.v' h + 1) := ⟨_, rfl⟩
  rw [← hX] at hp hd1
  rw [← hY] at hv
  norm_num at hp hv
  refine allK_small V VC Ex (forA E h L) (forP E h L) (FoNums.several h) rfl ?_ ?_ ?_ ?_
  · omega
  · show 2 ^ (FoNums.v' h + 1) ≤ _
    rw [← hY]
    omega
  · show FoNums.w + h.d < _
    have : FoNums.w = 5 := rfl
    omega
  · show 2 ^ h.d < _
    rw [← hX]
    omega

theorem forB_small_gl {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh)
    (L : Lay Cb.Gl.E St₀ J₀) (Ex : ExtSpec)
    (H : FoNums.ok h = true) :
    List.Forall₂ (· < ·) (errList (forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).e)
      ((forB Cb.Gl.E h L V₀ V₀C (Ex := Ex)).R.shape.map fun r => Nat.card r.Chal) :=
  forB_small Cb.Gl.E Cb.Gl.p h L V₀ V₀C Ex H (ok_wrap H (le_of_eq pW_gl))

end Cb.Fo
