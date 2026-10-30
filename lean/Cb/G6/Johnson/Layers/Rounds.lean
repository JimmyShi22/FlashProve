-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/G6/Johnson/Layers/Rounds.lean: two kinds of draw, each as one round's set of bad draws.

Definitions, statements and proofs. No protocol occurs here. The form is the one that round-by-round
soundness takes (Iop/Rbr.lean): a set of draws that is fixed before the draw, a bound on its number,
and what a draw outside it gives.

Main names:
  A batch by the powers of one element. `badPow a`: the γ at which the sum of γ^j a_j is 0, if a is
    not 0; empty if a = 0. `cnt_badPow`: at most m - 1 of them. `zero_of_pow`: outside it, a batch
    that vanishes gives a = 0.
  A point under the equality kernel, with vectors and points as functions on ℕ (`Blocks.ext`,
    Blocks/Ext.lean). `badPt g d`: the points at which the extension of d vanishes, if d is not 0
    below 2^g. `cnt_badPt`: at most g |E|^(g-1). `zero_of_pt`: outside it, an extension that
    vanishes gives d X = 0 for all X < 2^g.
  `badPtFam`, `cnt_badPtFam`, `zero_of_pt_fam`: for a family of vectors, with one bad set: that of
    one member that is not 0. No union is taken, so the bound is that of one vector.

The two bounds are `Alg.count_powers_le` (Alg/Poly.lean) and `Blocks.cnt_ext_zero_le`
(Blocks/Ext.lean).
Limits: nothing is assumed; nothing is said on a protocol.

-/
import Iop.Rbr
import Alg.Poly
import Blocks.Ext

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.L5.Layers
open Prob Finset

section Pow
variable {E : Type} [Field E]

/-- The bad elements of a batch by powers. -/
def badPow {m : ℕ} (a : Fin m → E) : Set E := {γ | a ≠ 0 ∧ ∑ j : Fin m, γ ^ (j : ℕ) * a j = 0}

theorem cnt_badPow [Fintype E] {m : ℕ} (a : Fin m → E) : cnt (fun γ => γ ∈ badPow a) ≤ m - 1 := by
  by_cases ha : a = 0
  · rw [cnt_false fun γ hγ => hγ.1 ha]
    exact Nat.zero_le _
  · refine le_trans (cnt_mono fun γ hγ => hγ.2) ?_
    have h := Alg.count_powers_le a ha 0
    simpa using h

theorem zero_of_pow {m : ℕ} {a : Fin m → E} {γ : E} (hγ : γ ∉ badPow a)
    (h : ∑ j : Fin m, γ ^ (j : ℕ) * a j = 0) : a = 0 := by
  by_contra ha
  exact hγ ⟨ha, h⟩

end Pow

section Pt
variable {E : Type} [Field E]

/-- The bad points of a vector under the equality kernel. -/
def badPt (g : ℕ) (d : ℕ → E) : Set (Fin g → E) :=
  {p | (∃ X < 2 ^ g, d X ≠ 0) ∧ Blocks.ext g d (Blocks.nat p) = 0}

theorem cnt_badPt [Fintype E] (g : ℕ) (d : ℕ → E) :
    cnt (fun p => p ∈ badPt g d) ≤ g * Fintype.card E ^ (g - 1) := by
  by_cases hd : ∃ X < 2 ^ g, d X ≠ 0
  · exact le_trans (cnt_mono fun p hp => hp.2) (Blocks.cnt_ext_zero_le g d hd)
  · rw [cnt_false fun p hp => hd hp.1]
    exact Nat.zero_le _

theorem zero_of_pt {g : ℕ} {d : ℕ → E} {p : Fin g → E} (hp : p ∉ badPt g d)
    (h : Blocks.ext g d (Blocks.nat p) = 0) : ∀ X < 2 ^ g, d X = 0 := by
  intro X hX
  by_contra hne
  exact hp ⟨⟨X, hX, hne⟩, h⟩

open Classical in
/-- One bad set for a family: that of a member that is not 0, if there is one. -/
noncomputable def badPtFam {J : Type} (g : ℕ) (d : J → ℕ → E) : Set (Fin g → E) :=
  if h : ∃ k, ∃ X < 2 ^ g, d k X ≠ 0 then badPt g (d h.choose) else ∅

theorem cnt_badPtFam [Fintype E] {J : Type} (g : ℕ) (d : J → ℕ → E) :
    cnt (fun p => p ∈ badPtFam g d) ≤ g * Fintype.card E ^ (g - 1) := by
  unfold badPtFam
  split
  · exact cnt_badPt g _
  · rw [cnt_false (P := fun p => p ∈ (∅ : Set (Fin g → E))) fun p hp => Set.notMem_empty p hp]
    exact Nat.zero_le _

/-- Outside the one bad set: if the extensions of all members vanish at the point, all members are
0. -/
theorem zero_of_pt_fam {J : Type} {g : ℕ} {d : J → ℕ → E} {p : Fin g → E}
    (hp : p ∉ badPtFam g d) (h : ∀ k, Blocks.ext g (d k) (Blocks.nat p) = 0) :
    ∀ k, ∀ X < 2 ^ g, d k X = 0 := by
  by_contra hne
  have hex : ∃ k, ∃ X < 2 ^ g, d k X ≠ 0 := by
    by_contra hno
    exact hne fun k X hX => by
      by_contra h0
      exact hno ⟨k, X, hX, h0⟩
  unfold badPtFam at hp
  rw [dif_pos hex] at hp
  obtain ⟨X, hX, hX0⟩ := hex.choose_spec
  exact hX0 (zero_of_pt hp (h _) X hX)

end Pt

end Johnson.L5.Layers
