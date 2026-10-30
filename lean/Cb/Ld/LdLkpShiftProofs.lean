-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpShiftProofs.lean: the proofs of the statements of Cb/Ld/LdLkpShift.lean (several lookups
into one, by a random shift).
The order: the numbering (f, b) ↦ b + 2^v · f; completeness; the count; the block.
Nothing is defined here that a statement reads.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdLkpShift.lean):
  `ldLkpShift_fwd`: complete at every θ.
  `ldLkpShift_cnt`: under `TagInj`, if some key is outside its own table: the count: at most 2^(g+d)
    bad θ (the size of the joint table).
  `ldLkpShift_goodAt`: under `TagInj`, the block at the base: `GoodAt` (Cb/Ld/LdSigLift.lean), error
    2^(g+d) (values of θ).
  `ldLkpShift_goodB`: over a signature: `GoodB` (Ior/Masked.lean) (premise: `TagInj`).

Notation:
  `g`, `v`, `d`: numbers: f ranges below 2^g, b below 2^v, u below 2^d (`AllIn`,
    Cb/Ld/LdLkpShift.lean; `InTable`, Cb/Gen/LkpAlg.lean);
  `key`, `tab`: maps ℕ → ℕ → E, written `key f b`, `tab f u`;
  `tag`: a map ℕ → E;
  `θ`: an element of E.

Limits: what the head of Cb/Ld/LdLkpShift.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpShift
import Cb.Ld.LdSigLiftProofs

set_option autoImplicit false

namespace Cb
open Finset Prob Cb.Lkp Cb.LdLkp Iop IOR

theorem ldLkpShift_num (g v f b : ℕ) (hf : f < 2 ^ g) (hb : b < 2 ^ v) :
    b + 2 ^ v * f < 2 ^ (g + v) ∧ (b + 2 ^ v * f) / 2 ^ v = f ∧ (b + 2 ^ v * f) % 2 ^ v = b := by
  have hp : 0 < 2 ^ v := Nat.pos_of_ne_zero (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have h1 : 2 ^ v * (f + 1) ≤ 2 ^ v * 2 ^ g := Nat.mul_le_mul_left _ hf
    rw [pow_add, Nat.mul_comm (2 ^ g)]
    calc b + 2 ^ v * f < 2 ^ v + 2 ^ v * f := Nat.add_lt_add_right hb _
      _ = 2 ^ v * (f + 1) := by ring
      _ ≤ 2 ^ v * 2 ^ g := h1
  · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hb, Nat.zero_add]
  · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb]

theorem ldLkpShift_split (g v X : ℕ) (hX : X < 2 ^ (g + v)) :
    X / 2 ^ v < 2 ^ g ∧ X % 2 ^ v < 2 ^ v := by
  have hp : 0 < 2 ^ v := Nat.pos_of_ne_zero (by positivity)
  refine ⟨Nat.div_lt_of_lt_mul ?_, Nat.mod_lt _ hp⟩
  rw [Nat.mul_comm, ← pow_add]
  exact hX

theorem ldLkpShift_fwd : Spec.ldLkpShift_fwd := by
  intro E _ g v d key tab tag θ h X hX
  obtain ⟨hf, hb⟩ := ldLkpShift_split g v X hX
  obtain ⟨u, hu, he⟩ := h _ hf _ hb
  obtain ⟨h1, h2, h3⟩ := ldLkpShift_num g d (X / 2 ^ v) u hf hu
  refine ⟨u + 2 ^ d * (X / 2 ^ v), h1, ?_⟩
  unfold shKey shTab
  rw [h2, h3, he]

theorem ldLkpShift_cnt : Spec.ldLkpShift_cnt := by
  classical
  intro E _ _ g v d key tab tag hT hn
  have hex : ∃ f, f < 2 ^ g ∧ ∃ b, b < 2 ^ v ∧ ∀ u < 2 ^ d, key f b ≠ tab f u := by
    by_contra hc
    refine hn fun f hf b hb => ?_
    by_contra hc'
    exact hc ⟨f, hf, b, hb, fun u hu he => hc' ⟨u, hu, he⟩⟩
  obtain ⟨f, hf, b, hb, hout⟩ := hex
  obtain ⟨h1, h2, h3⟩ := ldLkpShift_num g v f b hf hb
  let Pd : ℕ → E → Prop := fun Y θ =>
    Y / 2 ^ d ≠ f ∧ key f b + tag f * θ = tab (Y / 2 ^ d) (Y % 2 ^ d) + tag (Y / 2 ^ d) * θ
  have hsub : cnt (fun θ : E => InTable (g + v) (g + d) (shKey v key tag θ) (shTab d tab tag θ)) ≤
      cnt (fun θ : E => ∃ Y ∈ range (2 ^ (g + d)), Pd Y θ) := by
    refine cnt_mono fun θ hθ => ?_
    obtain ⟨Y, hY, he⟩ := hθ _ h1
    unfold shKey shTab at he
    rw [h2, h3] at he
    refine ⟨Y, mem_range.2 hY, fun hj => ?_, he⟩
    rw [hj] at he
    exact hout _ (ldLkpShift_split g d Y hY).2 (add_right_cancel he)
  refine hsub.trans ((cnt_exists_mem_le _ _).trans ?_)
  have hone : ∀ Y ∈ range (2 ^ (g + d)), cnt (Pd Y) ≤ 1 := by
    intro Y hY
    refine cnt_le_one fun θ θ' h h' => ?_
    have hne : tag f - tag (Y / 2 ^ d) ≠ 0 := fun h0 =>
      h.1 (hT _ hf _ (ldLkpShift_split g d Y (mem_range.1 hY)).1 (sub_eq_zero.1 h0)).symm
    have e : (tag f - tag (Y / 2 ^ d)) * (θ - θ') = 0 := by linear_combination h.2 - h'.2
    exact sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_left hne)
  calc ∑ Y ∈ range (2 ^ (g + d)), cnt (Pd Y) ≤ ∑ _Y ∈ range (2 ^ (g + d)), 1 := sum_le_sum hone
    _ = 2 ^ (g + d) := by simp

theorem ldLkpShift_goodAt : Spec.ldLkpShift_goodAt := by
  intro E _ _ St M Wp Kc Ex P R0 hT
  refine goodAt_draw Kc M St (St × E) Ex Wp E Prod.mk (P.jIn R0) (P.jOut R0) (2 ^ (P.g + P.d)) ?_
    (fun _ _ _ h => h) (fun _ => rfl) ?_
  · intro x y w θ h
    exact ⟨h.1, ldLkpShift_fwd E P.g P.v P.d _ _ P.tag θ h.2⟩
  · intro x y m _
    by_cases hin : P.inC x m
    · refine le_trans (le_of_eq (cnt_false ?_)) (Nat.zero_le _)
      rintro θ ⟨wp, h, hn⟩
      exact hn ⟨h.1, hin⟩
    · refine (cnt_mono ?_).trans (ldLkpShift_cnt E P.g P.v P.d (P.key x m) (P.tab x) P.tag hT hin)
      rintro θ ⟨wp, h, _⟩
      exact h.2

theorem ldLkpShift_goodB : Spec.ldLkpShift_goodB := fun E _ _ S St Wp Kc E₀ P R0 hT =>
  sigLift_goodB E S Kc _ _ Wp Wp E₀ E₀ _ _ _ _ _ _ (ldLkpShift_goodAt E St S.Msg Wp Kc E₀ P R0 hT)

end Cb
