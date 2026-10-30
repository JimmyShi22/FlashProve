-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLkpMultProofs.lean: the proofs of the statements of Cb/Ld/LdLkpMult.lean (which vectors of
multiplicities make a lookup complete, when the table is a multiset).
The order: sums over a range that is a product; the idle positions; the claim after the first
challenge, by grouping keys and entries by their values; the random shift; the honest vector of
Cb/Gen/LkpAlg.lean.
Nothing is defined here that a statement reads.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names (statements and hypotheses: Cb/Ld/LdLkpMult.lean):
  `ldLkpMult_idle`: `Valid` ⇒ the table's product at an idle position: 1, at every challenge.
  `ldLkpMult_mid`: every key in the table, W ≤ 2^w, `Valid` ⇒ the claim after the first challenge
    (`Cb.Lkp.Mid`), at every challenge.
  `ldLkpMult_shift`: valid bits laid side by side (`shBit`): valid for the random shift's joint keys
    and table.
  `ldLkpMult_honest`: the honest bits of Cb/Gen/LkpAlg.lean: valid (2^n < 2^W, every key in the
    table).

Limits: what the head of Cb/Ld/LdLkpMult.lean lists as not said is not said here either.

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLkpMult
import Cb.Ld.LdLkpShiftProofs
import Cb.Gen.LkpAlgProofs

set_option autoImplicit false

namespace Cb
open Finset Cb.Lkp Cb.LdLkp

theorem ldLkpMult_sum_mul {α : Type} [AddCommMonoid α] (B A : ℕ) (G : ℕ → α) :
    ∑ Y ∈ range (B * A), G Y = ∑ f ∈ range A, ∑ u ∈ range B, G (B * f + u) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

/-- a sum over a joint numbering (Y / 2^d, Y % 2^d), as a double sum -/
theorem ldLkpMult_sum_split {α : Type} [AddCommMonoid α] (g d : ℕ) (G : ℕ → ℕ → α) :
    ∑ Y ∈ range (2 ^ (g + d)), G (Y / 2 ^ d) (Y % 2 ^ d) =
      ∑ f ∈ range (2 ^ g), ∑ u ∈ range (2 ^ d), G f u := by
  have hp : 0 < 2 ^ d := Nat.pos_of_ne_zero (by positivity)
  rw [pow_add, Nat.mul_comm, ldLkpMult_sum_mul]
  refine sum_congr rfl fun f _ => sum_congr rfl fun u hu => ?_
  rw [Nat.mul_add_div hp, Nat.mul_add_mod, Nat.div_eq_of_lt (mem_range.1 hu),
    Nat.mod_eq_of_lt (mem_range.1 hu), Nat.add_zero]

theorem ldLkpMult_idle : Spec.ldLkpMult_idle := by
  intro E _ n T w W key t M hV al j hW hj
  unfold tabProd
  refine prod_eq_one fun u hu => ?_
  rw [hV.2.1 u (mem_range.1 hu) j hW hj, zero_mul, add_zero]

theorem ldLkpMult_mid : Spec.ldLkpMult_mid := by
  classical
  intro E _ n T w W key t M hW hin hV al
  have hk : ∀ b ∈ range (2 ^ n), key b ∈ (range (2 ^ T)).image t := fun b hb => by
    obtain ⟨u, hu, he⟩ := hin b (mem_range.1 hb)
    exact mem_image.2 ⟨u, mem_range.2 hu, he.symm⟩
  have ht : ∀ u ∈ range (2 ^ T), t u ∈ (range (2 ^ T)).image t := fun u hu => mem_image_of_mem t hu
  have hval : ∀ x : E, ∑ u ∈ (range (2 ^ T)).filter (fun u => t u = x), multOf W M u =
      ((range (2 ^ n)).filter fun b => key b = x).card := fun x => by
    convert hV.2.2 x
  refine ⟨hV.1, ?_, ?_⟩
  · have hsum : ∑ u ∈ range (2 ^ T), multOf W M u = 2 ^ n := by
      rw [← sum_fiberwise_of_maps_to ht, sum_congr rfl fun x _ => hval x,
        ← card_eq_sum_card_fiberwise hk, card_range]
    unfold NumKeys
    rw [sum_bits_fin T W M (fun u j => decide (M u j = 1)) fun u hu j hj =>
          eq_ite_of_bit (hV.1 u hu j (lt_of_lt_of_le hj hW)),
      Alg.Lookup.sum_bits_eq W (fun (u : Fin (2 ^ T)) j => decide (M u j = 1))]
    congr 1
    rw [← hsum, sum_range]
    rfl
  · rw [planes E T w W t M al hW hV.1]
    unfold keyProd
    rw [← prod_fiberwise_of_maps_to hk, ← prod_fiberwise_of_maps_to ht]
    refine prod_congr rfl fun x _ => ?_
    rw [prod_congr rfl fun b hb => by rw [(mem_filter.1 hb).2], prod_const,
      prod_congr rfl fun u hu => by rw [(mem_filter.1 hu).2], prod_pow_eq_pow_sum, hval x]

theorem ldLkpMult_shift : Spec.ldLkpMult_shift := by
  classical
  intro E _ g v d w W key tab tag M h θ
  refine ⟨fun Y hY j hj => ?_, fun Y hY j hW hj => ?_, fun x => ?_⟩
  · exact (h _ (ldLkpShift_split g d Y hY).1).1 _ (ldLkpShift_split g d Y hY).2 j hj
  · exact (h _ (ldLkpShift_split g d Y hY).1).2.1 _ (ldLkpShift_split g d Y hY).2 j hW hj
  · have hval : ∀ f ∈ range (2 ^ g), ∑ u ∈ range (2 ^ d),
          (if tab f u + tag f * θ = x then multOf W (M f) u else 0) =
        ∑ b ∈ range (2 ^ v), if key f b + tag f * θ = x then 1 else 0 := by
      intro f hf
      have h0 := (h f (mem_range.1 hf)).2.2 (x - tag f * θ)
      rw [card_filter, sum_filter] at h0
      simp only [eq_sub_iff_add_eq] at h0
      convert h0
    rw [card_filter, sum_filter]
    have e1 :=
      ldLkpMult_sum_split g d fun f u => if tab f u + tag f * θ = x then multOf W (M f) u else 0
    have e2 := ldLkpMult_sum_split g v fun f b => if key f b + tag f * θ = x then 1 else 0
    exact (e1.trans (sum_congr rfl hval)).trans e2.symm

theorem ldLkpMult_multOf_hbit
    {E : Type} [Field E] (n W : ℕ) (key t : ℕ → E) (hW : 2 ^ n < 2 ^ W) (u : ℕ) :
    multOf W (hbit n W key t) u = hmult n key t u := by
  classical
  rw [← Alg.Lookup.mult_testBit W (fun u => hmult n key t u) u (hmult_lt n W key t hW u)]
  unfold multOf Alg.Lookup.mult
  refine sum_congr rfl fun j hj => ?_
  show (if decide (hbit n W key t u j = 1) = true then 2 ^ j else 0) =
    if (hmult n key t u).testBit j = true then 2 ^ j else 0
  rw [hbit_eq n W key t u (mem_range.1 hj)]
  cases (hmult n key t u).testBit j <;> simp

theorem ldLkpMult_honest : Spec.ldLkpMult_honest := by
  classical
  intro E _ n T w W key t hW hin
  refine ⟨honest_bits E n T w W key t, fun u _ j hj _ => ?_, fun x => ?_⟩
  · unfold hbit
    rw [if_neg fun h => absurd h.1 (not_lt.2 hj)]
  · have hex : ∀ b : Fin (2 ^ n), ∃ u, u < 2 ^ T ∧ key b = t u := fun b => hin b b.2
    have hA : ((range (2 ^ n)).filter fun b => key b = x).card =
        ((univ : Finset (Fin (2 ^ n))).filter fun b : Fin (2 ^ n) => key b = x).card := by
      rw [card_filter, card_filter, sum_range]
    have hmap : ∀ b ∈ (univ : Finset (Fin (2 ^ n))).filter (fun b : Fin (2 ^ n) => key b = x),
        Nat.find (hex b) ∈ (range (2 ^ T)).filter fun u => t u = x := fun b hb =>
      mem_filter.2 ⟨mem_range.2 (Nat.find_spec (hex b)).1,
        (Nat.find_spec (hex b)).2.symm.trans (mem_filter.1 hb).2⟩
    have hgoal : ∑ u ∈ (range (2 ^ T)).filter (fun u => t u = x), multOf W (hbit n W key t) u =
        ((range (2 ^ n)).filter fun b => key b = x).card := by
      rw [hA, card_eq_sum_card_fiberwise hmap]
      refine sum_congr rfl fun u hu => ?_
      rw [ldLkpMult_multOf_hbit n W key t hW u]
      unfold hmult
      congr 1
      ext b
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1.trans (mem_filter.1 hu).2, ?_⟩
        rw [Nat.find_eq_iff]
        exact ⟨⟨mem_range.1 (mem_filter.1 hu).1, h1⟩, fun u' hu' he => h2 u' hu' he.2⟩
      · rintro ⟨h1, h2⟩
        rw [Nat.find_eq_iff] at h2
        exact ⟨h2.1.2, fun u' hu' he => h2.2 u' hu' ⟨lt_trans hu' h2.1.1, he⟩⟩
    convert hgoal

end Cb
