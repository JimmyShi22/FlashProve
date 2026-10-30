-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Listed.lean: lists of the end values' names in the order of the library's
numberings exist.

Main names:
  `listed_exists`: a numbering that is one-to-one and onto the numbers below N has a Listed list of
    length N.
  `sc3_listed`: at sc3Num (a sumcheck of products: twice as many end values as pairs).
  `scd_listed`: at scdNum (the key at the index).

Sources: Att/K05ReadAs.lean; OnBytes/Tie/Pv/Att/Sc3Top.lean, Flat.lean.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05ReadAs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Cb.Pv.Att
open OnBytes.Tie.Pv.Att (sc3Num sc3Num_lt scdNum scdNum_lt)

theorem listed_exists {A : Type} (num : A → ℕ) (N : ℕ) (hi : Function.Injective num)
    (hs : ∀ j, j < N → ∃ a, num a = j) (hl : ∀ a, num a < N) : ∃ sh : List A, Listed sh num ∧ sh.length = N := by
  classical
  let f : Fin N → A := fun j => Classical.choose (hs j.1 j.2)
  have hf : ∀ j : Fin N, num (f j) = j.1 := fun j => Classical.choose_spec (hs j.1 j.2)
  refine ⟨List.ofFn f, ⟨?_, fun a => ?_⟩, by simp⟩
  · refine List.nodup_ofFn.2 fun i j h => Fin.ext ?_
    rw [← hf i, ← hf j, h]
  · rw [List.getElem?_ofFn]
    rw [dif_pos (hl a)]
    exact congrArg some (hi (hf ⟨num a, hl a⟩))

theorem sc3_listed (nb : ℕ) : ∃ sh : List (Fin nb × Bool), Listed sh sc3Num ∧ sh.length = 2 * nb := by
  refine listed_exists sc3Num (2 * nb) (fun a b h => ?_) (fun j hj => ?_) sc3Num_lt
  · obtain ⟨⟨a1, ha⟩, a2⟩ := a
    obtain ⟨⟨b1, hb⟩, b2⟩ := b
    unfold sc3Num at h
    simp only at h
    cases a2 <;> cases b2 <;> simp at h <;> first | (subst h; rfl) | omega
  · refine ⟨(⟨j / 2, by omega⟩, Decidable.decide (j % 2 = 1)), ?_⟩
    unfold sc3Num
    simp only
    by_cases h : j % 2 = 1
    · simp [h]; omega
    · simp [h]; omega

theorem scd_listed (s : ScdSize) : ∃ sh : List s.A, Listed sh (scdNum s) ∧ sh.length = s.Lam + s.pairs * s.lt := by
  refine listed_exists (scdNum s) (s.Lam + s.pairs * s.lt) (fun a b h => ?_) (fun j hj => ?_) (scdNum_lt s)
  · rcases a with ⟨a, ha⟩ | ⟨⟨a1, ha1⟩, ⟨a2, ha2⟩⟩ <;> rcases b with ⟨b, hb⟩ | ⟨⟨b1, hb1⟩, ⟨b2, hb2⟩⟩
    · have e : a = b := h
      subst e
      rfl
    · have e : a = s.Lam + b1 * s.lt + b2 := h
      omega
    · have e : s.Lam + a1 * s.lt + a2 = b := h
      omega
    · have e : s.Lam + a1 * s.lt + a2 = s.Lam + b1 * s.lt + b2 := h
      have e' : a2 + s.lt * a1 = b2 + s.lt * b1 := by
        rw [Nat.mul_comm s.lt a1, Nat.mul_comm s.lt b1]
        omega
      have q1 : a1 = b1 := by
        have := congrArg (· / s.lt) e'
        simp only at this
        rwa [Nat.add_mul_div_left _ _ (by omega), Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt ha2,
          Nat.div_eq_of_lt hb2, Nat.zero_add, Nat.zero_add] at this
      subst q1
      have q2 : a2 = b2 := by omega
      subst q2
      rfl
  · by_cases h : j < s.Lam
    · exact ⟨.inl ⟨j, h⟩, rfl⟩
    · have hlt : 0 < s.lt := by
        rcases Nat.eq_zero_or_pos s.lt with h0 | h0
        · rw [h0] at hj
          omega
        · exact h0
      refine ⟨.inr (⟨(j - s.Lam) / s.lt, ?_⟩, ⟨(j - s.Lam) % s.lt, Nat.mod_lt _ hlt⟩), ?_⟩
      · exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
      · show s.Lam + (j - s.Lam) / s.lt * s.lt + (j - s.Lam) % s.lt = j
        have := Nat.div_add_mod (j - s.Lam) s.lt
        rw [Nat.mul_comm] at this
        omega

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.scd_listed
#print axioms VerifiableInference.Desc.First.Att.P.sc3_listed
