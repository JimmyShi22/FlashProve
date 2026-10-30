-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdWfToyProofs.lean: lemmas towards the conditions of `LdWfF.OK` (Cb/Ld/LdWfFull.lean) for the
data of the toy of weights-formedness (Cb/Ld/LdWfToy.lean), field by field; part 1: configuration,
places, keys, numbers, codes, sender.
The rest, and the statement, are in Cb/Ld/LdWfToyMasks.lean, under its hypothesis `It.OK`.

Limits: the theorems of this file that speak of the toy take the model (a relation pair Md with
`Md.OK` and countably many instances: class `WfToy.ToyModel`) as an instance argument (all but those
under `omit [WfToy.ToyModel] in`): so each of them holds for every model; where none is declared:
the trivial one. What follows for their reach is told under "Limits:" in the head of
Cb/Ld/LdWfToy.lean (from "The toy's relation pair"), and holds here too. Weights-formedness and the
test behind it do not read the relation pair (but for the conditions named there).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdWfToy

set_option autoImplicit false

namespace Cb

variable [WfToy.ToyModel]
namespace WfToy
open Iop Prob Hiop Blocks Cb.Ood IOR LdToy LdToy7 Cb.LdLkp Cb.Lkp

omit [WfToy.ToyModel] in
theorem btAt_inj : Function.Injective btAt := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective (Sum.inr_injective h))

omit [WfToy.ToyModel] in
theorem bit_ne (x : Ix) (i : WBt) : (Sum.inl x : Nm) ≠ btAt i := fun h => by cases h
omit [WfToy.ToyModel] in
theorem mk_ne (x : LkpToy.Mk) (i : WBt) : mkAt x ≠ btAt i := fun h => by cases h
omit [WfToy.ToyModel] in
theorem idle_ne (i : WBt) : idle ≠ btAt i := fun h => by cases h

omit [WfToy.ToyModel] in
theorem oneHot_inj {α : Type} [DecidableEq α] :
    Function.Injective fun (i j : α) => decide (j = i) := fun a b h => by
  have e := congrFun h a
  simp only [decide_true] at e
  exact of_decide_eq_true e.symm

omit [WfToy.ToyModel] in
theorem famHyp : F.Hyp 7 7 2 2 := (stdFam_toy7 Ix Im Ix Im _ _ oneHot_inj oneHot_inj).1

/-! ### The keys, the index set, the multiplicities -/

omit [WfToy.ToyModel] in
/-- Each of the two code rows is the column with a number: every c : Fin 1 → Bool is `Alg.bits 1` of
a number (0 or 1). -/
theorem row_eq (c : Fin 1 → Bool) : c = Alg.bits 1 ((if c 0 then 1 else 0) % 2) := by
  funext v
  obtain rfl : v = 0 := Subsingleton.elim _ _
  cases h : c 0 <;> simp [Alg.bits]

omit [WfToy.ToyModel] in
/-- Conditions that give `Valid 1 1 1 2` at the toy's numbers, for bits given as four values. -/
theorem valid_of (ky : ℕ → K) (M : ℕ → ℕ → K) (k0 k1 b00 b01 b10 b11 : K) (hk0 : ky 0 = k0)
    (hk1 : ky 1 = k1) (h00 : M 0 0 = b00) (h01 : M 0 1 = b01) (h10 : M 1 0 = b10)
    (h11 : M 1 1 = b11)
    (hb : b00 * (b00 - 1) = 0 ∧ b01 * (b01 - 1) = 0 ∧ b10 * (b10 - 1) = 0 ∧ b11 * (b11 - 1) = 0)
    (hs : ∀ x : K,
      (if (5 : K) = x then (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) else 0) +
          (if (7 : K) = x then (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) else 0) =
        (if k0 = x then 1 else 0) + (if k1 = x then 1 else 0)) : Valid 1 1 1 2 ky tab M := by
  classical
  refine ⟨?_, ?_, fun x => ?_⟩
  · intro u hu j hj
    have hu' : u < 2 := hu
    have hj' : j < 2 := hj
    interval_cases u <;> interval_cases j
    · rw [h00]; exact hb.1
    · rw [h01]; exact hb.2.1
    · rw [h10]; exact hb.2.2.1
    · rw [h11]; exact hb.2.2.2
  · intro u _ j h1 h2
    have h2' : j < 2 := h2
    omega
  · have e1 : (Finset.range (2 ^ 1)) = Finset.range 2 := rfl
    rw [e1, Finset.sum_filter, Finset.card_filter, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_zero, hk0, hk1]
    have m0 : multOf 2 M 0 = (if b00 = 1 then 1 else 0) + (if b01 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h00, h01]
      by_cases a : b00 = 1 <;> by_cases c : b01 = 1 <;> simp [a, c]
    have m1 : multOf 2 M 1 = (if b10 = 1 then 1 else 0) + (if b11 = 1 then 2 else 0) := by
      unfold multOf Alg.Lookup.mult
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      beta_reduce
      rw [h10, h11]
      by_cases a : b10 = 1 <;> by_cases c : b11 = 1 <;> simp [a, c]
    rw [m0, m1, show tab 0 = 5 from rfl, show tab 1 = 7 from rfl]
    have := hs x
    by_cases h5 : (5 : K) = x <;> by_cases h7 : (7 : K) = x <;> by_cases g0 : k0 = x
      <;> by_cases g1 : k1 = x
      <;> simp only [h5, h7, g0, g1, if_true, if_false, Nat.zero_add] at this ⊢ <;> exact this

end WfToy
end Cb
