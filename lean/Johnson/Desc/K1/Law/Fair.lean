-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Fair.lean: a message reads the first seeds of a place's joint seeds, and of each
point the first coordinates: every seed of the message comes from equally many joint seeds.

Main names: Rest, partSeeds (an equivalence), cnt_part, card_part.

What is not claimed. Nothing on how seeds are drawn from a hash. No verifier is named.

-/
import Johnson.Desc.K1.Law.SaysTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open Prob

section
variable {X B : Type} (n a v v' : Nat)

/-- What a message does not read of the joint seeds: the later seeds whole; of the first seeds the
later coordinates. -/
abbrev Rest (X B : Type) (n a v v' : Nat) : Type :=
  ({i : Fin n // a ≤ i.val} → (Fin v → X) × B) ×
    ({i : Fin n // i.val < a} → {t : Fin v // v' ≤ t.val} → X)

/-- The joint seeds, parted: what the message reads, and the rest. -/
def partSeeds (ha : a ≤ n) (hv : v' ≤ v) :
    (Fin n → (Fin v → X) × B) ≃ (Fin a → (Fin v' → X) × B) × Rest X B n a v v' where
  toFun ρ :=
    (fun i => (fun t => (ρ ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩).1
        ⟨t.val, Nat.lt_of_lt_of_le t.isLt hv⟩, (ρ ⟨i.val, Nat.lt_of_lt_of_le i.isLt ha⟩).2),
      (fun i => ρ i.1, fun i t => (ρ i.1).1 t.1))
  invFun x := fun i =>
    if h : i.val < a then
      (fun t => if h' : t.val < v' then (x.1 ⟨i.val, h⟩).1 ⟨t.val, h'⟩
        else x.2.2 ⟨i, h⟩ ⟨t, Nat.le_of_not_lt h'⟩, (x.1 ⟨i.val, h⟩).2)
    else x.2.1 ⟨i, Nat.le_of_not_lt h⟩
  left_inv ρ := by
    funext i
    by_cases h : i.val < a
    · simp only [dif_pos h]
      refine Prod.ext (funext fun t => ?_) rfl
      by_cases h' : t.val < v'
      · simp only [dif_pos h']
      · simp only [dif_neg h']
    · simp only [dif_neg h]
  right_inv x := by
    refine Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
      (funext fun i => funext fun t => ?_))
    · have h : i.val < a := i.isLt
      simp only [dif_pos h]
      refine Prod.ext (funext fun t => ?_) rfl
      have h' : t.val < v' := t.isLt
      simp only [dif_pos h']
    · have h : ¬ i.1.val < a := Nat.not_lt.2 i.2
      simp only [dif_neg h]
    · have h : i.1.val < a := i.2
      have h' : ¬ t.1.val < v' := Nat.not_lt.2 t.2
      simp only [dif_pos h, dif_neg h']

variable [Fintype X] [Fintype B]

/-- A property of what the message reads holds at as many joint seeds as it holds at seeds of the
message, times the number of rests. -/
theorem cnt_part (ha : a ≤ n) (hv : v' ≤ v) (Q : (Fin a → (Fin v' → X) × B) → Prop) :
    cnt (fun ρ : Fin n → (Fin v → X) × B => Q (partSeeds n a v v' ha hv ρ).1) =
      cnt Q * Fintype.card (Rest X B n a v v') := by
  rw [← cnt_fst (D := Rest X B n a v v') Q]
  exact cnt_equiv (partSeeds n a v v' ha hv) fun x => Q x.1

/-- The numbers of seeds multiply. -/
theorem card_part (ha : a ≤ n) (hv : v' ≤ v) :
    Fintype.card (Fin n → (Fin v → X) × B) =
      Fintype.card (Fin a → (Fin v' → X) × B) * Fintype.card (Rest X B n a v v') := by
  rw [Fintype.card_congr (partSeeds n a v v' ha hv), Fintype.card_prod]

end

end VerifiableInference.Desc.K1
