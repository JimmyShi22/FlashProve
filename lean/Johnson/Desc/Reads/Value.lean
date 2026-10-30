-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/Value.lean: a form's part in U3 (`u3Value`, Reads/Stated.lean) through the value
of a form in a world (`Aff.value`, OnBytes/Model/HideLaws.lean).

All of this file is a tool: it holds for all forms, readings and values, and names no description of
the protocol.

Why. The tie of the uses to the text, clause (T) of Reads/Stated.lean, is an equality of linear
forms on U3. A kind's forms are written with sums and multiples, and the laws of `Aff.value` under
these are at hand. Here `u3Value` is brought to `Aff.value`, so that (T) can be shown of a form by
these laws, without a look at the list of its entries.

What is here.
  `worldOf iU3 cols v`: the world in which v stands at the places of array number iU3, by the rule
    of `placeOf`, and 0 at every other entry and under every slot.
  `u3Value_eq`: at a reading, `u3Value` is the form's value in that world less its constant.
  `u3Value_diff`: it is the form's value in that world less its value in the world of v = 0.
  `value_place`: the form "entry x / cols, x % cols of array iU3" has the value v x there.
  `ents_sum`, `slots_sum`, `u3Value_zero`: steps.

Of OnBytes/Model/ this file names the records `Aff`, `Ent`, `Reading` and `World`, and the measures
`Aff.value`, `Ent.value` and `slotValue` of OnBytes/Model/HideLaws.lean. It names no routine of that
program.

Limits. `worldOf` takes the number of an entry's row for the vector's own row, as `placeOf` does:
see the limits of Reads/Stated.lean on virtual rows. Nothing on soundness.


-/
import Johnson.Desc.Reads.Stated
import OnBytes.Model.HideLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes (E)
open OnBytes.Model (Aff Ent Reading World slotValue)

variable {K : Type} [CommRing K]

/-- The world in which v stands at the places of array number iU3, and 0 everywhere else. -/
def worldOf (iU3 cols : ℕ) (v : ℕ → K) : World K :=
  ⟨fun _ => 0, fun tr row idx => if tr = iU3 then v (row * cols + idx) else 0⟩

variable (ρ : Reading K) (iU3 cols : ℕ) (v : ℕ → K)

/-- The entries' values in that world: those of array iU3 alone count. -/
theorem ents_sum (l : List Ent) :
    (l.map (Ent.value ρ (worldOf iU3 cols v))).sum =
      (((l.filter fun x => x.tree == iU3).map fun x => (placeOf cols x, ρ.val x.coef)).map
        fun p => p.2 * v p.1).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    by_cases h : x.tree = iU3
    · have hb : (x.tree == iU3) = true := beq_iff_eq.2 h
      have e : Ent.value ρ (worldOf iU3 cols v) x = ρ.val x.coef * v (placeOf cols x) := by
        show ρ.val x.coef * (if x.tree = iU3 then v (x.row * cols + x.idx) else 0) = _
        rw [if_pos h]
        rfl
      rw [List.filter_cons, if_pos hb, List.map_cons, List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, ih, e]
    · have hb : ¬ (x.tree == iU3) = true := fun hb => h (beq_iff_eq.1 hb)
      have e : Ent.value ρ (worldOf iU3 cols v) x = 0 := by
        show ρ.val x.coef * (if x.tree = iU3 then v (x.row * cols + x.idx) else 0) = 0
        rw [if_neg h, mul_zero]
      rw [List.filter_cons, if_neg hb, List.map_cons, List.sum_cons, ih, e, zero_add]

/-- The slots count for nothing there. -/
theorem slots_sum (l : List (ℕ × E)) :
    (l.map (slotValue ρ (worldOf iU3 cols v))).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have e : slotValue ρ (worldOf iU3 cols v) x = 0 := by
      show ρ.val x.2 * 0 = 0
      rw [mul_zero]
    rw [List.map_cons, List.sum_cons, ih, e, add_zero]

/-- **A form's part in U3 is its value in that world, less its constant.** -/
theorem u3Value_eq (f : Aff) :
    u3Value ρ.val iU3 cols f v = f.value ρ (worldOf iU3 cols v) - ρ.val f.const := by
  unfold u3Value entsU3 Aff.value
  rw [ents_sum, slots_sum, add_zero, add_sub_cancel_right]

/-- At v = 0 a form's part in U3 is 0. -/
theorem u3Value_zero (val : E → K) (f : Aff) : u3Value val iU3 cols f (fun _ => 0) = 0 := by
  unfold u3Value
  generalize entsU3 val iU3 cols f = l
  induction l with
  | nil => rfl
  | cons p l ih => rw [List.map_cons, List.sum_cons, ih, mul_zero, add_zero]

/-- **It is the form's value in that world less its value where 0 stands at every place.** -/
theorem u3Value_diff (f : Aff) :
    u3Value ρ.val iU3 cols f v =
      f.value ρ (worldOf iU3 cols v) - f.value ρ (worldOf iU3 cols fun _ => 0) := by
  have h0 := u3Value_eq ρ iU3 cols (fun _ => 0) f
  rw [u3Value_zero] at h0
  have h1 := u3Value_eq ρ iU3 cols v f
  rw [h1]
  have h2 : f.value ρ (worldOf iU3 cols fun _ => 0) = ρ.val f.const := (sub_eq_zero.1 h0.symm)
  rw [h2]

/-- The entry of array iU3 at the place x, written with x / cols and x % cols, has the value v x. -/
theorem value_place (x : ℕ) :
    (Aff.ent iU3 (x / cols) (x % cols)).value ρ (worldOf iU3 cols v) = v x := by
  rw [Aff.value_ent]
  show (if iU3 = iU3 then v (x / cols * cols + x % cols) else 0) = v x
  rw [if_pos rfl, Nat.div_add_mod']

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.ents_sum
#print axioms VerifiableInference.Reads.slots_sum
#print axioms VerifiableInference.Reads.u3Value_eq
#print axioms VerifiableInference.Reads.u3Value_zero
#print axioms VerifiableInference.Reads.u3Value_diff
#print axioms VerifiableInference.Reads.value_place
