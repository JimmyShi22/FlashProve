-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ZeroWorld.lean: the constant of a form of the verifier, from what the form is worth
on true reads: that worth, read at the world in which every hidden value is 0.

The library's theorems on the forms of a layers' sub-proof say what a form is WORTH in a world whose
tables of reads are true of cells c (`TrueAt`, Johnson/Road/FormsKeysFits.lean). A tie with a typed
sumcheck also asks for a NUMBER: the form's public part (Cb/Pv/Lay/At/Fore.lean's head: "the target
itself ... must be the public part of the programs' start form as a number"). A true entry of the
reads is a sum of cells under weights, with no constant of its own. So the world in which all hidden
values are 0 has true tables of the cells 0, and there a form is worth its constant.

  `zeroW`: that world. `value_zeroW`: in it a form is worth its constant.
  `shortTrue_zero`, `longTrue_zero`, `trueAt_zero`: its tables are true of the cells 0, at every
      environment and all points.
  `const_of_worth`: if a form is worth Φ c in every world whose tables are true of c, its constant
      reads as Φ at the cells 0.

Limits. An identity. It speaks of the six families of `TrueAt` alone. Nothing on a draw, on
soundness or on hiding.
-/
import Johnson.Road.FormsKeysFits
import Johnson.Road.FormsKeysTab

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Finset
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Env)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The world in which every hidden value is 0. -/
def zeroW : World K := ⟨fun _ => 0, fun _ _ _ => 0⟩

/-- In it a form is worth its constant. -/
theorem value_zeroW (a : Aff) : a.value ρ zeroW = ρ.val a.const := by
  unfold Aff.value
  have e1 : (a.ents.toList.map (Ent.value ρ zeroW)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      unfold Ent.value
      exact mul_zero _
  have e2 : (a.slots.toList.map (slotValue ρ zeroW)).sum = 0 :=
    List.sum_eq_zero fun x hx => by
      obtain ⟨y, _, rfl⟩ := List.mem_map.mp hx
      unfold slotValue
      exact mul_zero _
  rw [e1, e2, zero_add, zero_add]

variable {ρ}

theorem U3at_zero {v : Env} {tb e : ℕ} {a : Aff} (h : v.U3at tb e = some a) :
    a.value ρ zeroW = 0 := by
  obtain ⟨_, _, _, hv⟩ := U3at_entry ρ zeroW h
  rw [hv]
  rfl

theorem shortTrue_zero (v : Env) (tb mat lt : ℕ) (u : ℕ → K) :
    ShortTrue ρ zeroW v tb mat lt (fun _ _ _ => 0) u := fun _ _ h => by
  rw [U3at_zero h, Blocks.ext_zero_of_forall (fun _ _ => rfl)]

theorem longTrue_zero (v : Env) (tb mat ls lt : ℕ) (low u : ℕ → K) :
    LongTrue ρ zeroW v tb mat ls lt (fun _ _ _ => 0) low u := fun _ _ h => by
  rw [U3at_zero h]
  exact (sum_eq_zero fun r _ => by
    rw [Blocks.ext_zero_of_forall (fun _ _ => rfl), mul_zero]).symm

/-- **The zero world's tables are true of the cells 0.** -/
theorem trueAt_zero (v : Env) (lT : ℕ) (low u : ℕ → K) :
    TrueAt ρ zeroW v lT (fun _ _ _ => 0) low u where
  af := fun b _ => longTrue_zero v b 0 v.y.ls lT low u
  qa := fun b _ => longTrue_zero v b 3 v.y.ls lT low u
  xi := fun b _ => longTrue_zero v b 4 v.y.ls lT low u
  xo := fun b _ => longTrue_zero v b 5 v.y.ls lT low u
  ad := fun b _ => shortTrue_zero v b 1 lT u
  ar := fun b _ => shortTrue_zero v b 2 lT u

/-- **The constant, from the worth.** -/
theorem const_of_worth {v : Env} {lT : ℕ} {low u : ℕ → K} {f : Aff} {Φ : Cells K → K}
    (h : ∀ (W : World K) (c : Cells K), TrueAt ρ W v lT c low u → f.value ρ W = Φ c) :
    ρ.val f.const = Φ fun _ _ _ => 0 := by
  rw [← value_zeroW ρ f]
  exact h zeroW _ (trueAt_zero v lT low u)

#print axioms trueAt_zero
#print axioms const_of_worth

end OnBytes.Road.K4
