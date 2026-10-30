-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/GateLists.lean: the entries of the verifier's two tables of the gate (gateTables,
OnBytes/Model/LayerTables.lean:217) as functions of one power of e^(1/256), and that power as a
recursion.

gateTables reads the powers out of an array of 32,769 numbers (expPowers). Lean's kernel holds an
array as a list, so reading entry a costs a steps. Here:
  powers_get: entry a of expPowers eg n is xAt u a fxOne (Johnson/Meaning/RopeLists.lean), the a-th
    step of "x to x u / 2^320" from 2^320, with u the series' value.
  siluOf x a neg, sigOf x neg: the words of siluWord and sigmoidAt from the power x alone.
  siluWord_eq, sigmoidAt_eq: the verifier's words are these, at the power that the array holds.
General in the array. Nothing is evaluated here.
-/
import Johnson.Meaning.RopeLists

set_option autoImplicit false

namespace Meaning.Gate

open OnBytes.Model.Layer (fxOne roundD roundHalfUp expSeries fxPowersLoop expPowers onePlusExp
  siluWord sigmoidAt)
open Meaning.Rope (xAt)

/-- What fxPowersLoop appends. -/
theorem loop_spec (u : Nat) : ∀ (n x : Nat) (a : Array Nat),
    (fxPowersLoop u n x a).size = a.size + n ∧
    (∀ j, j < a.size → (fxPowersLoop u n x a).getD j fxOne = a.getD j fxOne) ∧
    ∀ j, j < n → (fxPowersLoop u n x a).getD (a.size + j) fxOne = xAt u j x
  | 0, x, a => ⟨rfl, fun _ _ => rfl, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  | n + 1, x, a => by
    have e : fxPowersLoop u (n + 1) x a = fxPowersLoop u n (x * u / fxOne) (a.push x) := rfl
    obtain ⟨i1, i2, i3⟩ := loop_spec u n (x * u / fxOne) (a.push x)
    rw [e]
    have hs : (a.push x).size = a.size + 1 := Array.size_push _
    refine ⟨by rw [i1, hs]; omega, fun j hj => ?_, fun j hj => ?_⟩
    · rw [i2 j (by rw [hs]; omega)]
      simp [Array.getD, hj, Nat.lt_succ_of_lt hj, Array.getElem_push_lt]
    · cases j with
      | zero =>
        rw [Nat.add_zero, i2 a.size (by rw [hs]; omega)]
        simp [Array.getD, xAt]
      | succ j =>
        have y := i3 j (by omega)
        rw [hs] at y
        have e2 : a.size + (j + 1) = a.size + 1 + j := by omega
        rw [e2, y]
        rfl

/-- The series' value: e^(1 / 2^eg) in fixed-point. -/
def stepOf (eg : Nat) : Nat := expSeries (2 ^ eg) 400 1 fxOne fxOne

/-- Entry a of the array of powers. -/
theorem powers_get (eg n : Nat) {a : Nat} (ha : a ≤ n) :
    (expPowers eg n).getD a fxOne = xAt (stepOf eg) a fxOne := by
  have y := (loop_spec (stepOf eg) (n + 1) fxOne (Array.emptyWithCapacity (n + 1))).2.2 a
    (by omega)
  have e0 : (Array.emptyWithCapacity (n + 1) : Array Nat).size = 0 := by simp
  rw [e0, Nat.zero_add] at y
  exact y

/-- 1 + exp(-z) from the power x. -/
def oneExp (x : Nat) (neg : Bool) : Nat × Nat :=
  let e := if neg then roundD x fxOne else roundD fxOne x
  roundD (e.2 + e.1) e.2

/-- The word of the table SILU at the distance a from the middle, from the power x. -/
def siluOf (eg smax x a : Nat) (neg : Bool) : Nat :=
  let s := oneExp x neg
  let v := min (roundHalfUp 64 (roundD (a * s.2) (2 ^ eg * s.1))) smax
  if neg then 4096 - v else 4096 + v

/-- The word of the sigmoid, from the power x. -/
def sigOf (x : Nat) (neg : Bool) : Nat :=
  let s := oneExp x neg
  16 * roundHalfUp 1 (roundD (4096 * s.2) s.1)

/-- The distance from the middle at which siluWord reads. -/
def distS (eg t : Nat) : Nat :=
  if t < 32768 then min (32768 - t) (64 * 2 ^ eg) else min (t - 32768) (64 * 2 ^ eg - 1)

theorem siluWord_eq (eg smax : Nat) (X : Array Nat) (t : Nat) :
    siluWord eg smax X t =
      siluOf eg smax (X.getD (distS eg t) fxOne) (distS eg t) (decide (t < 32768)) := by
  unfold siluWord siluOf oneExp onePlusExp distS
  by_cases h : t < 32768 <;> simp [h]

theorem sigmoidAt_eq (X : Array Nat) (t : Nat) :
    sigmoidAt X t =
      sigOf (X.getD (if t < 32768 then 32768 - t else t - 32768) fxOne) (decide (t < 32768)) := by
  unfold sigmoidAt sigOf oneExp onePlusExp
  by_cases h : t < 32768 <;> simp [h]

#print axioms powers_get
#print axioms siluWord_eq
#print axioms sigmoidAt_eq

end Meaning.Gate
