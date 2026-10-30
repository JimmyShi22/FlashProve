-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/Weights.lean: the weights of the encoded index's rows read as the equality
vector at gamma.

Main names: eqTable_val (entry j of eqTable z reads as eqK at z, under every reading), eqTable_size,
weights_val, weights_size.

What is not claimed. Every equation is between readings, not between the program's words.

-/
import Johnson.Desc.K14.Law.Tensors

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params Desc.Plain
open OnBytes.Model (Reading)

variable {K : Type} [Field K] (ρ : Reading K)

/-- One coordinate more: the table's entries times 1 - x, then its entries times x. -/
def tableStep (out : List E) (x : E) : List E :=
  List.zipWith subE out (out.map fun w => mulE w x) ++ out.map fun w => mulE w x

/-- The table as a list. -/
theorem eqTable_toList (z : List E) : (eqTable z).toList = z.foldl tableStep [oneE] := by
  unfold eqTable
  have h : ∀ (z : List E) (out : Array E),
      (z.foldl (fun (out : Array E) x =>
        let hi := out.map fun w => mulE w x
        (Array.zipWith subE out hi) ++ hi) out).toList = z.foldl tableStep out.toList := by
    intro z
    induction z with
    | nil => intro out; rfl
    | cons x z ih =>
      intro out
      rw [List.foldl_cons, List.foldl_cons, ih]
      congr 1
      simp [tableStep]
  exact h z #[oneE]

/-- What holds of the table behind the coordinates a. -/
def TableAt (a : List E) (out : List E) : Prop :=
  out.length = 2 ^ a.length ∧
    ∀ j < 2 ^ a.length, ρ.val (out.getD j zeroE) = eqK (a.map ρ.val) j

/-- One coordinate more keeps it. -/
theorem tableAt_step (a out : List E) (x : E) (h : TableAt ρ a out) :
    TableAt ρ (a ++ [x]) (tableStep out x) := by
  obtain ⟨hl, hv⟩ := h
  have hlen : (tableStep out x).length = 2 ^ (a ++ [x]).length := by
    simp only [tableStep, List.length_append, List.length_zipWith, List.length_map, hl,
      Nat.min_self, List.length_cons, List.length_nil]
    rw [Nat.pow_succ]; omega
  refine ⟨hlen, fun j hj => ?_⟩
  have hp : (a.map ρ.val).length = a.length := List.length_map _
  rw [List.map_append, eqK_append, hp]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add,
    Nat.pow_succ] at hj
  by_cases hjn : j < 2 ^ a.length
  · have h1 : (tableStep out x).getD j zeroE =
        subE (out.getD j zeroE) (mulE (out.getD j zeroE) x) := by
      have hjo : j < out.length := by rw [hl]; exact hjn
      simp [tableStep, List.getD_eq_getElem?_getD, List.getElem?_append_left, hjo,
        List.getElem?_zipWith]
    rw [h1, ρ.sub, ρ.mul, hv j hjn, Nat.div_eq_of_lt hjn]
    simp [eqK]
    ring
  · have hjo : j - 2 ^ a.length < out.length := by rw [hl]; omega
    have h1 : (tableStep out x).getD j zeroE = mulE (out.getD (j - 2 ^ a.length) zeroE) x := by
      have hz : (List.zipWith subE out (out.map fun w => mulE w x)).length = 2 ^ a.length := by
        simp [hl]
      simp only [tableStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by rw [hz]; omega), hz]
      simp [hjo]
    have h2 : eqK (a.map ρ.val) j = eqK (a.map ρ.val) (j - 2 ^ a.length) := by
      have := eqK_add_mul (a.map ρ.val) (j - 2 ^ a.length) 1
      rw [hp, Nat.mul_one, Nat.sub_add_cancel (by omega)] at this
      exact this
    have h3 : j / 2 ^ a.length = 1 := by
      rw [Nat.div_eq_iff (Nat.two_pow_pos _)]
      omega
    rw [h1, ρ.mul, hv _ (by omega), h2, h3]
    simp [eqK]

/-- So do coordinates one after the other. -/
theorem tableAt_foldl (z : List E) : ∀ (a out : List E), TableAt ρ a out →
    TableAt ρ (a ++ z) (z.foldl tableStep out) := by
  induction z with
  | nil => intro a out h; simpa using h
  | cons x z ih =>
    intro a out h
    have := ih (a ++ [x]) (tableStep out x) (tableAt_step ρ a out x h)
    simpa using this

/-- It holds of the table at z. -/
theorem tableAt_eqTable (z : List E) : TableAt ρ z (eqTable z).toList := by
  rw [eqTable_toList]
  have h0 : TableAt ρ [] [oneE] := ⟨rfl, fun j hj => by
    have : j = 0 := by simpa using hj
    subst this
    simp [eqK, ρ.one]⟩
  simpa using tableAt_foldl ρ z [] [oneE] h0

/-- The table has 2 ^ (the number of coordinates) entries. -/
theorem eqTable_size (z : List E) : (eqTable z).size = 2 ^ z.length := by
  have := (tableAt_eqTable Reading.gl z).1
  simpa using this

/-- **Entry j of the table reads as the equality vector's entry j.** -/
theorem eqTable_val (z : List E) (j : Nat) (hj : j < 2 ^ z.length) :
    ρ.val ((eqTable z).getD j zeroE) = eqK (z.map ρ.val) j := by
  have := (tableAt_eqTable ρ z).2 j hj
  simpa [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD] using this

/-- The weights of the encoded index's rows. -/
theorem weights_val (S : LinShape) (l : Lin) (r : Nat) (hr : r < 2 ^ (gamma S l).length) :
    ρ.val ((weights S l).getD r zeroE) = eqK ((gamma S l).map ρ.val) r :=
  eqTable_val ρ _ r hr

end Desc.K14.Law
