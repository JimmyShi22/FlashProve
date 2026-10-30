-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/Ends/AlgWcell.lean: two texts of the rule for a weight's cell. H.lean is
OnBytes/Tie/Pv/Lookup/Ends/H.lean.
States: (wcell_eq_cellOf) TWO TEXTS OF ONE RULE ARE ONE: H.lean's wcell (the cell of W that holds
digit δ of the weight of a unit with given indices, written after the verifier's takenAt) IS cellOf
(Johnson/Road/FormsKeysWm.lean), for every unit whose groups' numbers fit each other (GrpOK,
Johnson/Road/FormsKeysWOk.lean: a theorem for every unit of a layout that the verifier builds),
every digit and every list of indices.
Does not say: that the verifier's own settling of a claim on the weights reaches the cell cellOf
(Johnson/Road/FormsKeysWLay.lean's head says the same of cellOf).
-/
import Johnson.Road.FormsKeysWOk
import OnBytes.Tie.Pv.Lookup.Ends.H

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Alg

open OnBytes.Ends
open OnBytes.Model (WsGrp WsUnit)

/-- The t bits of n from bit c on, summed under their weights. -/
theorem bits_fold (n c : ℕ) : ∀ t : ℕ,
    (List.range t).foldl (fun s b => s + (n / 2 ^ (c + b) % 2) * 2 ^ b) 0 = n / 2 ^ c % 2 ^ t
  | 0 => by simp [Nat.mod_one]
  | t + 1 => by
    rw [List.range_succ, List.foldl_append, bits_fold n c t, Nat.mod_pow_succ]
    show n / 2 ^ c % 2 ^ t + n / 2 ^ (c + t) % 2 * 2 ^ t = _
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ t)]

/-- What a group leaves to the rows. -/
theorem rowPart_eq {g : WsGrp} (hg : GrpOK g) (v : ℕ) : H.rowPart g v = (splitG g v).2 := by
  unfold H.rowPart splitG
  rcases hg with ⟨hc, -, ht, -⟩ | ⟨hc, -, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hc]; rfl
    rw [if_pos hE, if_pos hE]
    have hz : (2 : ℕ) ^ g.z = 2 ^ g.t * 2 ^ (g.z - g.t) := by
      rw [← Nat.pow_add, Nat.add_sub_cancel' ht]
    cases hh : g.high with
    | true =>
      rw [if_pos rfl, if_pos rfl]
      show v / 2 ^ g.z * 2 ^ (g.z - g.t) + v % 2 ^ g.z % 2 ^ (g.z - g.t) =
        v / 2 ^ g.z * 2 ^ (g.z - g.t) + v % 2 ^ (g.z - g.t)
      rw [Nat.mod_mod_of_dvd v (Nat.pow_dvd_pow 2 (Nat.sub_le _ _))]
    | false =>
      rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true]
      show v / 2 ^ g.z * 2 ^ (g.z - g.t) + v % 2 ^ g.z / 2 ^ g.t = v / 2 ^ g.t
      rw [hz, Nat.mod_mul_right_div_self, ← Nat.div_div_eq_div_mul, Nat.div_add_mod']
  · have hE : ¬ (g.cls == 'E') = true := by rw [hc]; decide
    rw [if_neg hE, if_neg hE]
    split_ifs <;> rfl

/-- What a group gives to the columns. -/
theorem colPart_eq {g : WsGrp} (hg : GrpOK g) (v : ℕ) : H.colPart g v = (splitG g v).1 := by
  unfold H.colPart splitG
  rcases hg with ⟨hc, -, ht, -⟩ | ⟨hc, -, -⟩
  · have hE : (g.cls == 'E') = true := by rw [hc]; rfl
    rw [if_pos hE, if_pos hE]
    cases hh : g.high with
    | true =>
      rw [if_pos rfl]
      have e : (fun (s b : ℕ) => s + (v % 2 ^ g.z / 2 ^ g.takenAt b % 2) * 2 ^ b) =
          fun s b => s + (v % 2 ^ g.z / 2 ^ (g.z - g.t + b) % 2) * 2 ^ b := by
        funext s b
        unfold WsGrp.takenAt
        rw [hh, if_pos rfl]
      rw [e, bits_fold]
      show v % 2 ^ g.z / 2 ^ (g.z - g.t) % 2 ^ g.t = v / 2 ^ (g.z - g.t) % 2 ^ g.t
      have hz : (2 : ℕ) ^ g.z = 2 ^ (g.z - g.t) * 2 ^ g.t := by
        rw [← Nat.pow_add, Nat.sub_add_cancel ht]
      rw [hz, Nat.mod_mul_right_div_self, Nat.mod_mod]
    | false =>
      rw [if_neg Bool.false_ne_true]
      have e : (fun (s b : ℕ) => s + (v % 2 ^ g.z / 2 ^ g.takenAt b % 2) * 2 ^ b) =
          fun s b => s + (v % 2 ^ g.z / 2 ^ (0 + b) % 2) * 2 ^ b := by
        funext s b
        unfold WsGrp.takenAt
        rw [hh, if_neg Bool.false_ne_true, Nat.zero_add]
      rw [e, bits_fold]
      show v % 2 ^ g.z / 2 ^ 0 % 2 ^ g.t = v % 2 ^ g.t
      rw [Nat.pow_zero, Nat.div_one, Nat.mod_mod_of_dvd v (Nat.pow_dvd_pow 2 ht)]
  · have hE : ¬ (g.cls == 'E') = true := by rw [hc]; decide
    rw [if_neg hE, if_neg hE]
    split_ifs <;> rfl

/-- The row within the unit. -/
theorem rows_fold : ∀ (gi : List (WsGrp × ℕ)) (δ : ℕ), (∀ x ∈ gi, GrpOK x.1) →
    gi.foldr (fun x s => s * x.1.left + H.rowPart x.1 x.2) δ = rowIn gi δ
  | [], _, _ => rfl
  | (g, v) :: rest, δ, h => by
    show rest.foldr (fun x s => s * x.1.left + H.rowPart x.1 x.2) δ * g.left + H.rowPart g v =
      rowIn rest δ * g.left + (splitG g v).2
    rw [rows_fold rest δ (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      rowPart_eq (h (g, v) List.mem_cons_self)]

/-- The column. -/
theorem cols_fold : ∀ (gi : List (WsGrp × ℕ)) (a : ℕ), (∀ x ∈ gi, GrpOK x.1) →
    gi.foldl (fun s x => s + H.colPart x.1 x.2 * 2 ^ x.1.cb0) a = a + colIn gi
  | [], a, _ => rfl
  | (g, v) :: rest, a, h => by
    show rest.foldl (fun s x => s + H.colPart x.1 x.2 * 2 ^ x.1.cb0)
      (a + H.colPart g v * 2 ^ g.cb0) = a + ((splitG g v).1 * 2 ^ g.cb0 + colIn rest)
    rw [cols_fold rest _ (fun x hx => h x (List.mem_cons_of_mem _ hx)),
      colPart_eq (h (g, v) List.mem_cons_self), Nat.add_assoc]

/-- **The two texts of the rule are one.** -/
theorem wcell_eq_cellOf {u : WsUnit} (hu : ∀ g ∈ u.g, GrpOK g) (δ : ℕ) (idx : List ℕ) :
    H.wcell u δ idx = cellOf u δ idx := by
  have hz : ∀ x ∈ u.g.zip idx, GrpOK x.1 := fun x hx => hu x.1 (List.of_mem_zip hx).1
  unfold H.wcell cellOf
  show (u.off + (u.g.zip idx).reverse.foldl (fun s x => s * x.1.left + H.rowPart x.1 x.2) δ,
    (u.g.zip idx).foldl (fun s x => s + H.colPart x.1 x.2 * 2 ^ x.1.cb0) 0) = _
  rw [List.foldl_reverse, rows_fold _ δ hz, cols_fold _ 0 hz, Nat.zero_add]

#print axioms wcell_eq_cellOf

end OnBytes.Road.Alg
