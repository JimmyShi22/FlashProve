-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5K3R/SitsAddr.lean: the kind "lookup"'s fifty addresses against the table's two written
lists, at the full size: three facts, each decided by the kernel.

Why. A law at a seat of the kind is stated at letters: a list of segments, a list of places, a
number k, an address a, a sort of segment. Where it is called at the proof file's description these
are the full size's written lists and the driver's address. Here: what the lists hold there.

Main names:
  `k03_at_full`: number 14 l + i + 2 of the full list of places IS the driver's address of link l's
    lookup on the calls, or on the digits (the converse of `k03_places_full`).
  `k03_sub_full`: the list of segments has a sort at l, and by the table's own count (2 + o at the
    calls, 7 + o at the digits, o the sort's shift) the two addresses' pieces are the table's.

Limits: the full size's two written lists alone. Nothing on a record; nothing on soundness; nothing
on hiding.


-/
import Johnson.P5K3R.SitsKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace K3Lot

open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift flatPlacesOf)

/-- The test: each of the fifty numbers holds its address. -/
def k3HasB (ps : List Place) : Bool :=
  (List.range 25).all fun l => [false, true].all fun d =>
    decide (ps[14 * l + IM.k3Ix l d + 2]? = some (IM.k3Place l d))

set_option maxRecDepth 1000000 in
theorem k3HasB_full : k3HasB (flatPlacesOf linksFull true) = true := by decide +kernel

/-- **Each of the fifty numbers holds its address.** -/
theorem k03_at_full (l : ℕ) (hl : l < 25) (d : Bool) :
    (flatPlacesOf linksFull true)[14 * l + IM.k3Ix l d + 2]? = some (IM.k3Place l d) := by
  have h := List.all_eq_true.1 k3HasB_full l (List.mem_range.2 hl)
  exact of_decide_eq_true (List.all_eq_true.1 h d (by cases d <;> simp))

/-- The test: the two addresses' pieces are the table's, by the sort's shift. -/
def k3SubB (links : List ModelPart) : Bool :=
  (List.range 25).all fun l =>
    match links[l]? with
    | some sub =>
      (IM.k3Place l false).piece == 2 + shift sub && (IM.k3Place l true).piece == 7 + shift sub
    | none => false

theorem k3SubB_full : k3SubB linksFull = true := by decide +kernel

/-- **The addresses' pieces are the table's.** -/
theorem k03_sub_full (l : ℕ) (hl : l < 25) :
    ∃ sub, linksFull[l]? = some sub ∧ (IM.k3Place l false).piece = 2 + shift sub ∧
      (IM.k3Place l true).piece = 7 + shift sub := by
  have h := List.all_eq_true.1 k3SubB_full l (List.mem_range.2 hl)
  cases hs : linksFull[l]? with
  | none => rw [hs] at h; cases h
  | some sub =>
    rw [hs] at h
    obtain ⟨h1, h2⟩ := (Bool.and_eq_true _ _).mp h
    exact ⟨sub, rfl, by simpa using h1, by simpa using h2⟩

end K3Lot
