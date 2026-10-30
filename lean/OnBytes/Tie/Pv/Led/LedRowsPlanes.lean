-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Led/LedRowsPlanes.lean: the three claims of a layer sub-proof's lookup that read the
planes name entries of the array of the reads alone.

Main names.
  rowsIn_U3at: an entry that Env.U3at (OnBytes/Model/LayerForms.lean) returns lies in the array
    v.iU3.
  rowsIn_foldlM: a sum by List.foldlM in Option, each of whose steps keeps RowsIn.
  rowsIn_planesAtO, rowsIn_countO, rowsIn_planeFormsO: the three forms (LedWalkPlanes.lean).
  rowsIn_planesL: each form of planesL v fo names entries of v.iU3 alone, if the start form of the
    leaves' sumcheck does (it is bare: gives_pad, LedRowsLook.lean).

RowsIn: LedRowsOf.lean.

What this file does not claim. That planesL has a value.


-/
import OnBytes.Tie.Pv.Led.LedWalkPlanes
import OnBytes.Tie.Pv.Led.LedRowsPsc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows
open OnBytes.Model OnBytes.Model.Layer

/-- An entry of the array of the reads. -/
theorem rowsIn_U3at {v : Env} {t i : Nat} {f : Aff} (h : v.U3at t i = some f) :
    RowsIn (fun a _ => a = v.iU3) f := by
  unfold Env.U3at at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · obtain rfl := Option.some.inj h
      exact rowsIn_ent _ rfl
    · cases h

theorem rowsIn_planeCol {v : Env} {t x : Nat} {f : Aff} (h : planeCol v t x = some f) :
    RowsIn (fun a _ => a = v.iU3) f := by
  unfold planeCol at h
  split at h
  · exact rowsIn_U3at h
  · cases h

variable {Q : Nat → Nat → Prop}

/-- A sum by List.foldlM in Option. -/
theorem rowsIn_foldlM {α : Type} (step : Aff → α → Option Aff)
    (hs : ∀ f x f', RowsIn Q f → step f x = some f' → RowsIn Q f') :
    ∀ (l : List α) (f f' : Aff), RowsIn Q f → l.foldlM step f = some f' → RowsIn Q f'
  | [], f, f', h, e => by
    rw [List.foldlM_nil] at e
    obtain rfl := Option.some.inj e
    exact h
  | x :: l, f, f', h, e => by
    rw [List.foldlM_cons] at e
    cases hx : step f x with
    | none => simp [hx] at e
    | some f1 =>
      have e2 : l.foldlM step f1 = some f' := by simpa [hx] using e
      exact rowsIn_foldlM step hs l f1 f' (hs f x f1 h hx) e2

theorem rowsIn_planesAtO {g : Forest.Heard} {lm e : Nat} {bit : Nat → Nat → Option Aff}
    (hb : ∀ e x f, bit e x = some f → RowsIn Q f) {a : Aff}
    (h : planesAtO g lm e bit = some a) : RowsIn Q a := by
  unfold planesAtO at h
  refine rowsIn_foldlM _ (fun f col f' hf hq => ?_) _ _ _ (rowsIn_ofConst _) h
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp hq
  obtain rfl := Option.some.inj e2
  exact rowsIn_addMul _ hf (hb e col x hx)

theorem rowsIn_countO {g : Forest.Heard} {lm : Nat} {pin : Nat → Option Aff}
    (hp : ∀ x f, pin x = some f → RowsIn Q f) {a : Aff} (h : countO g lm pin = some a) :
    RowsIn Q a := by
  unfold countO at h
  refine rowsIn_foldlM _ (fun f col f' hf hq => ?_) _ _ _ (rowsIn_ofConst _) h
  obtain ⟨x, hx, e2⟩ := Option.bind_eq_some_iff.mp hq
  obtain rfl := Option.some.inj e2
  exact rowsIn_add hf (hp col x hx)

theorem rowsIn_planeFormsO {g : Forest.Heard} {lm : Nat} {bit : Nat → Nat → Option Aff}
    {pin : Nat → Option Aff} (hs : RowsIn Q g.leaves.start)
    (hb : ∀ e x f, bit e x = some f → RowsIn Q f) (hp : ∀ x f, pin x = some f → RowsIn Q f)
    {rows : Array Aff} (h : planeFormsO g lm bit pin = some rows) :
    ∀ f ∈ rows.toList, RowsIn Q f := by
  unfold planeFormsO at h
  obtain ⟨at0, h0, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨at1, h1, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨count, h2, e⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj e
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl
  · exact rowsIn_rowForm _ _ hs (rowsIn_scale _ (rowsIn_planesAtO hb h0))
  · exact rowsIn_sub (rowsIn_slot _) (rowsIn_planesAtO hb h1)
  · exact rowsIn_countO hp h2

/-- The three claims that read the planes. -/
theorem rowsIn_planesL {v : Env} {fo : Forest.Heard} {l : List Aff}
    (hs : RowsIn (fun a _ => a = v.iU3) fo.leaves.start) (h : planesL v fo = some l) :
    ∀ f ∈ l, RowsIn (fun a _ => a = v.iU3) f := by
  unfold planesL at h
  obtain ⟨tB0, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tB1, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨tP, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨rows, h3, e⟩ := Option.bind_eq_some_iff.mp h
  obtain rfl := Option.some.inj e
  exact rowsIn_planeFormsO hs (fun _ _ _ hq => rowsIn_planeCol hq)
    (fun _ _ hq => rowsIn_planeCol hq) h3

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.rowsIn_U3at
#print axioms OnBytes.Road.Rows.rowsIn_planesL
