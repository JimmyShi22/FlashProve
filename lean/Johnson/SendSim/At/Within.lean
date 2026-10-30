-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/At/Within.lean: if the job fits its place and the queried positions are within the
bound budAt, the instance's list of queries asksOf is within the model's bound Sender.Within. The
proof of Spec.withinOf.
Terms: Johnson/SendSim/At/Sim.lean; for Within, Johnson/SendSim/Defs.lean; sender, asksOf, treeOf:
Johnson/SendSim/At/Bridge.lean. Limits of the folder: Johnson/SendSim/Defs.lean.

What this file proves. Lists and finite sets, and that a position's evaluation point depends on the
position modulo the code's length; no distribution is named.
  withinOf     Spec.withinOf, the statement of the title, written out in
               Johnson/SendSim/At/Bridge.lean. The proof does not use the first premise.
  mem_ptsOf    A point that the list asksOf queries of a row ρ is the evaluation point of a position
               that is queried of the tree of ρ's oracle message.
  card_map_le  A list has at most as many distinct images under h ∘ g as under g.

How it fits. Johnson/SendSim/At/JoinRows.lean uses withinOf as the premise Within of sendExact and
sendFresh, for rowsExact (Johnson/SendSim/At/RowsExact.lean) and rowsFresh
(Johnson/SendSim/At/RowsFresh.lean). The proof rests on point_mod (Johnson/SendSim/Tie/Point.lean).
-/
import Johnson.SendSim.At.Bridge

set_option autoImplicit false

namespace OnBytes.SendSim.At
open ProofFile.Honest ProofFile.Honest.K1 OnBytes OnBytes.Slice VerifiableInference.Desc
open Johnson.Prover.Send (Rows shapeAt)

/-- A list has at most as many distinct images under h ∘ g as under g. -/
theorem card_map_le {α β γ : Type} [DecidableEq β] [DecidableEq γ] (L : List α) (g : α → β)
    (h : β → γ) : ((L.map fun a => h (g a)).toFinset).card ≤ ((L.map g).toFinset).card := by
  have e : (L.map fun a => h (g a)).toFinset = ((L.map g).toFinset).image h := by
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨g a, ⟨a, ha, rfl⟩, rfl⟩
    · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, rfl⟩
  rw [e]
  exact Finset.card_image_le

variable (P : K1.Par) (ride : Nat → Option Ride)

open Classical in
/-- A point that the list asksOf P asks queries of the row ρ is the evaluation point, in the row's
code, of a position queried of the tree of ρ's oracle message. -/
theorem mem_ptsOf (asks : List (List (List Nat))) (ρ : RowN P) (x : GF)
    (hx : x ∈ (sender P ride).ptsOf (asksOf P asks) ρ) :
    ∃ τ, treeOf P ρ.1 = some τ ∧ ∃ p ∈ asked asks τ, x = ptF (codeAt P ρ).a p := by
  unfold Sender.ptsOf at hx
  rw [List.mem_toFinset, List.mem_map] at hx
  obtain ⟨a, ha0, rfl⟩ := hx
  rw [List.mem_filter] at ha0
  obtain ⟨hmem, hρ0⟩ := ha0
  have hρ : a.1 = ρ := of_decide_eq_true hρ0
  unfold asksOf at hmem
  obtain ⟨ρ', -, ha⟩ := (List.mem_flatMap (α := RowN P) (β := RowN P × GF)).1 hmem
  cases hτ : treeOf P ρ'.1 with
  | none =>
    rw [hτ] at ha
    cases ha
  | some τ =>
    rw [hτ] at ha
    simp only [List.mem_map] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    have e : ρ' = ρ := hρ
    subst e
    exact ⟨τ, hτ, p, hp, rfl⟩

open Classical in
/-- Proof of Spec.withinOf. The premise that the job fits its place is not used. -/
theorem withinOf : Spec.withinOf := by
  intro P ride asks _ hb ρ
  cases hτ : treeOf P ρ.1 with
  | none =>
    have e : (sender P ride).ptsOf (asksOf P asks) ρ = ∅ := by
      refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
      obtain ⟨τ, h, -⟩ := mem_ptsOf P ride asks ρ x hx
      rw [hτ] at h
      cases h
    rw [e]
    exact Nat.zero_le _
  | some τ =>
    have hsub : (sender P ride).ptsOf (asksOf P asks) ρ ⊆
        ((asked asks τ).map fun p => ptF (codeAt P ρ).a (p % 2 ^ (codeAt P ρ).a)).toFinset := by
      intro x hx
      obtain ⟨τ', h, p, hp, rfl⟩ := mem_ptsOf P ride asks ρ x hx
      rw [hτ] at h
      cases h
      rw [List.mem_toFinset, List.mem_map]
      exact ⟨p, hp, by unfold ptF; rw [point_mod]⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans
      (card_map_le (asked asks τ) (· % 2 ^ (codeAt P ρ).a) (ptF (codeAt P ρ).a)) ?_)
    have hk := hb ρ.1 τ ρ.1.isLt hτ
    obtain ⟨k, v⟩ := ρ
    rcases v with ⟨r, t⟩ | ⟨r, t⟩
    · convert hk.1 (fun h0 => by
        have h1 : r.val < (shapeAt P k).mainRows := r.isLt
        have h2 : (shapeAt P k).mainRows = 0 := h0
        omega) using 2
    · convert hk.2 (fun h0 => by
        have h1 : r.val < (shapeAt P k).maskRows := r.isLt
        have h2 : (shapeAt P k).maskRows = 0 := h0
        omega) using 2

end OnBytes.SendSim.At

#print axioms OnBytes.SendSim.At.withinOf
