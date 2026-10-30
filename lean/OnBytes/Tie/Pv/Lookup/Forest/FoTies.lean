-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoTies.lean: the fields of the value forA, written out one by one in
functions of Forest.Shape; general in h.

 (a) One public quantity, one description: the functions of FoNums are those of Port (rfl), of which
     the statements on the shift speak.
 (b) The sizes are Shape.v, Shape.d and what forestSize hands to the planner.
 (c) key, tab and bAt in FoNums' keyOf, rowOf, cellOf; the entry that is no cell reads 0 by the
     value of zext; no mask place is that entry.
 (d) The orders, as lists of variables, are the terms that Forest.pad passes to Forest.level
     (orderForestRange, orderDefault), and the reversal at the leaves and the bits.
 (e) The letter oK is not idle: the last key level's order is neither the identity nor the reversal,
     at every h with FoNums.ok h.

Main theorems: tie_fK, tie_fT, tie_several, tie_pads, tie_size, tie_plan, tie_v, tie_key, tie_tab,
tie_bAt_cell, tie_bAt_none, tie_masks_some, tie_oK, tie_oT, tie_oE, tie_oB, tie_degE,
set_last_ne_rev, set_last_ne_one.
Limits: (b) and (d) reach functions of the verifier (OnBytes/Model/, OnBytes/Params/). (a) and (c)
reach FoNums' and Port's own descriptions, which no statement compares with what Forest.pad,
Forest.join or Forest.planesAt (OnBytes/Model/Look.lean) compute. That the terms of (d) are those
in the text of Forest.pad is a reading of that text, not a statement. Of the ten families of mask
places nothing is stated but the last clause of (c).
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoHole

set_option autoImplicit false

namespace Cb.Fo
open Iop Prob Hiop IOR Cb Cb.LdLkp Cb.Lkp

/-! ### (a) -/
example : FoNums.nOf = Port.nOf := rfl
example : FoNums.kOf = Port.kOf := rfl
example : FoNums.t0Of = Port.t0Of := rfl
example : FoNums.io = Port.io := rfl
example : FoNums.fst = Port.fst := rfl
example : FoNums.co = Port.co := rfl
theorem tie_fK : FoNums.fK = Port.fK := rfl
theorem tie_fT : FoNums.fT = Port.fT := rfl
theorem tie_several : FoNums.several = Port.several := rfl
theorem tie_pads : FoNums.pads = Port.pads := rfl

/-! ### (b) -/
theorem tie_size (h : Sh) : OnBytes.Model.forestSize h = ⟨h.v, h.d, FoNums.several h⟩ := rfl
theorem tie_plan (h : Sh) : OnBytes.Params.planForest (OnBytes.Model.forestSize h) =
    OnBytes.Params.planLookup { v := h.v, d := h.d, mu := FoNums.w, shifted := FoNums.several h } :=
        rfl

section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh)
    (L : Lay E St₀ J₀)

theorem tie_v (H : FoNums.ok h = true) : (forA E h L).v' + 1 = h.dT + h.rK := (ok_v H).symm
theorem tie_d : (forA E h L).d = h.kT + h.cK := rfl
theorem tie_w : ((forA E h L).w, (forA E h L).n) = (5, 30) := rfl
theorem tie_St : (forA E h L).St = (St₀ × E) := rfl
theorem tie_J : (forA E h L).J = Option J₀ := rfl
theorem tie_padsA : (forA E h L).pads = Port.pads h := rfl

/-! ### (c) -/
theorem tie_key (st : St₀) (θ : E) (μ : Option J₀ → E) (X : ℕ) :
    (forA E h L).key (st, θ) μ X =
      match FoNums.keyOf h X with
      | some ci => L.K st (fun j => μ (some j)) ci.1 ci.2 + (ci.1 : E) * θ
      | none => (FoNums.tauN h 0 (FoNums.t0Of h 0) : E) + ((0 : ℕ) : E) * θ := by
  show Port.key h (forT E h st) (forK E L st μ) X + ((Port.fK h X : ℕ) : E) * θ = _
  unfold Port.key Port.fK FoNums.keyOf
  by_cases hl : X % 2 ^ h.rK < h.NT
  · rw [if_pos hl, if_pos hl, if_pos hl]
    rfl
  · rw [if_neg hl, if_neg hl, if_neg hl]
    rfl

theorem tie_tab (st : St₀) (θ : E) (u : ℕ) :
    (forA E h L).tab (st, θ) u =
        (FoNums.tauN h (FoNums.rowOf h u).1 (FoNums.rowOf h u).2 : E) + ((FoNums.rowOf h u).1 : E) *
        θ := rfl

theorem tie_bAt_cell (u j : ℕ) (hc : u % 2 ^ h.cK < h.NC) :
    (forA E h L).bAt u j = some (L.bc (u / 2 ^ h.cK) (u % 2 ^ h.cK) j) := by
  show (FoNums.cellOf h u j).map _ = _
  unfold FoNums.cellOf
  rw [if_pos hc]
  rfl

/-- from NC on: the entry that is no cell; it reads 0 by zext's value, whatever the entries are -/
theorem tie_bAt_none (u j : ℕ) (hc : ¬ u % 2 ^ h.cK < h.NC) (μ : J₀ → E) :
    (forA E h L).bAt u j = none ∧ zext μ ((forA E h L).bAt u j) = 0 := by
  have e : (forA E h L).bAt u j = none := by
    show (FoNums.cellOf h u j).map _ = _
    unfold FoNums.cellOf
    rw [if_neg hc]
    rfl
  exact ⟨e, by rw [e]; rfl⟩

/-- no mask place is the entry that is no cell -/
theorem tie_masks_some :
    (forA E h L).cZ ≠ none ∧ (forA E h L).cB ≠ none ∧ (∀ j b, (forA E h L).cAt j b ≠ none) ∧
    (∀ l b, (forA E h L).cK l b ≠ none) ∧ (∀ l b, (forA E h L).cT l b ≠ none) ∧
        (∀ j i, (forA E h L).wAt j i ≠ none) ∧
    (∀ l i, (forA E h L).wK l i ≠ none) ∧ (∀ l i, (forA E h L).wT l i ≠ none) ∧
        (∀ i, (forA E h L).wE i ≠ none) ∧ ∀ i, (forA E h L).wB i ≠ none :=
  ⟨nofun, nofun, fun _ _ => nofun, fun _ _ => nofun, fun _ _ => nofun, fun _ _ => nofun, fun _ _ =>
      nofun, fun _ _ => nofun, fun _ => nofun, fun _ => nofun⟩

end

/-! ### (d) the orders as lists of variables -/

theorem asList_perm (k : ℕ) (l : List ℕ) (hp : l.Perm (List.range k)) :
    E3.asList (E3.permOfList k l hp) = l := by
  have hl : l.length = k := by rw [hp.length_eq, List.length_range]
  refine List.ext_getElem (by simp [E3.asList, hl]) fun i h1 h2 => ?_
  simp only [E3.asList, List.getElem_map, List.getElem_finRange]
  rfl

theorem asList_default (k : ℕ) : E3.asList (E3.ordDefault k) = OnBytes.Model.orderDefault k := by
  rw [E3.ordDefault_eq, asList_perm]
  rfl

theorem asList_forOK (h : Sh) (hd : 10 ≤ h.dT) (k : ℕ) :
    E3.asList (forOK h k) = FoNums.ordK h k := by
  unfold forOK FoNums.ordK
  rw [dif_pos hd]
  by_cases e : k + 1 = h.v
  · rw [if_pos e, E3.ordKeys_last h.dT h.rK hd k e]
    exact asList_perm _ _ _
  · rw [if_neg e, E3.ordKeys_other h.dT h.rK hd k e]
    exact asList_default k

theorem ordE_default (h : Sh) : FoNums.ordE h = OnBytes.Model.orderDefault (FoNums.w + h.d) := by
  unfold FoNums.ordE OnBytes.Model.orderDefault FoNums.placeOf
  refine List.ext_getElem (by simp) fun i h1 h2 => ?_
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getElem_reverse, List.length_range]

section
variable (E : Type) [Field E] [Fintype E] {St₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀] (h : Sh)
    (L : Lay E St₀ J₀)

/-- The key levels: round j of level l binds the variable in place j of the verifier's list. -/
theorem tie_oK (H : FoNums.ok h = true) (l : ℕ) :
    E3.asList ((forA E h L).oK l) =
      if (0 + l) + 1 = h.v then OnBytes.Model.Forest.orderForestRange (0 + l) h.rK else
          OnBytes.Model.orderDefault (0 + l) :=
  asList_forOK h (ok_parts H).1.1 (0 + l)
/-- The table levels. -/
theorem tie_oT (l : ℕ) :
    E3.asList ((forA E h L).oT l) = OnBytes.Model.orderDefault (5 + l) := asList_default _
/-- The leaves, the bits: the verifier walks the point's array from place 0 up, so round j binds
variable k - 1 - j. -/
theorem tie_oE :
    E3.asList (forA E h L).oE = FoNums.ordE h := (asList_default _).trans (ordE_default h).symm
theorem tie_oB :
    E3.asList (forA E h L).oB = FoNums.ordB h := (asList_default _).trans (ordE_default h).symm
/-- the leaves' degrees by round: the d rows' variables first (2), then the five planes' (1) -/
theorem tie_degE :
    List.ofFn (forA E h L).En.dg = List.replicate h.d 2 ++ List.replicate 5 1 := dgEnd_rev FoNums.w
    h.d

/-! ### (e) -/

/-- the first round of the last key level binds variable rK + 2 -/
theorem last_first (H : FoNums.ok h = true) :
    (E3.asList ((forA E h L).oK (FoNums.v' h))).head? = some (h.rK + 2) := by
  rw [tie_oK E h L H, if_pos (by rw [ok_v H]; omega)]
  rfl

theorem set_last_ne_rev (H : FoNums.ok h = true) : (forA E h L).oK (FoNums.v' h) ≠ Fin.revPerm := by
  intro e
  have h1 := last_first E h L H
  rw [e] at h1
  have h2 : E3.asList (Fin.revPerm : Equiv.Perm (Fin (0 + FoNums.v' h))) =
      OnBytes.Model.orderDefault (0 + FoNums.v' h) := asList_default _
  rw [h2] at h1
  have a1 := (ok_parts H).1.1
  have hv := ok_v H
  have hv2 : h.v = h.dT + h.rK := rfl
  obtain ⟨m, hm⟩ : ∃ m, 0 + FoNums.v' h = m + 1 := ⟨FoNums.v' h - 1, by omega⟩
  rw [hm] at h1
  unfold OnBytes.Model.orderDefault at h1
  rw [List.range_succ, List.reverse_append] at h1
  simp at h1
  omega

theorem set_last_ne_one (H : FoNums.ok h = true) : (forA E h L).oK (FoNums.v' h) ≠ 1 := by
  intro e
  have h1 := last_first E h L H
  rw [e] at h1
  have a1 := (ok_parts H).1.1
  have hv := ok_v H
  have hv2 : h.v = h.dT + h.rK := rfl
  obtain ⟨m, hm⟩ : ∃ m, 0 + FoNums.v' h = m + 1 := ⟨FoNums.v' h - 1, by omega⟩
  have h3 : ∀ k, (E3.asList (1 : Equiv.Perm (Fin (k + 1)))).head? = some 0 := by
    intro k
    simp [E3.asList, List.finRange_succ]
  rw [hm, h3] at h1
  simp at h1

end
end Cb.Fo
