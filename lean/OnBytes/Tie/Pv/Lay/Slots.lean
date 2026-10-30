-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/Slots.lean: the model's counts of the slots that a sumcheck takes, as closed
formulas.

In the model a hidden scalar lies under a slot, and entry j of a sub-proof's mask row belongs to
slot j. The functions `sumcheckSlots`, `layerSlots`, `wsForkSlots`, `tscSlots` and `slotsOf`
(OnBytes/Model/Rounds.lean, Tsc.lean, Merge.lean, LayerPlan.lean) count the slots.

Main names:
  `sumcheckSlots_eq2`, `_sum2`, `_sum3`, `_nodes`, `_eq`, `layerSlots_eq`, `wsForkSlots_eq`,
    `tscSlots_eq`: the numbers of slots as closed formulas.
  `powers_length`, `walk_length`: the linear form of the hiding polynomial (`hidingWalk`) has
    `hidingEntries` members, if every weight has at least one coefficient and there is a variable.
  `entries_three`: `hidingEntries` of n variables with three coefficients each and a last one with
    dy + 1 is 1 + 2 n + dy.
  `layer_split`, `merge_split`, `tsc_split`: a sumcheck's slots are as many as its hiding
    coefficients and its end values together; in a sumcheck over the token positions there is one
    more.
  `slotsOf_eq`: the model's count of the slots of a layers' sub-proof, written out with these
    formulas.

Limits: that the model's routines take these numbers of slots is not shown here. Nothing is said
on what a slot hides.
-/
import OnBytes.Model.Merge
import OnBytes.Model.Tsc
import OnBytes.Model.LayerPlan

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Lay
open OnBytes OnBytes.Model OnBytes.Psc

theorem sumcheckSlots_eq2 (n e dy d : Nat) : sumcheckSlots .eq2 n e dy d = 1 + 2 * n + dy + e := by
  simp only [sumcheckSlots, roundValues]; omega

theorem sumcheckSlots_sum2 (n e dy d : Nat) : sumcheckSlots .sum2 n e dy d = 1 + 2 * n + dy + e :=
    by
  simp only [sumcheckSlots, roundValues]; omega

theorem sumcheckSlots_sum3 (n e dy d : Nat) : sumcheckSlots .sum3 n e dy d = 1 + 3 * n + dy + e :=
    by
  simp only [sumcheckSlots, roundValues]; omega

theorem sumcheckSlots_nodes (n e dy d : Nat) : sumcheckSlots .nodes n e dy d = 1 + n * d + dy + e
    := by
  simp only [sumcheckSlots, roundValues]

theorem sumcheckSlots_eq (n e dy d : Nat) : sumcheckSlots .eq n e dy d = 1 + n * d + dy + e := by
  simp only [sumcheckSlots, roundValues]

theorem layerSlots_eq (mu : Nat) : layerSlots mu = 2 * mu + 5 := by
  simp only [layerSlots, sumcheckSlots_eq2]; omega

theorem wsForkSlots_eq (lk : Nat) : wsForkSlots lk = 2 * lk + 3 := by
  simp only [wsForkSlots, sumcheckSlots_sum2]; omega

theorem tscSlots_eq (lt shown dy more : Nat) : tscSlots lt shown dy more = 2 * (lt + more) + dy +
    shown + 2 := by
  simp only [tscSlots, sumcheckSlots_eq2]; omega

theorem powersLoop_length (x : E) : ∀ (n : Nat) (c : E) (done : List E),
    (OnBytes.Psc.powersLoop x n c done).length = n + done.length
  | 0, _, done => by simp [OnBytes.Psc.powersLoop]
  | n + 1, c, done => by
      rw [OnBytes.Psc.powersLoop, powersLoop_length x n (mulE c x) (c :: done), List.length_cons];
          omega

theorem powers_length (c x : E) (n : Nat) : (OnBytes.Psc.powers c x n).length = n := by
  simp [OnBytes.Psc.powers, powersLoop_length]

/-- The hiding polynomial's linear form has as many members as the model counts coefficients. -/
theorem walk_length : ∀ l : List (Weight × E), l ≠ [] → (∀ p ∈ l, 1 ≤ p.1.d) →
    (hidingWalk l).1.length = hidingEntries (l.map (·.1))
  | [], h, _ => absurd rfl h
  | [(w, g)], _, hd => by
      have h1 : 1 ≤ w.d := hd (w, g) (List.mem_singleton.mpr rfl)
      simp only [hidingWalk, powers_length, hidingEntries, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil]
      omega
  | (w, g) :: q :: rest, _, hd => by
      have ih := walk_length (q :: rest) (List.cons_ne_nil _ _) (fun p hp => hd p
          (List.mem_cons_of_mem _ hp))
      simp only [hidingWalk, List.length_append, powers_length, ih, hidingEntries, List.map_cons,
          List.sum_cons]
      omega

/-- n variables with three coefficients each, then one with dy + 1. -/
theorem entries_three (ws : List Weight) (last : Weight) (dy : Nat) (h3 : ∀ w ∈ ws, w.d = 3)
    (hl : last.d = dy + 1) : hidingEntries (ws ++ [last]) = 1 + 2 * ws.length + dy := by
  induction ws with
  | nil => simp [hidingEntries, hl]
  | cons w ws ih =>
      have hw : w.d = 3 := h3 w (List.mem_cons_self ..)
      have := ih (fun v hv => h3 v (List.mem_cons_of_mem _ hv))
      simp only [hidingEntries, List.cons_append, List.map_cons, List.sum_cons, List.length_cons,
          hw] at this ⊢
      omega

theorem layer_split (ws : List Weight) (h3 : ∀ w ∈ ws, w.d = 3) :
    layerSlots ws.length = hidingEntries (ws ++ [Weight.atZero 3]) + 2 := by
  rw [layerSlots_eq, entries_three ws (Weight.atZero 3) 2 h3 rfl]; omega

theorem merge_split (ws : List Weight) (h3 : ∀ w ∈ ws, w.d = 3) :
    wsForkSlots ws.length = hidingEntries (ws ++ [Weight.atZero 2]) + 1 := by
  rw [wsForkSlots_eq, entries_three ws (Weight.atZero 2) 1 h3 rfl]; omega

theorem tsc_split (ws : List Weight) (h3 : ∀ w ∈ ws, w.d = 3) (shown dy : Nat) :
    tscSlots ws.length shown dy = 1 + hidingEntries (ws ++ [Weight.atZero (dy + 1)]) + shown := by
  rw [tscSlots_eq, entries_three ws (Weight.atZero (dy + 1)) dy h3 rfl]; omega

/-- the weights that the model's rounds make have three coefficients -/
theorem eq2_d (z : E) : ∀ w, RoundForm.weight .eq2 z = some w → w.d = 3 := by
  intro w h; simp [RoundForm.weight, RoundForm.degreeOK, RoundForm.equality, roundValues] at h; rw
      [← h]; rfl

theorem sum2_d : ∀ w, RoundForm.weight .sum2 = some w → w.d = 3 := by
  intro w h; simp [RoundForm.weight, RoundForm.degreeOK, RoundForm.equality, roundValues] at h; rw
      [← h]; rfl

open OnBytes.Model.Layer in
/-- The model's count of the slots of a layers' sub-proof, with the closed formulas. -/
theorem slotsOf_eq (y : Lay) (rd : Reads) (g lk small : Nat) :
    slotsOf y rd g lk small =
      Forest.elems y.fo + ledNS y.h.xl * y.NI + (2 * rd.muV + 5) + ledNP y.h.xl * y.NI +
        (2 * (y.h.lt + 0) + 2 + ledNO y.h.xl * y.NI + 2) +
        (if rd.tscCalls.isEmpty then 0 else 2 * (y.h.lt + 0) + 1 + shownByTerms y rd + 2) +
        (1 + 2 * lamSOf y + 2 +
          (2 + 1 + (if y.h.p3 then y.LamM else 0) + nclOf y g - (if g == 0 then 1 else 0))) +
        (2 * rd.muH + 5) + (if y.h.p3 then 2 * rd.muH2 + 5 else 0) + (if g == 0 then 1 else 0) +
        (2 * lk + 3) + small := by
  simp only [slotsOf, layerSlots_eq, wsForkSlots_eq, tscSlots_eq, sumcheckSlots_sum2]

-- at two sizes
example : layerSlots 26 = 57 ∧ layerSlots 18 = 41 ∧ layerSlots 24 = 53 ∧ layerSlots 16 = 37 :=
    ⟨rfl, rfl, rfl, rfl⟩
example : wsForkSlots 18 = 39 ∧ wsForkSlots 11 = 25 := ⟨rfl, rfl⟩
example : ledNS 5 * 8 = 72 ∧ ledNP 5 * 8 = 56 := ⟨rfl, rfl⟩

#print axioms sumcheckSlots_eq2
#print axioms layerSlots_eq
#print axioms wsForkSlots_eq
#print axioms tscSlots_eq
#print axioms walk_length
#print axioms entries_three
#print axioms layer_split
#print axioms merge_split
#print axioms tsc_split
#print axioms eq2_d
#print axioms sum2_d
#print axioms slotsOf_eq

end OnBytes.Tie.Pv.Lay
