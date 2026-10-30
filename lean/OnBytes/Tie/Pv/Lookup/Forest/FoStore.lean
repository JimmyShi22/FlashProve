-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoStore.lean.
What the rounds of a product tree's level leave in the array of challenges, and which coordinates of
the point they read.

The byte-level routine levelRounds (OnBytes/Model/Psc.lean) walks a list of variables. In the round
of variable v it reads place mu - 1 - v of the level's point and stores the round's challenge at the
same place of an array
of mu places. This file has that bookkeeping without the monad, for any type of elements:
* `stored mu order xs r`: the array after the rounds, from the challenges xs in the order of the
rounds.
* `stored_read`: if the order names each of the mu variables once, the array, read by any map f into
a commutative ring, is the flat function's point by coordinate (TwV.byVar) read backwards, whatever
stood in the array
  before. Further premises: there are mu challenges, and the array has mu places.
* `readAt_inRounds`: the coordinates that the rounds read, in the order of the rounds, are the flat
function's TwV.inRounds of the point read backwards. Premises: the order names variables below mu,
and the point's array has mu places.
* `down_read`: the point handed to the next level, the line's draw first, is the next point by
coordinate read backwards. Premise: the array of challenges, read, is the point by coordinate read
backwards.

Not claimed here: anything on the monad's run.

-/
import OnBytes.Tie.Pv.Lookup.Forest.FoPts

set_option autoImplicit false

namespace Fo
open TwV

section
variable {α : Type}

/-- The array of challenges after the rounds. -/
def stored (mu : ℕ) : List ℕ → List α → Array α → Array α
  | v :: o, x :: xs, r => stored mu o xs (r.set! (mu - 1 - v) x)
  | _, _, r => r

/-- The same on lists. -/
def storedL (mu : ℕ) : List ℕ → List α → List α → List α
  | v :: o, x :: xs, r => storedL mu o xs (r.set (mu - 1 - v) x)
  | _, _, r => r

theorem stored_toList (mu : ℕ) : ∀ (o : List ℕ) (xs : List α) (r : Array α),
    (stored mu o xs r).toList = storedL mu o xs r.toList
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | v :: o, x :: xs, r => by
    show (stored mu o xs (r.set! (mu - 1 - v) x)).toList = storedL mu o xs
        (r.toList.set (mu - 1 - v) x)
    rw [stored_toList mu o xs, Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds]

theorem storedL_length (mu : ℕ) : ∀ (o : List ℕ) (xs r : List α),
    (storedL mu o xs r).length = r.length
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | v :: o, x :: xs, r => by
    show (storedL mu o xs (r.set (mu - 1 - v) x)).length = _
    rw [storedL_length mu o xs, List.length_set]

/-- Place i after the rounds: the challenge of the round that names variable mu - 1 - i, if there is
one. -/
theorem storedL_get (mu : ℕ) : ∀ (o : List ℕ) (xs r : List α),
    o.Nodup → (∀ v ∈ o, v < mu) → o.length ≤ xs.length →
    r.length = mu → ∀ i < mu, (storedL mu o xs r)[i]? =
      if mu - 1 - i ∈ o then xs[o.idxOf (mu - 1 - i)]? else r[i]?
  | [], _, _, _, _, _, _, _, _ => by simp [storedL]
  | _ :: _, [], _, _, _, hl, _, _, _ => by simp at hl
  | v :: o, x :: xs, r, hn, hv, hl, hr, i, hi => by
    have hn' := List.nodup_cons.mp hn
    have hvm : v < mu := hv v (List.mem_cons_self)
    show (storedL mu o xs (r.set (mu - 1 - v) x))[i]? = _
    rw [storedL_get mu o xs _ hn'.2 (fun u hu => hv u (List.mem_cons_of_mem _ hu))
        (by simpa using hl)
      (by rw [List.length_set]; exact hr) i hi]
    by_cases e : mu - 1 - i = v
    · have hi' : mu - 1 - v = i := by omega
      rw [e, if_neg hn'.1, if_pos (List.mem_cons_self), List.idxOf_cons_self, hi',
          List.getElem?_set_self (by omega)]
      rfl
    · have hne : mu - 1 - v ≠ i := by omega
      have hne' : v ≠ mu - 1 - i := fun c => e c.symm
      by_cases hm : mu - 1 - i ∈ o
      · rw [if_pos hm, if_pos (List.mem_cons_of_mem _ hm), List.idxOf_cons_ne _ hne',
          List.getElem?_cons_succ]
      · rw [if_neg hm, if_neg (by simp [e, hm]), List.getElem?_set_ne hne]

end

section
variable {α K : Type} [CommRing K]

theorem stored_read (f : α → K) (mu : ℕ) (order : List ℕ) (hp : order.Perm (List.range mu))
    (xs : List α)
    (hx : xs.length = mu) (r0 : Array α) (h0 : r0.size = mu) :
    (stored mu order xs r0).toList.map f = (byVar order (xs.map f)).reverse := by
  have hlen : order.length = mu := by rw [hp.length_eq, List.length_range]
  have hn : order.Nodup := hp.symm.nodup List.nodup_range
  have hv : ∀ v ∈ order, v < mu := fun v h => List.mem_range.mp (hp.subset h)
  rw [stored_toList]
  unfold byVar
  rw [hlen, reverse_map_range]
  refine List.ext_getElem? fun i => ?_
  by_cases hi : i < mu
  · have hm : mu - 1 - i ∈ order := hp.symm.subset (List.mem_range.mpr (by omega))
    have hidx : order.idxOf (mu - 1 - i) < xs.length := by
      have h1 := List.idxOf_lt_length_of_mem hm
      omega
    rw [List.getElem?_map, storedL_get mu order xs r0.toList hn hv
        (by omega) (by simpa using h0) i hi, if_pos hm,
      List.getElem?_map, List.getElem?_range hi, List.getElem?_eq_getElem hidx]
    simp only [Option.map_some]
    rw [List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hidx), List.getElem_map]
  · rw [List.getElem?_eq_none (by rw [List.length_map, storedL_length]; simp [h0]; omega),
      List.getElem?_eq_none (by simp; omega)]

/-- The coordinates that the rounds read. -/
theorem readAt_inRounds (f : α → K) (d : α) (mu : ℕ) (order : List ℕ) (hv : ∀ v ∈ order, v < mu)
    (rho : Array α)
    (h0 : rho.size = mu) :
    (order.map fun v => f (rho.getD (mu - 1 - v) d)) = inRounds order (rho.toList.map f).reverse :=
      by
  unfold inRounds
  refine List.map_congr_left fun v hvo => ?_
  have hvm := hv v hvo
  have hl : (rho.toList.map f).reverse.length = mu := by simp [h0]
  rw [List.getD_eq_getElem _ _ (by rw [hl]; exact hvm), List.getElem_reverse, List.getElem_map]
  have e : (rho.toList.map f).length - 1 - v = mu - 1 - v := by simp [h0]
  simp only [e]
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by omega)]
  rfl

omit [CommRing K] in
/-- The point handed down. -/
theorem down_read (f : α → K) (tau : α) (r : Array α) (p : List K) (h : r.toList.map f = p.reverse)
    :
    (#[tau] ++ r).toList.map f = (p ++ [f tau]).reverse := by
  rw [Array.toList_append, List.map_append, h, List.reverse_append]
  rfl

end
end Fo
