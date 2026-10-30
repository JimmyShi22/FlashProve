-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Forest/FoLedger.lean.
The ledger of a lookup's mask entries: how many there are, and that their places are pairwise apart.

A lookup runs a list of sumchecks. Each has its own mask entries: one for each coefficient of its
hiding polynomial (for each round the powers from 1 up, and one constant), and one
for each value that it shows at its end. `TwNums` gives each entry a name (the sumcheck's number;
`Ent`: coefficient, constant or shown value) and a place, a number
(`Sizes.place`). This file states two facts on these numbers. It says nothing on what the entries
are for.

Main names, for every `S : TwNums.Sizes`, without a hypothesis:
  `sc_perm`: inside one sumcheck whose first entry is f the places are, up to order, f, f + 1, .., f
    + masks - 1.
  `ledger_perm`: the places of all names are, up to order, 0, 1, .., nMasks - 1.
  `ledger_nodup`, `ledger_inj`: two names with one place are one name. `ledger_lt`, `ledger_onto`:
    every place is below nMasks, and every number below it is a place.
For every shape `h` of a sub-proof's forest, lawful or not:
  `elems_eq`: there are as many mask entries as the verifier's own count of the scalars that the
    lookup sends (`OnBytes.Model.Forest.elems`).

Limits: counts and places alone. Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoNums
import Mathlib.Data.List.Range
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace FoLedger
open TwNums TwNums.Sizes

/-! ## Lists -/

theorem flatMap_congr' {α β : Type} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem map_add_range (c n : ℕ) : (List.range n).map (fun t => c + t) = List.range' c n := by
  rw [List.range'_eq_map_range]

theorem range_succ_cons (n : ℕ) : List.range (n + 1) = 0 :: (List.range n).map Nat.succ :=
  List.range_succ_eq_map

/-- rounds laid one behind the other fill an interval, in order -/
theorem coef_fill : ∀ (dg : List ℕ) (f : ℕ),
    ((List.range dg.length).flatMap fun j => (List.range (dg.getD j 0)).map fun t => f +
        (dg.take j).sum + t) =
      List.range' f dg.sum
  | [], _ => rfl
  | a :: r, f => by
    rw [List.length_cons, range_succ_cons, List.flatMap_cons, List.flatMap_map]
    have h0 : ((List.range ((a :: r).getD 0 0)).map fun t => f + ((a :: r).take 0).sum + t) =
        List.range' f a := by
      simpa using map_add_range f a
    have h1 : ((List.range r.length).flatMap fun j =>
        (List.range ((a :: r).getD (Nat.succ j) 0)).map fun t => f +
            ((a :: r).take (Nat.succ j)).sum + t) =
        (List.range r.length).flatMap fun j => (List.range (r.getD j 0)).map fun t => (f + a) +
            (r.take j).sum + t := by
      refine flatMap_congr' fun j _ => ?_
      simp only [List.getD_cons_succ, List.take_succ_cons, List.sum_cons, Nat.succ_eq_add_one,
          add_assoc]
    rw [h0]
    refine (congrArg (List.range' f a ++ ·) (h1.trans (coef_fill r (f + a)))).trans ?_
    rw [List.sum_cons, List.range'_append_1]

/-! ## Inside one sumcheck -/

/-- the place of an entry of a sumcheck with the degrees dg whose first entry is f: TwNums' three
functions as one -/
def slotOf (dg : List ℕ) (f : ℕ) : Ent → ℕ
  | .coef j t => slotCoef dg f j t
  | .const => slotConst dg f
  | .shown a => slotShown dg f a

theorem place_eq (S : Sizes) (i : ℕ) (e : Ent) :
    S.place i e = slotOf (S.scs.getD i ⟨[], false, 0⟩).degs (S.firstOf i) e := by
  cases e <;> rfl

theorem ents_map (c : Sc) (f : ℕ) : (entsOf c).map (slotOf c.degs f) =
    ((List.range c.degs.length).flatMap fun j => (List.range (c.degs.getD j 0)).map fun t =>
        slotCoef c.degs f j t) ++
      [slotConst c.degs f] ++ (List.range c.shown).map fun a => slotShown c.degs f a := by
  unfold entsOf
  rw [List.map_append, List.map_append, List.map_flatMap, List.map_map]
  refine congrArg₂ (· ++ ·) (congrArg₂ (· ++ ·) (flatMap_congr' fun j _ => ?_) rfl) rfl
  rw [List.map_map]
  rfl

/-- the coefficients' places, where there is a last round -/
theorem coef_snoc (ini : List ℕ) (la f : ℕ) :
    ((List.range (ini ++ [la]).length).flatMap fun j =>
      (List.range ((ini ++ [la]).getD j 0)).map fun t => slotCoef (ini ++ [la]) f j t) =
      List.range' f ini.sum ++ List.range' (f + ini.sum + 1) la := by
  rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · rw [← coef_fill ini f]
    refine flatMap_congr' fun j hj => ?_
    have hj' : j < ini.length := List.mem_range.mp hj
    rw [List.getD_append _ _ _ _ hj']
    refine List.map_congr_left fun t _ => ?_
    unfold slotCoef
    rw [List.take_append_of_le_length (le_of_lt hj'), List.length_append, List.length_singleton,
      if_neg (by omega), Nat.add_zero]
  · rw [List.flatMap_singleton, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self,
      ← map_add_range]
    refine List.map_congr_left fun t _ => ?_
    unfold slotCoef
    rw [List.take_left', List.length_append, List.length_singleton, if_pos rfl]
    rfl

theorem sc_perm (c : Sc) (f : ℕ) : ((entsOf c).map (slotOf c.degs f)).Perm (List.range' f c.masks)
    := by
  rw [ents_map]
  obtain ⟨dg, y, sh⟩ := c
  show ((((List.range dg.length).flatMap fun j => (List.range (dg.getD j 0)).map fun t => slotCoef
      dg f j t) ++
      [slotConst dg f]) ++ (List.range sh).map fun a => slotShown dg f a).Perm
          (List.range' f (1 + dg.sum + sh))
  have hs : ((List.range sh).map fun a => slotShown dg f a) = List.range' (f + (1 + dg.sum)) sh :=
    by
    rw [← map_add_range]
    exact List.map_congr_left fun a _ => by unfold slotShown; omega
  rw [hs, ← List.range'_append_1]
  refine List.Perm.append_right _ ?_
  rcases List.eq_nil_or_concat dg with rfl | ⟨ini, la, rfl⟩
  · exact List.Perm.refl _
  · rw [List.concat_eq_append, coef_snoc]
    have hc : slotConst (ini ++ [la]) f = f + ini.sum := by
      unfold slotConst
      rw [List.dropLast_concat]
    rw [hc, List.sum_append, List.sum_singleton,
      show 1 + (ini.sum + la) = ini.sum + (1 + la) by
        omega, ← List.range'_append_1, ← List.range'_append_1,
      List.append_assoc]
    refine List.Perm.append_left _ ?_
    exact List.perm_append_comm

/-! ## All sumchecks -/

theorem all_perm : ∀ (cs : List Sc) (f : ℕ),
    ((List.range cs.length).flatMap fun i =>
      (entsOf (cs.getD i ⟨[], false, 0⟩)).map (slotOf (cs.getD i ⟨[], false, 0⟩).degs
          (f + ((cs.take i).map Sc.masks).sum))).Perm
      (List.range' f (cs.map Sc.masks).sum)
  | [], _ => List.Perm.refl _
  | c :: r, f => by
    rw [List.length_cons, range_succ_cons, List.flatMap_cons, List.flatMap_map, List.map_cons,
        List.sum_cons,
      ← List.range'_append_1]
    refine List.Perm.append ?_ ?_
    · simpa using sc_perm c f
    · refine List.Perm.trans (List.Perm.of_eq (flatMap_congr' fun i _ => ?_))
        (all_perm r (f + c.masks))
      simp only [List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons,
          Nat.succ_eq_add_one, add_assoc]

/-- the names of all entries: (sumcheck's number, entry) -/
def names (S : Sizes) : List (ℕ × Ent) :=
  (List.range S.scs.length).flatMap fun i => (entsOf (S.scs.getD i ⟨[], false, 0⟩)).map fun e =>
      (i, e)

/-- **THE PLACES OF ALL ENTRIES OF ALL SUMCHECKS ARE, UP TO ORDER, 0, 1, .., nMasks − 1.** -/
theorem ledger_perm (S : Sizes) : ((names S).map fun p => S.place p.1 p.2).Perm
    (List.range S.nMasks) := by
  have h := all_perm S.scs 0
  rw [← List.range_eq_range'] at h
  refine List.Perm.trans (List.Perm.of_eq ?_) h
  unfold names
  rw [List.map_flatMap]
  refine flatMap_congr' fun i _ => ?_
  rw [List.map_map]
  refine List.map_congr_left fun e _ => ?_
  show S.place i e = _
  rw [place_eq, Nat.zero_add]
  rfl

theorem ledger_nodup (S : Sizes) : ((names S).map fun p => S.place p.1 p.2).Nodup :=
  (ledger_perm S).nodup_iff.mpr List.nodup_range

/-- pairwise apart -/
theorem ledger_inj (S : Sizes) (p q : ℕ × Ent) (hp : p ∈ names S) (hq : q ∈ names S)
    (h : S.place p.1 p.2 = S.place q.1 q.2) : p = q :=
  List.inj_on_of_nodup_map (ledger_nodup S) hp hq h

theorem ledger_lt (S : Sizes) (p : ℕ × Ent) (hp : p ∈ names S) : S.place p.1 p.2 < S.nMasks :=
  List.mem_range.mp ((ledger_perm S).subset (List.mem_map_of_mem hp))

/-- and every number below nMasks is the place of a name -/
theorem ledger_onto (S : Sizes) (x : ℕ) (hx : x < S.nMasks) : ∃ p ∈ names S, S.place p.1 p.2 = x :=
  List.mem_map.mp ((ledger_perm S).symm.subset (List.mem_range.mpr hx))

/-! ## At the forest: as many as the scalars that the verifier counts -/

theorem foldl_add (g : ℕ → ℕ) : ∀ (n a : ℕ), (List.range n).foldl (fun s x => s + g x) a = a +
    ((List.range n).map g).sum
  | 0, _ => rfl
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append, List.map_append, List.sum_append, foldl_add g n a]
    simp [add_assoc]

theorem end_sum (w : ℕ) : ∀ d : ℕ, ((List.range (w + d)).map fun t => if t < w then 1 else 2).sum =
    w + 2 * d
  | 0 => by
    rw [Nat.add_zero, List.map_congr_left (g := fun _ => 1) fun t ht => if_pos
        (List.mem_range.mp ht)]
    simp
  | d + 1 => by
    rw [← Nat.add_assoc, List.range_succ, List.map_append, List.sum_append, end_sum w d]
    simp
    omega

theorem tie_sum : ((List.range 31).map fun j => Sc.masks ⟨[3], true, if j = 0 then 3 else 2⟩).sum =
    187 := by decide

open OnBytes.Model in
/-- There are as many mask entries as Forest.elems counts scalars sent, for every shape h. -/
theorem elems_eq (h : Forest.Shape) : FoNums.nMasks h = Forest.elems h := by
  have hK : ∀ l, Sc.masks ((FoNums.S h).scKey l) = layerSlots l := fun l => by
    show 1 + (List.replicate l 2 ++ [2]).sum + 2 = 1 + l * 2 + 2 + 2
    simp
    omega
  have hT : ∀ l, Sc.masks ((FoNums.S h).scTab l) = layerSlots (5 + l) := fun l => by
    show 1 + (List.replicate (5 + l) 2 ++ [2]).sum + 2 = 1 + (5 + l) * 2 + 2 + 2
    simp
    omega
  have hE : Sc.masks (FoNums.S h).scEnd = 1 + 2 * h.d + 5 := by
    show 1 + ((List.range (5 + h.d)).reverse.map fun t => if t < 5 then 1 else 2).sum + 0 = _
    rw [List.map_reverse, List.sum_reverse, end_sum]
    omega
  have hB : Sc.masks (FoNums.S h).scBit = sumcheckSlots .eq2 (5 + h.d) 1 2 := by
    show 1 + (List.replicate (5 + h.d) 2 ++ [2]).sum + 1 = 1 + (5 + h.d) * 2 + 2 + 1
    simp
    omega
  have e31 : (FoNums.S h).n + 1 = 31 := rfl
  have e187 : sumcheckSlots .eq2 0 3 3 + 30 * sumcheckSlots .eq2 0 2 3 = 187 := by decide
  have h0 : (((List.range ((FoNums.S h).n + 1)).map (FoNums.S h).scTie).map Sc.masks).sum =
      sumcheckSlots .eq2 0 3 3 + 30 * sumcheckSlots .eq2 0 2 3 := by
    rw [e31, e187, List.map_map]
    exact tie_sum
  unfold Forest.elems FoNums.nMasks Sizes.nMasks Sizes.scs
  rw [foldl_add, foldl_add]
  simp only [List.map_append, List.sum_append, List.map_map, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil]
  rw [List.map_map] at h0
  rw [h0, hE, hB, List.map_congr_left (f := Sc.masks ∘ (FoNums.S h).scKey) (g := layerSlots) fun l _
      => hK l,
    List.map_congr_left (f := Sc.masks ∘ (FoNums.S h).scTab) (g := fun l => layerSlots (5 + l)) fun
        l _ => hT l]
  show _ + ((List.range h.v).map layerSlots).sum +
      ((List.range h.d).map fun l => layerSlots (5 + l)).sum + _ = _
  omega

end FoLedger
