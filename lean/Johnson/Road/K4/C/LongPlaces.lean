-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/C/LongPlaces.lean: CONDITIONAL.

Not shown here. That the verifier's placed panels meet `PanelsFit`: a hypothesis on public numbers
here; it is shown in Johnson/Road/K4/C/PanelsFitOf.lean, which imports this file (from the library's
placed_list and shape_panels, Johnson/Road/FormsKeysEnd.lean): at the panels that the honest side's
maker of the batched sumcheck's data returns. Nothing on what a panel's sides hold. Nothing here is
evaluated at an example. No property is claimed.

THE LONG VECTORS OF THE BATCHED SUMCHECK, PLACE BY PLACE. The honest side of the sub-protocol K4
lays each panel's side into a vector of 2 ^ lam entries (fillAt, longTabs,
Johnson/Desc/K4/Honest/Stack.lean): entry row ny + column of the side goes to the place off + row 2
^ wy + column. Here, on tables and numbers alone, where the panels' stretches of places are aligned,
lie within the vector and are apart: at a panel's place the vector holds that entry; at every other
place it holds 0; and a sum over all places of a function that is 0 off the panels' places is the
sum over the panels, their rows and their columns.

  panelPlace        the place of (row, column) in a panel.
  PanelFit, PanelsFit   the hypotheses on one panel's numbers; on all panels'.
  panelPlace_lt, panelPlace_inj, panelPlace_apart   a place lies in its panel's stretch; places
                 are apart.
  fill_size, fill_miss, fill_hit   fillAt's loop.
  fillAt_at, fillAt_off            one panel laid.
  IsPlace, layL, layL_size, layL_off, layL_at   **a list of panels laid, place by place.**
  longTabs_fst, longTabs_snd   the long vectors are such lists laid on zeros.
  sum_grid, sum_panel, sum_places, sum_lay2   **a sum over all places; of the two vectors
                 together.**
-/
import Johnson.Desc.K4.Honest.Stack
import Johnson.Road.FormsKeysQK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.C
open Finset
open OnBytes OnBytes.Model OnBytes.Road
open OnBytes.Model.Layer (SBlk)
open OnBytes.Desc.First.K4.Honest (Tab fillAt longTabs)

/-- The place of (row, column) in a panel. -/
def panelPlace (b : SBlk) (i yv : ℕ) : ℕ := b.off + i * 2 ^ b.wy + yv

/-- The hypotheses on one panel's numbers. This defines a hypothesis; the definition claims
nothing. -/
structure PanelFit (lam : ℕ) (b : SBlk) : Prop where
  wy_le : b.wy ≤ b.w
  ny_le : b.ny ≤ 2 ^ b.wy
  ni_le : b.ni ≤ 2 ^ (b.w - b.wy)
  dvd : 2 ^ b.w ∣ b.off
  top : b.off + 2 ^ b.w ≤ 2 ^ lam

/-- The hypotheses on a list of panels: each fits, and the stretches of places are apart. -/
structure PanelsFit (lam : ℕ) (bl : List SBlk) : Prop where
  each : ∀ b ∈ bl, PanelFit lam b
  apart : bl.Pairwise fun b c => b.off + 2 ^ b.w ≤ c.off ∨ c.off + 2 ^ c.w ≤ b.off

/-- A place lies in its panel's stretch. -/
theorem panelPlace_lt {lam : ℕ} {b : SBlk} (h : PanelFit lam b) {i yv : ℕ} (hi : i < b.ni)
    (hy : yv < b.ny) : b.off ≤ panelPlace b i yv ∧ panelPlace b i yv < b.off + 2 ^ b.w := by
  unfold panelPlace
  have h1 : yv < 2 ^ b.wy := Nat.lt_of_lt_of_le hy h.ny_le
  have h2 : i + 1 ≤ 2 ^ (b.w - b.wy) := Nat.lt_of_lt_of_le hi h.ni_le
  have e : 2 ^ b.w = 2 ^ (b.w - b.wy) * 2 ^ b.wy := by
    rw [← Nat.pow_add, Nat.sub_add_cancel h.wy_le]
  have h3 : (i + 1) * 2 ^ b.wy ≤ 2 ^ b.w := by
    rw [e]
    exact Nat.mul_le_mul_right _ h2
  rw [Nat.succ_mul] at h3
  omega

/-- In one panel two places are one only at one row and one column. -/
theorem panelPlace_inj {lam : ℕ} {b : SBlk} (h : PanelFit lam b) {i yv i' yv' : ℕ} (hy : yv < b.ny)
    (hy' : yv' < b.ny) (e : panelPlace b i yv = panelPlace b i' yv') : i = i' ∧ yv = yv' := by
  unfold panelPlace at e
  have h1 : yv < 2 ^ b.wy := Nat.lt_of_lt_of_le hy h.ny_le
  have h2 : yv' < 2 ^ b.wy := Nat.lt_of_lt_of_le hy' h.ny_le
  have e' : i * 2 ^ b.wy + yv = i' * 2 ^ b.wy + yv' := by omega
  have p : 0 < 2 ^ b.wy := Nat.two_pow_pos _
  have d := congrArg (· / 2 ^ b.wy) e'
  have m := congrArg (· % 2 ^ b.wy) e'
  simp only [Nat.mul_comm _ (2 ^ b.wy), Nat.mul_add_div p, Nat.mul_add_mod,
    Nat.div_eq_of_lt h1, Nat.div_eq_of_lt h2, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
    Nat.add_zero] at d m
  exact ⟨d, m⟩

/-! ## fillAt's loop -/

/-- The place to which fillAt's loop writes entry number j of a side. -/
def placeNo (b : SBlk) (j : ℕ) : ℕ := panelPlace b (j / b.ny) (j % b.ny)

/-- The first m steps of fillAt's loop. -/
def fillTo (b : SBlk) (x : Array E) (t : Tab) (m : ℕ) : Tab :=
  (List.range m).foldl (fun t i => t.setIfInBounds (placeNo b i) (x.getD i zeroE)) t

theorem fillAt_eq (b : SBlk) (x : Array E) (t : Tab) : fillAt b x t = fillTo b x t (b.ni * b.ny) :=
  rfl

theorem fillTo_succ (b : SBlk) (x : Array E) (t : Tab) (m : ℕ) :
    fillTo b x t (m + 1) = (fillTo b x t m).setIfInBounds (placeNo b m) (x.getD m zeroE) := by
  unfold fillTo
  rw [List.range_succ, List.foldl_append]
  rfl

theorem fill_size (b : SBlk) (x : Array E) (t : Tab) : ∀ m, (fillTo b x t m).size = t.size
  | 0 => rfl
  | m + 1 => by rw [fillTo_succ, Array.size_setIfInBounds, fill_size b x t m]

/-- A place to which no step writes is left. -/
theorem fill_miss (b : SBlk) (x : Array E) (t : Tab) (n : ℕ) :
    ∀ m, (∀ j < m, placeNo b j ≠ n) → (fillTo b x t m).getD n zeroE = t.getD n zeroE
  | 0, _ => rfl
  | m + 1, h => by
    rw [fillTo_succ, getD_set_ne _ (h m (Nat.lt_succ_self m)),
      fill_miss b x t n m fun j hj => h j (Nat.lt_succ_of_lt hj)]

/-- A place to which just one step writes holds what that step wrote. -/
theorem fill_hit (b : SBlk) (x : Array E) (t : Tab) (j : ℕ) (hn : placeNo b j < t.size) :
    ∀ m, j < m → (∀ j' < m, j' ≠ j → placeNo b j' ≠ placeNo b j) →
      (fillTo b x t m).getD (placeNo b j) zeroE = x.getD j zeroE
  | 0, h, _ => absurd h (Nat.not_lt_zero _)
  | m + 1, h, hne => by
    rw [fillTo_succ]
    by_cases e : j = m
    · subst e
      exact getD_set_self _ (by rw [fill_size]; exact hn) _
    · rw [getD_set_ne _ (hne m (Nat.lt_succ_self m) fun c => e c.symm)]
      exact fill_hit b x t j hn m (by omega) fun j' hj' => hne j' (Nat.lt_succ_of_lt hj')

/-- Entry number row ny + column. -/
theorem placeNo_at (b : SBlk) {i yv : ℕ} (hy : yv < b.ny) :
    placeNo b (i * b.ny + yv) = panelPlace b i yv := by
  unfold placeNo
  have p : 0 < b.ny := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  rw [Nat.mul_comm i, Nat.mul_add_div p, Nat.div_eq_of_lt hy, Nat.add_zero, Nat.mul_add_mod,
    Nat.mod_eq_of_lt hy]

/-- **One panel laid: at its own places.** -/
theorem fillAt_at {lam : ℕ} {b : SBlk} (h : PanelFit lam b) (x : Array E) (t : Tab)
    (ht : t.size = 2 ^ lam) {i yv : ℕ} (hi : i < b.ni) (hy : yv < b.ny) :
    (fillAt b x t).getD (panelPlace b i yv) zeroE = x.getD (i * b.ny + yv) zeroE := by
  have p : 0 < b.ny := Nat.lt_of_le_of_lt (Nat.zero_le _) hy
  rw [fillAt_eq, ← placeNo_at b hy]
  refine fill_hit b x t _ ?_ _ ?_ fun j' _ hne e => hne ?_
  · rw [placeNo_at b hy, ht]
    exact Nat.lt_of_lt_of_le (panelPlace_lt h hi hy).2 h.top
  · calc i * b.ny + yv < i * b.ny + b.ny := Nat.add_lt_add_left hy _
      _ = (i + 1) * b.ny := (Nat.succ_mul _ _).symm
      _ ≤ b.ni * b.ny := Nat.mul_le_mul_right _ hi
  · rw [placeNo_at b hy] at e
    obtain ⟨e1, e2⟩ := panelPlace_inj h (Nat.mod_lt _ p) hy e
    rw [← e1, ← e2]
    exact (Nat.div_add_mod' j' b.ny).symm

/-- **One panel laid: off its stretch.** -/
theorem fillAt_off (b : SBlk) (x : Array E) (t : Tab) {n : ℕ}
    (hn : ∀ i < b.ni, ∀ yv < b.ny, panelPlace b i yv ≠ n) :
    (fillAt b x t).getD n zeroE = t.getD n zeroE := by
  rw [fillAt_eq]
  refine fill_miss b x t n _ fun j hj => ?_
  have p : 0 < b.ny := by
    rcases Nat.eq_zero_or_pos b.ny with e | e
    · rw [e, Nat.mul_zero] at hj
      exact absurd hj (Nat.not_lt_zero _)
    · exact e
  exact hn _ ((Nat.div_lt_iff_lt_mul p).2 hj) _ (Nat.mod_lt _ p)

/-! ## A list of panels laid -/

/-- A list of panels, each with a side, laid one after the other. -/
def layL (ps : List (SBlk × Array E)) (t : Tab) : Tab := ps.foldl (fun t x => fillAt x.1 x.2 t) t

theorem layL_size : ∀ (ps : List (SBlk × Array E)) (t : Tab), (layL ps t).size = t.size
  | [], _ => rfl
  | x :: ps, t => by
    show (layL ps (fillAt x.1 x.2 t)).size = t.size
    rw [layL_size ps, fillAt_eq, fill_size]

/-- n is the place of some row and column of b. -/
def IsPlace (b : SBlk) (n : ℕ) : Prop := ∃ i < b.ni, ∃ yv < b.ny, panelPlace b i yv = n

/-- Off all panels' places the vector is as it was. -/
theorem layL_off : ∀ (ps : List (SBlk × Array E)) (t : Tab) (n : ℕ),
    (∀ x ∈ ps, ¬ IsPlace x.1 n) → (layL ps t).getD n zeroE = t.getD n zeroE
  | [], _, _, _ => rfl
  | x :: ps, t, n, hn => by
    show (layL ps (fillAt x.1 x.2 t)).getD n zeroE = t.getD n zeroE
    rw [layL_off ps _ n fun y hy => hn y (List.mem_cons_of_mem _ hy),
      fillAt_off x.1 x.2 t fun i hi yv hy e => hn x List.mem_cons_self ⟨i, hi, yv, hy, e⟩]

/-- Two panels whose stretches are apart share no place. -/
theorem panelPlace_apart {lam : ℕ} {b c : SBlk} (hb : PanelFit lam b) (hc : PanelFit lam c)
    (h : b.off + 2 ^ b.w ≤ c.off ∨ c.off + 2 ^ c.w ≤ b.off) {n : ℕ} (h1 : IsPlace b n) :
    ¬ IsPlace c n := by
  rintro ⟨i', hi', yv', hy', e'⟩
  obtain ⟨i, hi, yv, hy, e⟩ := h1
  have a := panelPlace_lt hb hi hy
  have a' := panelPlace_lt hc hi' hy'
  omega

theorem PanelsFit.tail {lam : ℕ} {b : SBlk} {bl : List SBlk} (h : PanelsFit lam (b :: bl)) :
    PanelsFit lam bl :=
  ⟨fun c hc => h.each c (List.mem_cons_of_mem _ hc), (List.pairwise_cons.1 h.apart).2⟩

/-- **At a panel's place the vector holds that panel's entry.** k: the panel's number in the
list. -/
theorem layL_at {lam : ℕ} : ∀ (ps : List (SBlk × Array E)) (t : Tab), t.size = 2 ^ lam →
    PanelsFit lam (ps.map (·.1)) → ∀ (k : ℕ) (x : SBlk × Array E), ps[k]? = some x →
    ∀ i < x.1.ni, ∀ yv < x.1.ny,
      (layL ps t).getD (panelPlace x.1 i yv) zeroE = x.2.getD (i * x.1.ny + yv) zeroE
  | [], _, _, _, _, _, h, _, _, _, _ => by cases h
  | z :: ps, t, ht, hP, 0, x, h, i, hi, yv, hy => by
    obtain rfl : z = x := Option.some.inj h
    have hz : PanelFit lam z.1 := hP.each z.1 List.mem_cons_self
    show (layL ps (fillAt z.1 z.2 t)).getD (panelPlace z.1 i yv) zeroE = _
    rw [layL_off ps _ _ fun y hy' => panelPlace_apart hz
          (hP.each y.1 (List.mem_cons_of_mem _ (List.mem_map_of_mem hy')))
          ((List.pairwise_cons.1 hP.apart).1 y.1 (List.mem_map_of_mem hy')) ⟨i, hi, yv, hy, rfl⟩,
      fillAt_at hz z.2 t ht hi hy]
  | z :: ps, t, ht, hP, k + 1, x, h, i, hi, yv, hy => by
    show (layL ps (fillAt z.1 z.2 t)).getD (panelPlace x.1 i yv) zeroE = _
    exact layL_at ps _ (by rw [fillAt_eq, fill_size]; exact ht) hP.tail k x h i hi yv hy

/-! ## The long vectors -/

/-- The first long vector is the panels' first sides, laid on zeros. -/
theorem longTabs_fst (lam : ℕ) (bl : Array SBlk) (sides : Array (Array E × Array E)) :
    (longTabs lam bl sides).1 =
      layL ((bl.toList.zip sides.toList).map fun x => (x.1, x.2.1))
        (Array.replicate (2 ^ lam) zeroE) := by
  unfold longTabs layL
  rw [List.foldl_map, ← Array.toList_zip, Array.foldl_toList]

/-- The second long vector is the panels' second sides, laid on zeros. -/
theorem longTabs_snd (lam : ℕ) (bl : Array SBlk) (sides : Array (Array E × Array E)) :
    (longTabs lam bl sides).2 =
      layL ((bl.toList.zip sides.toList).map fun x => (x.1, x.2.2))
        (Array.replicate (2 ^ lam) zeroE) := by
  unfold longTabs layL
  rw [List.foldl_map, ← Array.toList_zip, Array.foldl_toList]

/-! ## A sum over all places -/

section
variable {M : Type} [AddCommMonoid M]

/-- One index over rows times columns, as two. -/
theorem sum_grid (f : ℕ → M) (ny : ℕ) : ∀ ni : ℕ,
    ∑ j ∈ range (ni * ny), f j = ∑ i ∈ range ni, ∑ yv ∈ range ny, f (i * ny + yv)
  | 0 => by simp
  | ni + 1 => by rw [Nat.succ_mul, sum_range_add, sum_grid f ny ni, sum_range_succ]

/-- One panel: the sum over its places. -/
theorem sum_panel {lam : ℕ} {b : SBlk} (h : PanelFit lam b) (F : ℕ → M)
    [DecidablePred fun n => IsPlace b n] :
    (∑ n ∈ (range (2 ^ lam)).filter fun n => IsPlace b n, F n) =
      ∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, F (panelPlace b i yv) := by
  have e : ((range (2 ^ lam)).filter fun n => IsPlace b n) =
      (range b.ni ×ˢ range b.ny).image fun p => panelPlace b p.1 p.2 := by
    ext n
    simp only [mem_filter, mem_range, mem_image, mem_product, Prod.exists, IsPlace]
    constructor
    · rintro ⟨-, i, hi, yv, hy, rfl⟩
      exact ⟨i, yv, ⟨hi, hy⟩, rfl⟩
    · rintro ⟨i, yv, ⟨hi, hy⟩, rfl⟩
      exact ⟨Nat.lt_of_lt_of_le (panelPlace_lt h hi hy).2 h.top, i, hi, yv, hy, rfl⟩
  rw [e, sum_image, sum_product]
  intro p hp q hq hpq
  have hp' := mem_product.1 (mem_coe.1 hp)
  have hq' := mem_product.1 (mem_coe.1 hq)
  obtain ⟨e1, e2⟩ := panelPlace_inj h (mem_range.1 hp'.2) (mem_range.1 hq'.2) hpq
  exact Prod.ext e1 e2

/-- **A SUM OVER ALL PLACES of a function that is 0 off the panels' places is the sum over the
panels, their rows and their columns.** -/
theorem sum_places {lam : ℕ} : ∀ (bl : List SBlk), PanelsFit lam bl → ∀ F : ℕ → M,
    (∀ n < 2 ^ lam, (∀ b ∈ bl, ¬ IsPlace b n) → F n = 0) →
    ∑ n ∈ range (2 ^ lam), F n =
      (bl.map fun b => ∑ i ∈ range b.ni, ∑ yv ∈ range b.ny, F (panelPlace b i yv)).sum
  | [], _, F, h => by
    rw [List.map_nil, List.sum_nil]
    exact sum_eq_zero fun n hn => h n (mem_range.1 hn) fun b hb => by cases hb
  | b :: bl, hP, F, h => by
    classical
    have hb : PanelFit lam b := hP.each b List.mem_cons_self
    have s1 : ∑ n ∈ range (2 ^ lam), F n =
        (∑ n ∈ (range (2 ^ lam)).filter fun n => IsPlace b n, F n) +
          ∑ n ∈ (range (2 ^ lam)).filter fun n => ¬ IsPlace b n, F n :=
      (sum_filter_add_sum_filter_not _ _ _).symm
    have s3 : (∑ n ∈ (range (2 ^ lam)).filter fun n => ¬ IsPlace b n, F n) =
        ∑ n ∈ range (2 ^ lam), if ¬ IsPlace b n then F n else 0 := sum_filter _ _
    have s4 := sum_places bl hP.tail (fun n => if ¬ IsPlace b n then F n else 0) fun n hn hno => by
      show (if ¬ IsPlace b n then F n else 0) = 0
      by_cases c : IsPlace b n
      · exact if_neg (not_not.2 c)
      · rw [if_pos c]
        exact h n hn fun d hd => by
          rcases List.mem_cons.1 hd with rfl | hd'
          · exact c
          · exact hno d hd'
    have s5 : (bl.map fun c => ∑ i ∈ range c.ni, ∑ yv ∈ range c.ny,
        if ¬ IsPlace b (panelPlace c i yv) then F (panelPlace c i yv) else 0) =
        bl.map fun c => ∑ i ∈ range c.ni, ∑ yv ∈ range c.ny, F (panelPlace c i yv) := by
      refine List.map_congr_left fun c hc => ?_
      refine sum_congr rfl fun i hi => sum_congr rfl fun yv hy => if_pos fun hbn => ?_
      exact panelPlace_apart hb (hP.each c (List.mem_cons_of_mem _ hc))
        ((List.pairwise_cons.1 hP.apart).1 c hc) hbn
        ⟨i, mem_range.1 hi, yv, mem_range.1 hy, rfl⟩
    rw [List.map_cons, List.sum_cons, s1, sum_panel hb F, s3, s4, s5]

/-- **A SUM OVER THE PLACES OF THE TWO LONG VECTORS TOGETHER**: of G n (the first's entry at n) (the
second's), where G n 0 0 is 0: the sum over the panels, their rows and their columns of G at the
place and the two sides' entries. qs: the panels, each with its two sides. -/
theorem sum_lay2 {lam : ℕ} (qs : List (SBlk × Array E × Array E))
    (hP : PanelsFit lam (qs.map (·.1))) (G : ℕ → E → E → M) (hG : ∀ n, G n zeroE zeroE = 0) :
    ∑ n ∈ range (2 ^ lam),
        G n ((layL (qs.map fun x => (x.1, x.2.1)) (Array.replicate (2 ^ lam) zeroE)).getD n zeroE)
          ((layL (qs.map fun x => (x.1, x.2.2)) (Array.replicate (2 ^ lam) zeroE)).getD n zeroE) =
      (qs.map fun x => ∑ i ∈ range x.1.ni, ∑ yv ∈ range x.1.ny,
        G (panelPlace x.1 i yv) (x.2.1.getD (i * x.1.ny + yv) zeroE)
          (x.2.2.getD (i * x.1.ny + yv) zeroE)).sum := by
  have hA : PanelsFit lam ((qs.map fun x => (x.1, x.2.1)).map (·.1)) := by
    rw [List.map_map]
    exact hP
  have hB : PanelsFit lam ((qs.map fun x => (x.1, x.2.2)).map (·.1)) := by
    rw [List.map_map]
    exact hP
  have hz : (Array.replicate (2 ^ lam) zeroE).size = 2 ^ lam := Array.size_replicate
  have off : ∀ (ps : List (SBlk × Array E)), ps.map (·.1) = qs.map (·.1) → ∀ n,
      (∀ b ∈ qs.map (·.1), ¬ IsPlace b n) →
      (layL ps (Array.replicate (2 ^ lam) zeroE)).getD n zeroE = zeroE := by
    intro ps e n hn
    rw [layL_off ps _ n fun x hx => hn x.1 (e ▸ List.mem_map_of_mem hx)]
    exact getD_zeros _ _
  rw [sum_places (qs.map (·.1)) hP _ fun n _ hn => by
    rw [off _ (by rw [List.map_map]; rfl) n hn, off _ (by rw [List.map_map]; rfl) n hn]
    exact hG n, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun q hq => ?_)
  obtain ⟨k, hk⟩ := List.getElem?_of_mem hq
  refine sum_congr rfl fun i hi => sum_congr rfl fun yv hy => ?_
  show G (panelPlace q.1 i yv) _ _ = _
  rw [layL_at _ _ hz hA k (q.1, q.2.1) (by rw [List.getElem?_map, hk]; rfl) i (mem_range.1 hi) yv
      (mem_range.1 hy),
    layL_at _ _ hz hB k (q.1, q.2.2) (by rw [List.getElem?_map, hk]; rfl) i (mem_range.1 hi) yv
      (mem_range.1 hy)]

end

/-- A panel has at most lam bits. -/
theorem PanelFit.w_le {lam : ℕ} {b : SBlk} (h : PanelFit lam b) : b.w ≤ lam := by
  have h1 : 2 ^ b.w ≤ 2 ^ lam := Nat.le_trans (Nat.le_add_left _ _) h.top
  exact (Nat.pow_le_pow_iff_right (by decide)).1 h1

end OnBytes.Road.K4.C

#print axioms OnBytes.Road.K4.C.panelPlace_lt
#print axioms OnBytes.Road.K4.C.panelPlace_inj
#print axioms OnBytes.Road.K4.C.fillTo_succ
#print axioms OnBytes.Road.K4.C.fill_size
#print axioms OnBytes.Road.K4.C.fill_miss
#print axioms OnBytes.Road.K4.C.fill_hit
#print axioms OnBytes.Road.K4.C.placeNo_at
#print axioms OnBytes.Road.K4.C.fillAt_at
#print axioms OnBytes.Road.K4.C.fillAt_off
#print axioms OnBytes.Road.K4.C.layL_size
#print axioms OnBytes.Road.K4.C.layL_off
#print axioms OnBytes.Road.K4.C.panelPlace_apart
#print axioms OnBytes.Road.K4.C.layL_at
#print axioms OnBytes.Road.K4.C.longTabs_fst
#print axioms OnBytes.Road.K4.C.longTabs_snd
#print axioms OnBytes.Road.K4.C.sum_grid
#print axioms OnBytes.Road.K4.C.sum_panel
#print axioms OnBytes.Road.K4.C.sum_places
#print axioms OnBytes.Road.K4.C.sum_lay2
#print axioms OnBytes.Road.K4.C.PanelFit.w_le
#print axioms OnBytes.Road.K4.C.fillAt_eq
#print axioms OnBytes.Road.K4.C.PanelsFit.tail
