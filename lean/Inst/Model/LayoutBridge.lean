-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/LayoutBridge.lean: facts about the layout of the weights in the matrix W
(Inst/Model/Layout.lean).
    Part 1  the split of one coordinate is that of Blocks/Layout.lean (given there as a bijection):
            bounds, injective, all row parts occur
    Part 2  index tuples: `col` and `row`
    Part 3  units one below the other; `lay_of_total`: `Lay` for every list of units that fits into
            W; `lay_ref` at `ppref`
    Part 4  `wf_weightsOf`
    Part 5  the pairs of rows of the plan: every numbered pair belongs to a unit, and every pair
            of a unit has a number
    Part 6  over the field: both rows of every pair are in W (`pair_lt`); `wfw_iff_pairs`,
            `wfPairs_iff` (not all hypotheses are named here: see their statements)
-/
import Inst.Model.Layout
import Inst.Model.LayoutSanity
import Blocks.Layout
import Blocks.RngPlan
import Mathlib.Tactic

set_option autoImplicit false

namespace Inst.Model.Layout.Bridge
open Inst.Model Inst.Model.Layout

/-! ## Part 1.  One coordinate -/

theorem pow_sAux_dvd : ∀ n R : ℕ, 2 ^ sAux n R ∣ R
  | 0, R => by simp [sAux]
  | n + 1, R => by
      simp only [sAux]
      split_ifs with h
      · have h1 := Nat.mul_dvd_mul (pow_sAux_dvd n (R / 2)) (dvd_refl 2)
        rwa [Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero h.1), ← pow_succ] at h1
      · simp

def kB : Kind → Blocks.Layout.Kind
  | .low => .low
  | .high => .high
  | .whole => .whole

/-- the same coordinate in the form of Blocks/Layout.lean, with the largest power of two that
divides its size -/
def cB (c : Coord) : Blocks.Layout.Coord := ⟨c.R, sOf c.R, pow_sAux_dvd _ _, kB c.kind⟩

/-- what Parts 2 to 5 use of the split of a coordinate with t bits and l row parts -/
structure Good (R t l : ℕ) (f : ℕ → ℕ × ℕ) : Prop where
  lt : ∀ i < R, (f i).1 < 2 ^ t ∧ (f i).2 < l
  inj : ∀ i < R, ∀ i' < R, f i = f i' → i = i'
  surj : ∀ r < l, ∃ i < R, (f i).2 = r

/-- A split of Blocks/Layout.lean, read on numbers. -/
theorem good_of_csplit (S : Blocks.Layout.CSplit) (hC : 0 < S.C) (f : ℕ → ℕ × ℕ)
    (hf : ∀ i : Fin S.R, ((S.e i).1 : ℕ) = (f i.val).1 ∧ ((S.e i).2 : ℕ) = (f i.val).2) :
    Good S.R S.t S.l f where
  lt := fun i hi => by
    obtain ⟨h1, h2⟩ := hf ⟨i, hi⟩
    exact ⟨h1 ▸ lt_of_lt_of_le (S.e ⟨i, hi⟩).1.2 S.hC, h2 ▸ (S.e ⟨i, hi⟩).2.2⟩
  inj := fun i hi i' hi' h => by
    obtain ⟨h1, h2⟩ := hf ⟨i, hi⟩
    obtain ⟨h1', h2'⟩ := hf ⟨i', hi'⟩
    have : S.e ⟨i, hi⟩ = S.e ⟨i', hi'⟩ :=
      Prod.ext (Fin.ext (by rw [h1, h1']; exact congrArg Prod.fst h))
        (Fin.ext (by rw [h2, h2']; exact congrArg Prod.snd h))
    exact congrArg Fin.val (S.e.injective this)
  surj := fun r hr => by
    refine ⟨(S.e.symm (⟨0, hC⟩, ⟨r, hr⟩)).val, (S.e.symm (⟨0, hC⟩, ⟨r, hr⟩)).2, ?_⟩
    rw [← (hf _).2, Equiv.apply_symm_apply]

/-- The split of a coordinate is the split of Blocks/Layout.lean, in each of the three kinds; so it
has the three properties. -/
theorem good_split (c : Coord) (left : ℕ) :
    Good c.R (tOf c left) (lOf c (tOf c left)) (split c (tOf c left)) := by
  obtain ⟨R, kind⟩ := c
  cases kind with
  | low =>
    exact good_of_csplit ((cB ⟨R, .low⟩).lowSplit (min (sOf R) left) (Nat.min_le_left _ _))
      (by show 0 < 2 ^ _; positivity) _ fun i => ⟨rfl, rfl⟩
  | high =>
    have ht : min (sOf R) left ≤ sOf R := Nat.min_le_left _ _
    have h := good_of_csplit ((cB ⟨R, .high⟩).highSplit (min (sOf R) left) ht)
      (by show 0 < 2 ^ _; positivity) (split ⟨R, .high⟩ (min (sOf R) left)) fun i => by
        refine ⟨rfl, ?_⟩
        rw [Blocks.Layout.Coord.highSplit_snd]
        show i.val % 2 ^ (sOf R - min (sOf R) left) +
            2 ^ (sOf R - min (sOf R) left) *
              (i.val / 2 ^ (sOf R - min (sOf R) left) / 2 ^ min (sOf R) left) =
          i.val / 2 ^ sOf R * 2 ^ (sOf R - min (sOf R) left) +
            i.val % 2 ^ (sOf R - min (sOf R) left)
        rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.sub_add_cancel ht]
        ring
    have hl : ((cB ⟨R, .high⟩).highSplit (min (sOf R) left) ht).l = R / 2 ^ min (sOf R) left :=
      Blocks.Layout.Coord.highSplit_l _ _ ht
    rw [hl] at h
    exact h
  | whole =>
    by_cases hc : Nat.clog 2 R ≤ left
    · by_cases h0 : 0 < Nat.clog 2 R
      · have e : tOf ⟨R, .whole⟩ left = Nat.clog 2 R := if_pos hc
        rw [e]
        have hR : 0 < R := by
          rcases Nat.eq_zero_or_pos R with h | h
          · subst h; simp at h0
          · exact h
        have h := good_of_csplit (cB ⟨R, .whole⟩).wholeCol hR (split ⟨R, .whole⟩ (Nat.clog 2 R)) fun i => by
          have : split ⟨R, .whole⟩ (Nat.clog 2 R) i.val = (i.val, 0) := if_pos h0
          rw [this]
          exact ⟨rfl, by simp [Blocks.Layout.Coord.wholeCol]⟩
        have hl : lOf ⟨R, .whole⟩ (Nat.clog 2 R) = 1 := if_pos h0
        rw [hl]
        exact h
      · have e : tOf ⟨R, .whole⟩ left = 0 := by
          have : tOf ⟨R, .whole⟩ left = Nat.clog 2 R := if_pos hc
          omega
        rw [e]
        exact good_of_csplit (cB ⟨R, .whole⟩).wholeRow Nat.one_pos (split ⟨R, .whole⟩ 0) fun i =>
          ⟨by simp [Blocks.Layout.Coord.wholeRow, split], rfl⟩
    · have e : tOf ⟨R, .whole⟩ left = 0 := if_neg hc
      rw [e]
      exact good_of_csplit (cB ⟨R, .whole⟩).wholeRow Nat.one_pos (split ⟨R, .whole⟩ 0) fun i =>
        ⟨by simp [Blocks.Layout.Coord.wholeRow, split], rfl⟩

theorem tOf_le (c : Coord) (left : ℕ) : tOf c left ≤ left := by
  obtain ⟨R, kind⟩ := c
  cases kind with
  | low => exact Nat.min_le_right _ _
  | high => exact Nat.min_le_right _ _
  | whole =>
    show (if Nat.clog 2 R ≤ left then Nat.clog 2 R else 0) ≤ left
    split_ifs with h
    · exact h
    · exact Nat.zero_le _

/-! ## Part 2.  Index tuples -/

/-- Π_g l_g for the coordinates cs when "left" bits are left -/
def lprod : List Coord → ℕ → ℕ
  | [], _ => 1
  | c :: cs, left => lOf c (tOf c left) * lprod cs (left - tOf c left)

theorem hU_eq (k : ℕ) (U : UnitS) : hU k U = lprod U.coords k := by
  unfold hU
  generalize U.coords = cs
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih => simp only [bits, List.zip_cons_cons, List.map_cons, List.prod_cons, lprod, ih]

/-- The coordinates take at most the bits that there are; so the column number of an index
tuple in the unit (`InUnit`) is below 2^left. -/
theorem col_lt :
    ∀ (cs : List Coord) (left : ℕ) (i : List ℕ), InUnit cs i → col cs (bits cs left) i < 2 ^ left
  | [], left, [], _ => by simp [col]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | c :: cs, left, i :: is, h => by
      have h1 := ((good_split c left).lt i h.1).1
      have h2 := col_lt cs (left - tOf c left) is h.2
      have h3 : 2 ^ left = 2 ^ tOf c left * 2 ^ (left - tOf c left) := by
        rw [← pow_add, Nat.add_sub_cancel' (tOf_le c left)]
      show (split c (tOf c left) i).1 + 2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is <
        2 ^ left
      rw [h3]
      calc _ < 2 ^ tOf c left + 2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is := by omega
        _ = 2 ^ tOf c left * (col cs (bits cs (left - tOf c left)) is + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h2

/-- For an index tuple in the unit (`InUnit`): row(ȷ, ·) = ȷ · Π l + row(0, ·): the byte is the most
significant digit. -/
theorem row_shift (jj : ℕ) : ∀ (cs : List Coord) (left : ℕ) (i : List ℕ), InUnit cs i →
    row jj cs (bits cs left) i = jj * lprod cs left + row 0 cs (bits cs left) i
  | [], left, [], _ => by simp [row, lprod]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | c :: cs, left, i :: is, h => by
      have ih := row_shift jj cs (left - tOf c left) is h.2
      show (split c (tOf c left) i).2 +
          lOf c (tOf c left) * row jj cs (bits cs (left - tOf c left)) is =
        jj * (lOf c (tOf c left) * lprod cs (left - tOf c left)) +
          ((split c (tOf c left) i).2 +
            lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is)
      rw [ih]
      ring

theorem row0_lt :
    ∀ (cs : List Coord) (left : ℕ) (i : List ℕ),
      InUnit cs i → row 0 cs (bits cs left) i < lprod cs left
  | [], left, [], _ => by simp [row, lprod]
  | [], _, _ :: _, h => h.elim
  | _ :: _, _, [], h => h.elim
  | c :: cs, left, i :: is, h => by
      have h1 := ((good_split c left).lt i h.1).2
      have h2 := row0_lt cs (left - tOf c left) is h.2
      show (split c (tOf c left) i).2 +
          lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is <
        lOf c (tOf c left) * lprod cs (left - tOf c left)
      calc
        _ < lOf c (tOf c left) +
              lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is := by omega
        _ = lOf c (tOf c left) * (row 0 cs (bits cs (left - tOf c left)) is + 1) := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ h2

/-- Every number below Π l is the row part of an index tuple. -/
theorem row0_surj :
    ∀ (cs : List Coord) (left r : ℕ),
      r < lprod cs left → ∃ i, InUnit cs i ∧ row 0 cs (bits cs left) i = r
  | [], left, r, h => ⟨[], trivial, by simp only [lprod] at h; simp only [row]; omega⟩
  | c :: cs, left, r, h => by
      have hl : 0 < lOf c (tOf c left) := by
        rcases Nat.eq_zero_or_pos (lOf c (tOf c left)) with h0 | h0
        · simp only [lprod, h0, Nat.zero_mul] at h; omega
        · exact h0
      obtain ⟨i, hi, hir⟩ := (good_split c left).surj (r % lOf c (tOf c left)) (Nat.mod_lt _ hl)
      obtain ⟨is, his, hr⟩ := row0_surj cs (left - tOf c left) (r / lOf c (tOf c left))
        ((Nat.div_lt_iff_lt_mul hl).2 (by simp only [lprod] at h; rwa [Nat.mul_comm] at h))
      refine ⟨i :: is, ⟨hi, his⟩, ?_⟩
      show (split c (tOf c left) i).2 +
          lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is = r
      rw [hir, hr]
      exact Nat.mod_add_div r _

/-- Column and row part together determine an index tuple in the unit (`InUnit`). -/
theorem tuple_inj :
    ∀ (cs : List Coord) (left : ℕ) (i i' : List ℕ), InUnit cs i → InUnit cs i' →
      col cs (bits cs left) i = col cs (bits cs left) i' →
      row 0 cs (bits cs left) i = row 0 cs (bits cs left) i' → i = i'
  | [], _, [], [], _, _, _, _ => rfl
  | [], _, _ :: _, _, h, _, _, _ => h.elim
  | [], _, [], _ :: _, _, h, _, _ => h.elim
  | _ :: _, _, [], _, h, _, _, _ => h.elim
  | _ :: _, _, _ :: _, [], _, h, _, _ => h.elim
  | c :: cs, left, i :: is, i' :: is', h, h', hc, hr => by
      have g := good_split c left
      obtain ⟨a1, a2⟩ := g.lt i h.1
      obtain ⟨b1, b2⟩ := g.lt i' h'.1
      have hc : (split c (tOf c left) i).1 +
            2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is =
          (split c (tOf c left) i').1 + 2 ^ tOf c left * col cs (bits cs (left - tOf c left)) is' :=
        hc
      have hr : (split c (tOf c left) i).2 +
            lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is =
          (split c (tOf c left) i').2 +
            lOf c (tOf c left) * row 0 cs (bits cs (left - tOf c left)) is' := hr
      have c1 : (split c (tOf c left) i).1 = (split c (tOf c left) i').1 := by
        have := congrArg (· % 2 ^ tOf c left) hc
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a1, Nat.mod_eq_of_lt b1] using this
      have r1 : (split c (tOf c left) i).2 = (split c (tOf c left) i').2 := by
        have := congrArg (· % lOf c (tOf c left)) hr
        simpa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt a2, Nat.mod_eq_of_lt b2] using this
      have c2 : col cs (bits cs (left - tOf c left)) is =
          col cs (bits cs (left - tOf c left)) is' := by
        rw [c1] at hc
        exact Nat.eq_of_mul_eq_mul_left (by positivity) (Nat.add_left_cancel hc)
      have r2 : row 0 cs (bits cs (left - tOf c left)) is =
          row 0 cs (bits cs (left - tOf c left)) is' := by
        rw [r1] at hr
        exact Nat.eq_of_mul_eq_mul_left (by omega) (Nat.add_left_cancel hr)
      rw [g.inj i h.1 i' h'.1 (Prod.ext c1 r1), tuple_inj cs _ is is' h.2 h'.2 c2 r2]

/-! ## Part 3.  Units one below the other, and `Lay` -/

theorem off_succ (k : ℕ) (us : List UnitS) (n : ℕ) (U : UnitS) (h : us[n]? = some U) :
    off k us (n + 1) = off k us n + rows k U := by
  simp [off, List.take_add_one, h]

theorem off_le_succ (k : ℕ) (us : List UnitS) (n : ℕ) : off k us n ≤ off k us (n + 1) := by
  cases h : us[n]? with
  | some U => rw [off_succ k us n U h]; exact Nat.le_add_right _ _
  | none => simp [off, List.take_add_one, h]

theorem off_mono (k : ℕ) (us : List UnitS) {n n' : ℕ} (h : n ≤ n') : off k us n ≤ off k us n' := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (off_le_succ k us _)

theorem lt_length_of_get {us : List UnitS} {n : ℕ} {U : UnitS} (h : us[n]? = some U) :
    n < us.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  cases h

/-- inside its unit, a byte has a row below the rows of the unit -/
theorem row_lt (k : ℕ) (U : UnitS) (jj : ℕ) (i : List ℕ) (hj : jj < U.nU) (hi : InUnit U.coords i) :
    row jj U.coords (bits U.coords k) i < rows k U := by
  have h1 := row_shift jj U.coords k i hi
  have h2 := row0_lt U.coords k i hi
  rw [h1, rows, hU_eq]
  calc
    jj * lprod U.coords k + row 0 U.coords (bits U.coords k) i <
        jj * lprod U.coords k + lprod U.coords k := by omega
    _ = (jj + 1) * lprod U.coords k := by ring
    _ ≤ U.nU * lprod U.coords k := Nat.mul_le_mul_right _ hj

/-- `Lay` for every list of units whose rows fit into W. -/
theorem lay_of_total (k h : ℕ) (us : List UnitS) (hh : off k us us.length ≤ h) : Lay k h us := by
  have hrow : ∀ n U jj i, us[n]? = some U → jj < U.nU → InUnit U.coords i →
      off k us n ≤ (place k us n U jj i).1 ∧ (place k us n U jj i).1 < off k us (n + 1) := by
    intro n U jj i hU hj hi
    have h1 := row_lt k U jj i hj hi
    rw [off_succ k us n U hU]
    show off k us n ≤ off k us n + row jj U.coords (bits U.coords k) i ∧
      off k us n + row jj U.coords (bits U.coords k) i < _
    omega
  refine ⟨fun n U jj i hU hj hi => ⟨?_, col_lt U.coords k i hi⟩, ?_⟩
  · have h1 := (hrow n U jj i hU hj hi).2
    have h2 : off k us (n + 1) ≤ off k us us.length :=
      off_mono k us (Nat.succ_le_of_lt (lt_length_of_get hU))
    omega
  · intro n U jj i n' U' jj' i' hU hj hi hU' hj' hi' he
    have e1 : (place k us n U jj i).1 = (place k us n' U' jj' i').1 := congrArg Prod.fst he
    have e2 : (place k us n U jj i).2 = (place k us n' U' jj' i').2 := congrArg Prod.snd he
    have a := hrow n U jj i hU hj hi
    have b := hrow n' U' jj' i' hU' hj' hi'
    have hn : n = n' := by
      rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
      · have : off k us (n + 1) ≤ off k us n' := off_mono k us (Nat.succ_le_of_lt hlt)
        omega
      · exact heq
      · have : off k us (n' + 1) ≤ off k us n := off_mono k us (Nat.succ_le_of_lt hgt)
        omega
    subst hn
    have hUU : U = U' := Option.some.inj (hU.symm.trans hU')
    subst hUU
    have e1' : row jj U.coords (bits U.coords k) i = row jj' U.coords (bits U.coords k) i' :=
      Nat.add_left_cancel e1
    rw [row_shift jj U.coords k i hi, row_shift jj' U.coords k i' hi'] at e1'
    have r1 := row0_lt U.coords k i hi
    have r2 := row0_lt U.coords k i' hi'
    have hjj : jj = jj' := by
      have d1 : (jj * lprod U.coords k + row 0 U.coords (bits U.coords k) i) / lprod U.coords k =
          jj := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt r1, Nat.zero_add]
      have d2 : (jj' * lprod U.coords k + row 0 U.coords (bits U.coords k) i') / lprod U.coords k =
          jj' := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt r2, Nat.zero_add]
      rw [← d1, ← d2, e1']
    subst hjj
    exact ⟨rfl, rfl, tuple_inj U.coords k i i' hi hi' e2 (Nat.add_left_cancel e1')⟩

/-- `Lay` at the reference parameters. -/
theorem lay_ref : Lay kRef hRef (units ppref) := by
  refine lay_of_total kRef hRef (units ppref) ?_
  rw [Sanity.units_total.1, Sanity.units_total.2]
  decide

/-! ## Part 4.  WF on the matrix gives WF of the weights, under the hypotheses of `wf_weightsOf` -/

section Lists
variable {α : Type} (f : ℕ → List α)

/-- the number of entries of f 0, ..., f (N − 1) together -/
def lenTo (N : ℕ) : ℕ := ((List.range N).map fun L => (f L).length).sum

theorem lenTo_succ (N : ℕ) : lenTo f (N + 1) = lenTo f N + (f N).length := by
  simp [lenTo, List.range_succ]

theorem length_flat (N : ℕ) : ((List.range N).flatMap f).length = lenTo f N := by
  simp [lenTo, List.length_flatMap]

theorem flat_get :
    ∀ (N L m : ℕ), L < N → m < (f L).length → ((List.range N).flatMap f)[lenTo f L + m]? = (f L)[m]?
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | N + 1, L, m, hL, hm => by
      rw [List.range_succ, List.flatMap_append]
      rcases Nat.lt_or_ge L N with h | h
      · have ih := flat_get N L m h hm
        have hlt : lenTo f L + m < ((List.range N).flatMap f).length := by
          by_contra hc
          rw [List.getElem?_eq_none (by omega), eq_comm, List.getElem?_eq_none_iff] at ih
          omega
        rw [List.getElem?_append_left hlt, ih]
      · have e : L = N := by omega
        subst e
        rw [List.getElem?_append_right (by rw [length_flat]; omega), length_flat]
        simp

end Lists

section WF
variable (P : Params) (k h : ℕ) (W : Mat)

theorem first_eq (L : ℕ) : first P L = lenTo (layerUnits P) L := rfl

theorem unit_at {L m : ℕ} {U : UnitS} (hL : L < P.layers) (hU : (layerUnits P L)[m]? = some U) :
    (units P)[first P L + m]? = some U := by
  have hm : m < (layerUnits P L).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega)] at hU
    cases hU
  have h1 := flat_get (layerUnits P) P.layers L m hL hm
  have hlt : lenTo (layerUnits P) L + m <
      ((List.range P.layers).flatMap (layerUnits P)).length := by
    by_contra hc
    rw [List.getElem?_eq_none (by omega), hU] at h1
    cases h1
  rw [units, first_eq, List.getElem?_append_left hlt, h1, hU]

theorem unit_emb : (units P)[first P P.layers]? = some (uEmb P) := by
  rw [units, first_eq, List.getElem?_append_right (by rw [length_flat]), length_flat]
  simp

theorem unit_h : (units P)[first P P.layers + 1]? = some (uH P) := by
  rw [units, first_eq, List.getElem?_append_right (by rw [length_flat]; omega), length_flat]
  simp

variable {P k h W}

/-- an entry of a unit with two bytes -/
theorem two_rd (hW : WFW P k W h) {n : ℕ} {U : UnitS} (hU : (units P)[n]? = some U) (h2 : U.nU = 2)
    {i : List ℕ} (hi : InUnit U.coords i) :
    -2 ^ 12 ≤ rd P k W n U i ∧ rd P k W n U i ≤ 2 ^ 12 - 1 := by
  have h1 := hW.2 n (lt_length_of_get hU) U hU h2 i hi _ (col_lt U.coords k i hi)
  have e : rd P k W n U i = W (place k (units P) n U 0 i).1 (col U.coords (bits U.coords k) i)
      + 256 * W (place k (units P) n U 1 i).1 (col U.coords (bits U.coords k) i) := by
    simp only [rd, entry, h2, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
      pow_one, one_mul, zero_add]
    rfl
  rw [e]
  omega

/-- an entry of a unit with four bytes: under the hypotheses below it is one of the integers from
−128 (256^4 − 1)/255 to 127 (256^4 − 1)/255 (as at `Weights.WF`, Inst/Model/Program.lean) -/
theorem four_rd (hh : off k (units P) (units P).length ≤ h) (hW : WFW P k W h) {n : ℕ} {U : UnitS}
    (hU : (units P)[n]? = some U) (h4 : U.nU = 4) {i : List ℕ} (hi : InUnit U.coords i) :
    -2155905152 ≤ rd P k W n U i ∧ rd P k W n U i ≤ 2139062143 := by
  have hL := (lay_of_total k h (units P) hh).1 n U
  have b0 := hW.1 _ (hL 0 i hU (by omega) hi).1 _ (hL 0 i hU (by omega) hi).2
  have b1 := hW.1 _ (hL 1 i hU (by omega) hi).1 _ (hL 1 i hU (by omega) hi).2
  have b2 := hW.1 _ (hL 2 i hU (by omega) hi).1 _ (hL 2 i hU (by omega) hi).2
  have b3 := hW.1 _ (hL 3 i hU (by omega) hi).1 _ (hL 3 i hU (by omega) hi).2
  simp only [rd, entry, h4, Finset.sum_range_succ, Finset.sum_range_zero, pow_zero,
    pow_one, one_mul, zero_add]
  norm_num at b0 b1 b2 b3 ⊢
  constructor <;> linarith

theorem box_mat {r c : ℕ} {lo hi : ℤ} {f : ℕ → ℕ → ℤ}
    (hf : ∀ j < r, ∀ x < c, lo ≤ f j x ∧ f j x ≤ hi) : Box r c lo hi (mat r c f) := by
  intro j x
  by_cases hin : j < r ∧ x < c
  · simp only [mat, if_pos hin]
    exact hf j hin.1 x hin.2
  · simp only [mat, if_neg hin]

theorem two_zero : Two 0 0 (fun _ _ => 0) := by
  intro j x
  simp

/-- Under `h64`, `hch`, `hh`: WF(W) gives WF of the weights that the layout reads from W, so that
weightsOf is a map from well-formed matrices to indices. -/
theorem wf_weightsOf (h64 : P.nq + P.nkv ≤ 64) (hch : 0 < P.ch)
    (hh : off k (units P) (units P).length ≤ h) (hW : WFW P k W h) : (weightsOf P k W).WF P := by
  refine ⟨fun L => ?_, box_mat fun t ht j hj => four_rd hh hW (unit_emb P) rfl ⟨ht, hj, trivial⟩,
    box_mat fun j hj v hv => two_rd hW (unit_h P) rfl ⟨hv, hj, trivial⟩⟩
  by_cases hL : L < P.layers
  · rw [if_pos hL]
    have eL : (weightsOf P k W).layer L = layerOf P k W L := if_pos hL
    rw [eL]
    have hdiv : ∀ c n, c < n * P.ch → c / P.ch < n := fun c n hc =>
      Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm] at hc)
    have u0 : (units P)[first P L]? = some (uQK P) := unit_at P (m := 0) hL (by simp [layerUnits])
    have u1 : (units P)[first P L + 1]? = some (uV P) := unit_at P hL (by simp [layerUnits])
    have u2 : (units P)[first P L + 2]? = some (uO P) := unit_at P hL (by simp [layerUnits])
    have hq : Two P.d (P.nq * P.ch) (layerOf P k W L).Wq := box_mat fun j hj c hc =>
      two_rd hW u0 rfl
        ⟨by have := hdiv c _ hc; show c / P.ch < 64; omega, Nat.mod_lt _ hch, hj, trivial⟩
    have hk : Two P.d (P.nkv * P.ch) (layerOf P k W L).Wk := box_mat fun j hj c hc =>
      two_rd hW u0 rfl
        ⟨by have := hdiv c _ hc; show P.nq + c / P.ch < 64; omega, Nat.mod_lt _ hch, hj, trivial⟩
    have hv : Two P.d (P.nkv * P.ch) (layerOf P k W L).Wv :=
      box_mat fun j hj x hx => two_rd hW u1 rfl ⟨hj, hx, trivial⟩
    have ho : Two (P.nq * P.ch) P.d (layerOf P k W L).Wo :=
      box_mat fun j hj x hx => two_rd hW u2 rfl ⟨hj, hx, trivial⟩
    refine ⟨hq, hk, hv, ho, ?_⟩
    by_cases hex : hasExperts L
    · rw [if_pos hex]
      have u3 : (units P)[first P L + 3]? = some (uGU P P.fe) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u4 : (units P)[first P L + 4]? = some (uGU P P.fe) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u5 : (units P)[first P L + 5]? = some (uGUr P) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u6 : (units P)[first P L + 6]? = some (uGUr P) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u7 : (units P)[first P L + 7]? = some (uD P P.fe) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u8 : (units P)[first P L + 8]? = some (uDr P) := unit_at P hL (by simp [layerUnits, hex])
      have u9 : (units P)[first P L + 9]? = some (uR P) := unit_at P hL (by simp [layerUnits, hex])
      have eg : (layerOf P k W L).Wg =
          mat P.d P.fe fun j x => rd P k W (first P L + 3) (uGU P P.fe) [j, x] := if_pos hex
      have eu : (layerOf P k W L).Wu =
          mat P.d P.fe fun j x => rd P k W (first P L + 4) (uGU P P.fe) [j, x] := if_pos hex
      have ed : (layerOf P k W L).Wd =
          mat P.fe P.d fun j x => rd P k W (first P L + 7) (uD P P.fe) [j, x] := if_pos hex
      have er : (layerOf P k W L).Wr =
          mat P.d P.nexp fun j e => rd P k W (first P L + 9) (uR P) [j, e] := if_pos hex
      rw [eg, eu, ed, er]
      refine ⟨box_mat fun j hj x hx => two_rd hW u3 rfl ⟨hj, hx, trivial⟩,
        box_mat fun j hj x hx => two_rd hW u4 rfl ⟨hj, hx, trivial⟩,
        box_mat fun j hj x hx => two_rd hW u7 rfl ⟨hj, hx, trivial⟩,
        box_mat fun j hj x hx => two_rd hW u9 rfl ⟨hj, hx, trivial⟩,
        fun e => ?_⟩
      by_cases he : e < P.nexp
      · rw [if_pos he]
        have e1 : (layerOf P k W L).Eg e =
            mat P.d P.fe fun j x => rd P k W (first P L + 5) (uGUr P) [j, e, x] := if_pos ⟨hex, he⟩
        have e2 : (layerOf P k W L).Eu e =
            mat P.d P.fe fun j x => rd P k W (first P L + 6) (uGUr P) [j, e, x] := if_pos ⟨hex, he⟩
        have e3 : (layerOf P k W L).Ed e =
            mat P.fe P.d fun j x => rd P k W (first P L + 8) (uDr P) [j, e, x] := if_pos ⟨hex, he⟩
        rw [e1, e2, e3]
        exact ⟨box_mat fun j hj x hx => two_rd hW u5 rfl ⟨hj, he, hx, trivial⟩,
          box_mat fun j hj x hx => two_rd hW u6 rfl ⟨hj, he, hx, trivial⟩,
          box_mat fun j hj x hx => two_rd hW u8 rfl ⟨hj, he, hx, trivial⟩⟩
      · rw [if_neg he]
        have e1 : (layerOf P k W L).Eg e = fun _ _ => 0 := if_neg fun hc => he hc.2
        have e2 : (layerOf P k W L).Eu e = fun _ _ => 0 := if_neg fun hc => he hc.2
        have e3 : (layerOf P k W L).Ed e = fun _ _ => 0 := if_neg fun hc => he hc.2
        rw [e1, e2, e3]
        exact ⟨two_zero, two_zero, two_zero⟩
    · rw [if_neg hex]
      have u3 : (units P)[first P L + 3]? = some (uGU P P.f) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u4 : (units P)[first P L + 4]? = some (uGU P P.f) :=
        unit_at P hL (by simp [layerUnits, hex])
      have u5 : (units P)[first P L + 5]? = some (uD P P.f) :=
        unit_at P hL (by simp [layerUnits, hex])
      have eg : (layerOf P k W L).Wg =
          mat P.d P.f fun j x => rd P k W (first P L + 3) (uGU P P.f) [j, x] := if_neg hex
      have eu : (layerOf P k W L).Wu =
          mat P.d P.f fun j x => rd P k W (first P L + 4) (uGU P P.f) [j, x] := if_neg hex
      have ed : (layerOf P k W L).Wd =
          mat P.f P.d fun j x => rd P k W (first P L + 5) (uD P P.f) [j, x] := if_neg hex
      have er : (layerOf P k W L).Wr = fun _ _ => 0 := if_neg hex
      rw [eg, eu, ed, er]
      refine ⟨box_mat fun j hj x hx => two_rd hW u3 rfl ⟨hj, hx, trivial⟩,
        box_mat fun j hj x hx => two_rd hW u4 rfl ⟨hj, hx, trivial⟩,
        box_mat fun j hj x hx => two_rd hW u5 rfl ⟨hj, hx, trivial⟩,
        two_zero, fun e => ?_⟩
      have e1 : (layerOf P k W L).Eg e = fun _ _ => 0 := if_neg fun hc => hex hc.1
      have e2 : (layerOf P k W L).Eu e = fun _ _ => 0 := if_neg fun hc => hex hc.1
      have e3 : (layerOf P k W L).Ed e = fun _ _ => 0 := if_neg fun hc => hex hc.1
      rw [e1, e2, e3]
      exact ⟨two_zero, two_zero, two_zero⟩
  · rw [if_neg hL]
    have eL : (weightsOf P k W).layer L = noLayer := if_neg hL
    rw [eL]
    exact ⟨two_zero, two_zero, two_zero, two_zero, two_zero, two_zero, two_zero, two_zero,
      fun _ => ⟨two_zero, two_zero, two_zero⟩⟩

/-- at the reference parameters: the index that a well-formed matrix holds -/
def indexOf (W : Mat) (hW : WFW ppref kRef W hRef) : Index ppref :=
  ⟨weightsOf ppref kRef W, wf_weightsOf (by decide) (by decide)
    (by rw [Sanity.units_total.1, Sanity.units_total.2]; decide) hW⟩

end WF

/-! ## Part 5.  The pairs of rows of the plan -/

section Pairs
variable (k : ℕ) (us : List UnitS)

/-- the number of pairs of a list of units -/
def pairsOf (ps : List (ℕ × UnitS)) : ℕ := (ps.map fun p => hU k p.2).sum

/-- every pair with a number below the total belongs to a unit of the list ... -/
theorem pairAux_mem : ∀ (ps : List (ℕ × UnitS)) (q : ℕ), q < pairsOf k ps →
    ∃ p ∈ ps, ∃ r < hU k p.2, pairAux k us ps q = (off k us p.1 + r, off k us p.1 + hU k p.2 + r)
  | [], q, h => by simp [pairsOf] at h
  | p :: ps, q, h => by
      by_cases hq : q < hU k p.2
      · exact ⟨p, List.mem_cons_self, q, hq, by simp only [pairAux, if_pos hq]⟩
      · obtain ⟨p', hp', r, hr, e⟩ :=
          pairAux_mem ps (q - hU k p.2)
            (by simp only [pairsOf, List.map_cons, List.sum_cons] at h ⊢; omega)
        exact ⟨p', List.mem_cons_of_mem _ hp', r, hr, by simp only [pairAux, if_neg hq]; exact e⟩

/-- ... and every pair of every unit of the list has a number. -/
theorem pairAux_surj : ∀ (ps : List (ℕ × UnitS)) (p : ℕ × UnitS), p ∈ ps → ∀ r < hU k p.2,
    ∃ q < pairsOf k ps, pairAux k us ps q = (off k us p.1 + r, off k us p.1 + hU k p.2 + r)
  | [], _, h, _, _ => by cases h
  | p₀ :: ps, p, h, r, hr => by
      rcases List.mem_cons.1 h with rfl | h'
      · exact ⟨r, by simp only [pairsOf, List.map_cons, List.sum_cons]; omega,
          by simp only [pairAux, if_pos hr]⟩
      · obtain ⟨q, hq, e⟩ := pairAux_surj ps p h' r hr
        refine ⟨hU k p₀.2 + q,
          by simp only [pairsOf, List.map_cons, List.sum_cons] at hq ⊢; omega,
          ?_⟩
        simp only [pairAux, if_neg (show ¬ hU k p₀.2 + q < hU k p₀.2 by omega),
          Nat.add_sub_cancel_left]
        exact e

theorem mem_twoByte (n : ℕ) (U : UnitS) : (n, U) ∈ twoByte us ↔ us[n]? = some U ∧ U.nU = 2 := by
  simp only [twoByte, List.mem_filter, List.mem_map, Prod.exists, Prod.mk.injEq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨a, b, hab, rfl, rfl⟩, h2⟩
    exact ⟨List.mem_zipIdx_iff_getElem?.1 hab, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨U, n, List.mem_zipIdx_iff_getElem?.2 h1, rfl, rfl⟩, h2⟩

end Pairs

theorem le_ceil_mul (a R : ℕ) (hR : 0 < R) : a ≤ (a + R - 1) / R * R := by
  have h1 := Nat.div_add_mod (a + R - 1) R
  have h2 := Nat.mod_lt (a + R - 1) hR
  have h3 : R * ((a + R - 1) / R) = (a + R - 1) / R * R := Nat.mul_comm _ _
  omega

/-- the two rows of the pair that belongs to the index tuple i of a unit with two bytes -/
theorem place_pair (k : ℕ) (us : List UnitS) (n : ℕ) (U : UnitS)
    (i : List ℕ) (hi : InUnit U.coords i) :
    (place k us n U 0 i).1 = off k us n + row 0 U.coords (bits U.coords k) i ∧
    (place k us n U 1 i).1 = off k us n + hU k U + row 0 U.coords (bits U.coords k) i := by
  refine ⟨rfl, ?_⟩
  show off k us n + row 1 U.coords (bits U.coords k) i = _
  rw [row_shift 1 U.coords k i hi, hU_eq]
  omega

/-! ## Part 6.  Over the field -/

section Field
open Blocks.Rng

variable (P : Params) (k h : ℕ)

/-- the rows of the pair with the number q -/
def y0 (q : ℕ) : ℕ := (pair k (units P) q).1
def y1 (q : ℕ) : ℕ := (pair k (units P) q).2

/-- If the units fit into W, both rows of every pair are in W. -/
theorem pair_lt (hh : off k (units P) (units P).length ≤ h) (q : ℕ) (hq : q < m2 k (units P)) :
    y0 P k q < h ∧ y1 P k q < h := by
  obtain ⟨⟨n, U⟩, hp, r, hr, e⟩ := pairAux_mem k (units P) (twoByte (units P)) q hq
  obtain ⟨hU1, hU2⟩ := (mem_twoByte (units P) n U).1 hp
  have e' : pair k (units P) q = (off k (units P) n + r, off k (units P) n + hU k U + r) := e
  have h1 := off_succ k (units P) n U hU1
  have h2 : off k (units P) (n + 1) ≤ off k (units P) (units P).length :=
    off_mono k (units P) (Nat.succ_le_of_lt (lt_length_of_get hU1))
  have h3 : rows k U = 2 * hU k U := by rw [rows, hU2]
  have hr' : r < hU k U := hr
  simp only [y0, y1, e']
  omega

variable {P k h}
variable {F : Type} [Field F]

theorem byte_unique (p : ℕ) [CharP F p] (hp : 2 ^ 17 < p) {z z' : ℤ} (h1 : -128 ≤ z ∧ z < 128)
    (h2 : -128 ≤ z' ∧ z' < 128) (e : (z : F) = (z' : F)) : z = z' := by
  have h0 : ((z - z' : ℤ) : F) = 0 := by push_cast; rw [e]; ring
  obtain ⟨c, hc⟩ := (CharP.intCast_eq_zero_iff F p (z - z')).1 h0
  have hp' : (131072 : ℤ) < p := by exact_mod_cast (by norm_num at hp; exact hp : 131072 < p)
  by_contra hne
  have hc0 : c ≠ 0 := by rintro rfl; apply hne; linarith [hc, mul_zero (p : ℤ)]
  rcases lt_or_gt_of_ne hc0 with hneg | hpos
  · have : (p : ℤ) * c ≤ (p : ℤ) * (-1) := mul_le_mul_of_nonneg_left (by omega) (by linarith)
    linarith
  · have : (p : ℤ) * 1 ≤ (p : ℤ) * c := mul_le_mul_of_nonneg_left (by omega) (by linarith)
    linarith

/-- WFW in terms of the numbered pairs of the plan of a layout -/
theorem wfw_iff_pairs (W : Mat) :
    WFW P k W h ↔
    (∀ y < h, ∀ c < 2 ^ k, -2 ^ 7 ≤ W y c ∧ W y c < 2 ^ 7) ∧
    ∀ q < m2 k (units P), ∀ c < 2 ^ k,
      -2 ^ 12 ≤ W (y0 P k q) c + 256 * W (y1 P k q) c ∧
      W (y0 P k q) c + 256 * W (y1 P k q) c < 2 ^ 12 := by
  constructor
  · rintro ⟨hb, hp⟩
    refine ⟨hb, fun q hq c hc => ?_⟩
    obtain ⟨⟨n, U⟩, hm, r, hr, e⟩ := pairAux_mem k (units P) (twoByte (units P)) q hq
    obtain ⟨hU1, hU2⟩ := (mem_twoByte (units P) n U).1 hm
    obtain ⟨i, hi, hir⟩ := row0_surj U.coords k r (by rw [← hU_eq]; exact hr)
    have e' : pair k (units P) q = (off k (units P) n + r, off k (units P) n + hU k U + r) := e
    have hb2 := hp n (lt_length_of_get hU1) U hU1 hU2 i hi c hc
    obtain ⟨p0, p1⟩ := place_pair k (units P) n U i hi
    rw [p0, p1, hir] at hb2
    simp only [y0, y1, e']
    exact hb2
  · rintro ⟨hb, hp⟩
    refine ⟨hb, fun n _ U hU1 hU2 i hi c hc => ?_⟩
    have hr : row 0 U.coords (bits U.coords k) i < hU k U := by
      rw [hU_eq]; exact row0_lt U.coords k i hi
    obtain ⟨q, hq, e⟩ := pairAux_surj
      k (units P) (twoByte (units P)) (n, U) ((mem_twoByte (units P) n U).2 ⟨hU1, hU2⟩) _ hr
    have e' : pair k (units P) q = (off k (units P) n + row 0 U.coords (bits U.coords k) i,
        off k (units P) n + hU k U + row 0 U.coords (bits U.coords k) i) := e
    have := hp q hq c hc
    simp only [y0, y1, e'] at this
    obtain ⟨p0, p1⟩ := place_pair k (units P) n U i hi
    rw [p0, p1]
    exact this

/-- For characteristic p > 2^17, under `hh`: a matrix over the field is well formed, in the sense of
Blocks/RngPlan.lean, iff on the h rows and 2^k columns it is the image of an integer matrix that is
well formed in the sense of Inst/Model/Layout.lean. -/
theorem wfPairs_iff (p : ℕ) [CharP F p] (hp : 2 ^ 17 < p)
    (hh : off k (units P) (units P).length ≤ h) (W' : ℕ → ℕ → F) :
    WFPairs h k (m2 k (units P)) (y0 P k) (y1 P k) W' ↔
    ∃ W : Mat, WFW P k W h ∧ ∀ y < h, ∀ c < 2 ^ k, W' y c = (W y c : F) := by
  constructor
  · rintro ⟨hb, hpr⟩
    classical
    let W : Mat := fun y c => if hyc : y < h ∧ c < 2 ^ k then (hb y hyc.1 c hyc.2).choose else 0
    have hWs : ∀ y (hy : y < h) c (hc : c < 2 ^ k),
        (-128 ≤ W y c ∧ W y c < 128) ∧ W' y c = (W y c : F) := by
      intro y hy c hc
      have e : W y c = (hb y hy c hc).choose := dif_pos ⟨hy, hc⟩
      have s := (hb y hy c hc).choose_spec
      rw [e]
      exact ⟨⟨s.1, s.2.1⟩, s.2.2⟩
    refine ⟨W,
      (wfw_iff_pairs W).2
        ⟨fun y hy c hc => by have := (hWs y hy c hc).1; norm_num; exact this, fun q hq c hc => ?_⟩,
      fun y hy c hc => (hWs y hy c hc).2⟩
    obtain ⟨z0, z1, ⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩, c1, c2⟩ := hpr q hq c hc
    obtain ⟨l0, l1⟩ := pair_lt P k h hh q hq
    have e0 : W (y0 P k q) c = z0 :=
      byte_unique p hp (hWs _ l0 c hc).1 ⟨a1, a2⟩ ((hWs _ l0 c hc).2.symm.trans a3)
    have e1 : W (y1 P k q) c = z1 :=
      byte_unique p hp (hWs _ l1 c hc).1 ⟨b1, b2⟩ ((hWs _ l1 c hc).2.symm.trans b3)
    rw [e0, e1]
    norm_num
    exact ⟨c1, c2⟩
  · rintro ⟨W, hW, hc⟩
    obtain ⟨hb, hpr⟩ := (wfw_iff_pairs W).1 hW
    refine ⟨fun y hy c hcc =>
        ⟨W y c, by have := hb y hy c hcc; norm_num at this; exact this.1,
          by have := hb y hy c hcc; norm_num at this; exact this.2,
          hc y hy c hcc⟩,
      fun q hq c hcc => ?_⟩
    obtain ⟨l0, l1⟩ := pair_lt P k h hh q hq
    have b0 := hb _ l0 c hcc
    have b1 := hb _ l1 c hcc
    have pr := hpr q hq c hcc
    norm_num at b0 b1 pr
    exact ⟨W (y0 P k q) c, W (y1 P k q) c, ⟨b0.1, b0.2, hc _ l0 c hcc⟩,
      ⟨b1.1, b1.2, hc _ l1 c hcc⟩, pr.1, pr.2⟩

end Field

end Inst.Model.Layout.Bridge
