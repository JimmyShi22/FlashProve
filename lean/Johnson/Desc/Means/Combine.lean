-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Means/Combine.lean: what a batched row means.

Bat.combine adds up x^i times row number i of a group and carries the sum to the group's tables;
Bat.combineRows adds up rows that stay rows on oracle messages. Call what a row is short of, on
words, its value less its target. This file shows, for all words: the batched row is short of the
sum of x^i times what row number i is short of. For Bat.combine it also shows that a row is
returned, if every row has passed the tests of the adding.
So if all rows hold of the words, the batched row holds (combine_all). Nothing on the converse is
in this file.

Main definitions: short, groupShort, RunIn, AsideIn.
Main theorems: value_addScaled, value_split, short_addScaled, combineRows_means, combine_means,
combine_all.

What is not claimed. Nothing on who draws x, or when. Nothing on soundness.

-/
import Johnson.Desc.Means.Lays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)

variable {K : Type} [CommRing K] (ρ : Reading K)
variable {S : Statement} {G : Group} {L : GroupLayout}

/-- What a row is short of on words: 0 just if the row holds of them. -/
def short (S : Statement) (r : Row) (m : Words K) : K := value ρ S r m - ρ.val r.target

/-- What a group's row is short of on tables. -/
def groupShort (S : Statement) (L : GroupLayout) (R : GroupRow) (T : Tables K) : K :=
  groupValue ρ S L R T - ρ.val R.target

theorem says_iff_short (S : Statement) (r : Row) (m : Words K) :
    Says ρ S r m ↔ short ρ S r m = 0 := by
  unfold Says short
  exact sub_eq_zero.symm

theorem groupSays_iff_short (S : Statement) (L : GroupLayout) (R : GroupRow) (T : Tables K) :
    GroupSays ρ S L R T ↔ groupShort ρ S L R T = 0 := by
  unfold GroupSays groupShort
  exact sub_eq_zero.symm

/-! ## Sums and parts of rows -/

theorem onTable_addScaled (S : Statement) (r other : Row) (y : E) (m : Words K) (o : Nat)
    (part : Part) : onTable ρ S (r.addScaled other y) m o part =
      onTable ρ S r m o part + onTable ρ S other m o part * ρ.val y := by
  unfold onTable
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Row.coefficient_addScaled]
  ring

/-- The value of a row plus y times another row. -/
theorem value_addScaled (S : Statement) (r other : Row) (y : E) (m : Words K) :
    value ρ S (r.addScaled other y) m = value ρ S r m + value ρ S other m * ρ.val y := by
  unfold value
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  rw [onTable_addScaled, onTable_addScaled]
  ring

theorem short_addScaled (S : Statement) (r other : Row) (y : E) (m : Words K) :
    short ρ S (r.addScaled other y) m = short ρ S r m + short ρ S other m * ρ.val y := by
  unfold short
  rw [value_addScaled, Row.target_addScaled]
  ring

theorem onTable_split (S : Statement) (r : Row) (m : Words K) (o : Nat) (part : Part) :
    onTable ρ S r m o part = onTable ρ S { r with units := #[], runs := #[] } m o part +
      onTable ρ S { units := r.units, runs := r.runs } m o part := by
  unfold onTable
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Row.coefficient_split ρ r]
  ring

/-- A row's value is that of its structured summands plus that of its written-out summands. -/
theorem value_split (S : Statement) (r : Row) (m : Words K) :
    value ρ S r m = value ρ S { r with units := #[], runs := #[] } m +
      value ρ S { units := r.units, runs := r.runs } m := by
  unfold value
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro o _
  rw [onTable_split ρ S r m o .main, onTable_split ρ S r m o .mask]
  ring

theorem short_split (S : Statement) (r : Row) (m : Words K) :
    short ρ S r m = short ρ S { r with units := #[], runs := #[] } m +
      short ρ S { units := r.units, runs := r.runs } m := by
  unfold short
  rw [value_split ρ S r m]
  have e : ρ.val ({ units := r.units, runs := r.runs } : Row).target = 0 := ρ.zero
  rw [e]
  ring

/-- The row without summands and with the target 0 is short of nothing. -/
theorem short_empty (S : Statement) (m : Words K) : short ρ S {} m = 0 := by
  have e : ρ.val ({} : Row).target = 0 := ρ.zero
  unfold short value onTable
  rw [e]
  simp [Row.coefficient_val]

/-- **Rows that stay rows**: the batched row is short of the sum of x^i times what row number i is
short of. -/
theorem combineRows_means (S : Statement) (rows : Array Row) (x : E) (m : Words K) :
    short ρ S (Bat.combineRows rows x) m =
      hornerSum (ρ.val x) (rows.toList.map fun r => short ρ S r m) := by
  unfold Bat.combineRows
  rw [← Array.foldl_toList, combineRows_fold ρ x (fun r => short ρ S r m)
    (fun r other y => short_addScaled ρ S r other y m)]
  simp only [short_empty, ρ.one, zero_add, one_mul]

/-! ## The tests, on the parts of a row and on the gathering row -/

/-- What the adding has tested of a run. -/
def RunIn (S : Statement) (G : Group) (w : Run) : Prop :=
  0 < w.coeffs.size ∧ 1 ≤ w.step ∧
    Blk.placeOk S G w.oracle w.part (S.tableBits w.oracle w.part)
      (w.first + w.step * (w.coeffs.size - 1)) = true

theorem RunIn.addScaled {r : Run} (h : RunIn S G r) (w : Run) (x : E) :
    RunIn S G (r.addScaled w x) := by
  unfold RunIn
  rw [Run.size_addScaled]
  exact h

theorem RunIn.scaled {w : Run} (h : RunIn S G w) (x : E) : RunIn S G (w.scaled x) := by
  unfold RunIn
  rw [Run.size_scaled]
  exact h

theorem mergeRun_in (x : E) (runs : Array Run) (w : Run) (hw : RunIn S G w)
    (h : ∀ r ∈ runs.toList, RunIn S G r) : ∀ r ∈ (mergeRun x runs w).toList, RunIn S G r := by
  unfold mergeRun
  split
  · rw [Array.toList_modify]
    exact all_modify (RunIn S G) (fun r : Run => r.addScaled w x)
      (fun a ha => ha.addScaled w x) _ _ h
  · intro r hr
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hr
    rcases hr with hr | rfl
    · exact h r hr
    · exact hw.scaled x

theorem foldl_mergeRun_in (x : E) : ∀ (others : List Run) (runs : Array Run),
    (∀ w ∈ others, RunIn S G w) → (∀ r ∈ runs.toList, RunIn S G r) →
    ∀ r ∈ (others.foldl (mergeRun x) runs).toList, RunIn S G r
  | [], _, _, h => h
  | w :: others, runs, ho, h => by
    rw [List.foldl_cons]
    exact foldl_mergeRun_in x others _ (fun a ha => ho a (by simp [ha]))
      (mergeRun_in x runs w (ho w (by simp)) h)

/-- The structured summands of a row that has passed the tests pass them. -/
theorem RowIn.structured {r : Row} (h : RowIn S G r) :
    RowIn S G { r with units := #[], runs := #[] } :=
  ⟨h.terms, by simp, by simp, h.forms⟩

/-- The row in which Bat.combine gathers the written-out summands: it has no structured summand and
passes the tests. -/
structure AsideIn (S : Statement) (G : Group) (a : Row) : Prop where
  terms : a.terms = #[]
  forms : a.forms = #[]
  isIn : RowIn S G a

theorem AsideIn.addScaled {a r : Row} (ha : AsideIn S G a) (hr : RowIn S G r) (x : E) :
    AsideIn S G (a.addScaled { units := r.units, runs := r.runs } x) := by
  have ht : (a.addScaled { units := r.units, runs := r.runs } x).terms = #[] := by
    show a.terms ++ (#[] : Array Term).map _ = #[]
    simp [ha.terms]
  have hf : (a.addScaled { units := r.units, runs := r.runs } x).forms = #[] := by
    show a.forms ++ (#[] : Array MainForm).map _ = #[]
    simp [ha.forms]
  have hm : (a.addScaled { units := r.units, runs := r.runs } x).runs =
      r.runs.foldl (mergeRun x) a.runs := rfl
  have hu : (a.addScaled { units := r.units, runs := r.runs } x).units =
      a.units ++ r.units.map fun u => { u with coeff := mulE u.coeff x } := rfl
  refine ⟨ht, hf, ?_, ?_, ?_, ?_⟩
  · rw [ht]
    simp
  · rw [hu]
    intro u hu'
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map] at hu'
    rcases hu' with c | ⟨v, hv, rfl⟩
    · exact ha.isIn.units u c
    · exact hr.units v hv
  · rw [hm, ← Array.foldl_toList]
    exact foldl_mergeRun_in x _ _ hr.runs ha.isIn.runs
  · rw [hf]
    simp

/-! ## Bat.combine -/

/-- The loop of Bat.combine: it does not fail, and what the group's row and the gathering row are
short of together grows by the sum of s.2.2 x^i times what row number i is short of. -/
theorem combine_loop (F : LayFacts S G L) (x : E) :
    ∀ (l : List Row) (s : GroupRow × Row × E), (∀ r ∈ l, RowIn S G r) → AsideIn S G s.2.1 →
    MaskReady L s.1 → Clean ρ S L s.1 →
    ∃ s', l.foldlM (fun (s : GroupRow × Row × E) r => do
      let structured : Row := { r with units := #[], runs := #[] }
      let acc ← addToGroupRow S L structured s.2.2 s.1
      let written : Row := { units := r.units, runs := r.runs }
      pure (acc, s.2.1.addScaled written s.2.2, mulE s.2.2 x)) s = some s' ∧
      AsideIn S G s'.2.1 ∧ MaskReady L s'.1 ∧ Clean ρ S L s'.1 ∧ ∀ m : Words K,
        groupShort ρ S L s'.1 (tablesOf S L m) + short ρ S s'.2.1 m =
          groupShort ρ S L s.1 (tablesOf S L m) + short ρ S s.2.1 m +
            ρ.val s.2.2 * hornerSum (ρ.val x) (l.map fun r => short ρ S r m)
  | [], s, _, ha, hp, hc => ⟨s, rfl, ha, hp, hc, fun m => by simp [hornerSum]⟩
  | r :: l, s, hr, ha, hp, hc => by
    have fr := hr r (by simp)
    obtain ⟨acc, h1⟩ := addToGroupRow_total ρ F fr.structured s.2.2 s.1 hp
    have p1 := (addToGroupRow_mask ρ S L F.maskOk _ fr.structured.fits (fr.structured.maskFits F)
      s.2.2 s.1 acc hp h1 0 (Nat.two_pow_pos _)).1
    obtain ⟨s', h2, a2, p2, c2, e2⟩ := combine_loop F x l
      (acc, s.2.1.addScaled { units := r.units, runs := r.runs } s.2.2, mulE s.2.2 x)
      (fun a h' => hr a (by simp [h'])) (ha.addScaled fr s.2.2) p1
      (lays_clean ρ F fr.structured s.2.2 s.1 acc hp h1 hc)
    refine ⟨s', ?_, a2, p2, c2, fun m => ?_⟩
    · rw [List.foldlM_cons]
      simp only [h1, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      exact h2
    · have e1 := lays_eq ρ F fr.structured s.2.2 s.1 acc hp h1 m
      have e3 := e2 m
      simp only [short_addScaled, ρ.mul] at e3
      simp only [List.map_cons, hornerSum, short_split ρ S r m]
      unfold groupShort short at *
      linear_combination e3 + e1

/-- **Rows carried to a group's tables**: if every row has passed the tests of the adding,
Bat.combine returns a row; it has no coefficient where the tables hold no word; and for all words it
is short, on the group's tables as the words fill them, of the sum of x^i times what row number i is
short of on the words. -/
theorem combine_means (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (rows : Array Row)
    (x : E) (hG : S.groups[g]? = some G) (hL : S.layout g = some L) (hOk : GroupOk S G)
    (hr : ∀ r ∈ rows.toList, RowIn S G r) :
    ∃ out, Bat.combine S g ⟨L, rows⟩ x = some out ∧ MaskReady L out ∧ Clean ρ S L out ∧
      ∀ m : Words K, groupShort ρ S L out (tablesOf S L m) =
        hornerSum (ρ.val x) (rows.toList.map fun r => short ρ S r m) := by
  have F := layFacts hG hL hOk
  have a0 : AsideIn S G {} := ⟨rfl, rfl, by simp, by simp, by simp, by simp⟩
  obtain ⟨s, h1, a1, p1, c1, e1⟩ := combine_loop ρ F x rows.toList ({ group := g }, {}, oneE) hr
    a0 (Or.inl rfl) (clean_start ρ S L g)
  obtain ⟨out, h2⟩ := addToGroupRow_total ρ F a1.isIn oneE s.1 p1
  have p2 := (addToGroupRow_mask ρ S L F.maskOk _ a1.isIn.fits (a1.isIn.maskFits F)
    oneE s.1 out p1 h2 0 (Nat.two_pow_pos _)).1
  refine ⟨out, ?_, p2, lays_clean ρ F a1.isIn oneE s.1 out p1 h2 c1, fun m => ?_⟩
  · unfold Bat.combine
    simp only [← Array.foldlM_toList, Option.bind_eq_bind]
    exact Option.bind_eq_some_iff.2 ⟨s, h1, h2⟩
  · have e2 := lays_eq ρ F a1.isIn oneE s.1 out p1 h2 m
    have e3 := e1 m
    have z1 : groupShort ρ S L { group := g } (tablesOf S L m) = 0 := by
      unfold groupShort
      rw [groupValue_start]
      have e : ρ.val ({ group := g } : GroupRow).target = 0 := ρ.zero
      rw [e, sub_zero]
    simp only [z1, short_empty, ρ.one] at e3
    rw [ρ.one] at e2
    unfold groupShort short at *
    linear_combination e2 + e3

/-- If all rows hold of the words, the batched row holds of the group's tables. -/
theorem combine_all (S : Statement) (g : Nat) (G : Group) (L : GroupLayout) (rows : Array Row)
    (x : E) (out : GroupRow) (hG : S.groups[g]? = some G) (hL : S.layout g = some L)
    (hOk : GroupOk S G) (hr : ∀ r ∈ rows.toList, RowIn S G r)
    (h : Bat.combine S g ⟨L, rows⟩ x = some out) (m : Words K) (hs : AllSay ρ S rows.toList m) :
    GroupSays ρ S L out (tablesOf S L m) := by
  obtain ⟨out', h', _, _, e⟩ := combine_means ρ S g G L rows x hG hL hOk hr
  rw [h] at h'
  obtain rfl := Option.some.inj h'
  rw [groupSays_iff_short, e m]
  apply hornerSum_zero
  intro a ha
  obtain ⟨r, hr', rfl⟩ := List.mem_map.1 ha
  exact (says_iff_short ρ S r m).1 (hs r hr')

end OnBytes.Means
