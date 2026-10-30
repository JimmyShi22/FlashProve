-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/BudCount.lean: THE CONTAINMENT GIVES THE COUNT. Of the two
bounds on the positions asked of the trees that a proximity test's second part sends: `budOpened`
(Sim/ExactPlan.lean: they lie among those that the next reading round samples) gives `budRest`
(Sim/Row.lean: in range, and at most C.r, Z.r different ones modulo the two codes' lengths), under
two public premises. One helper definition; statements and proofs.

What for. The second member's sentence is proved under the containment (`exact_free_trees`,
Sim/TreesExact.lean). The count is the bound that Sim/Row.lean and Sim/Spec.lean name. This file
shows that the containment lies within the count. Who pays the containment: Sim/BudRestAtRun.lean
and Sim/DebtBoth.lean, under public premises; which of these the head pays: Sim/DebtAtO.lean.

  `rest_of_opened`   the statement
  `test_of_both`   so `budBoth` (Sim/ExactFirstOwn.lean) gives `testBud` (Sim/Row.lean) at every
                 number
  `budRest_of_sub`   the count from a containment, in the count's own letters
  `budDue`       `Spec.budDue` (Sim/Spec.lean), till now a statement alone, holds
  `readOf`       the positions that the round which reads the tree of switch number j samples
  `different_aux`, `different_sub`   no more different numbers than a list that holds them all has
                 entries
  `okFrom_low`, `stages_low`   what `StagesOk` (RunBy.lean) gives stage by stage
  `sum_take`, `openedTr_here`, `openedTr_later`, `pick_succ`, `opened_at`, `fits_at`   where
                 `openedTr` (Sim/CoreText.lean) and `FitsBody`
                 (Johnson/LinkSim/AtText/SpecShift.lean) stand at the switch out of stage number j

The two premises. `StagesOk`: on the plan's stages alone: h ≤ k at each; the mask code no longer
than the main code at each but the last. `stagesOk_seated` (StagesOfPlan.lean) has it under the head
at the four seated tests. `FitsBody`: on the stages and on HOW MANY positions each reading round
samples: no more than a row's tail is long, in both codes; `fits_of_sizesB` (Sim/Reach.lean) makes
it of a test on numbers.

Limits.
- The converse does not hold: a count does not say where the positions lie.
- At the last tree the count is of the positions asked alone; `budRest` lays no sampled positions
  beside them there.
- `FitsBody` counts with repeats; `budRest` counts different numbers: so more is asked here than the
  count needs.
- Nothing on what a bound is good for. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.BudBoth
import Johnson.Desc.ProofFile.Honest.K12.Sim.Spec
import Johnson.Desc.ProofFile.Honest.K12.ReadsOfTree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open H2K.Pub (sgOf)
open OnBytes.LinkSim.AtText (FitsBody openAt qNext oNext)

/-- The positions that the round which reads the tree of switch number j samples: "CS" of the next
switch; for the last tree the base case's second round. As `Spec.budDue` has it. -/
def readOf (stages : List Fmt.M1.Stage) (ds : List Fmt.Drawn) (j : ℕ) : List ℕ :=
  (ds.getD (if j + 2 < stages.length then readAt stages j else seedAt stages j + 3) noDraw).poss

/-! ## 1 Different numbers -/

theorem different_aux : ∀ (n : ℕ) (l l' : List ℕ), l.length ≤ n → (∀ x ∈ l, x ∈ l') →
    l.eraseDups.length ≤ l'.length
  | _, [], _, _, _ => by simp
  | 0, _ :: _, _, h, _ => by simp at h
  | n + 1, a :: l, l', h, hs => by
    rw [List.eraseDups_cons, List.length_cons]
    have ha : a ∈ l' := hs a List.mem_cons_self
    have hlt : (l'.filter fun b => !b == a).length < l'.length :=
      List.length_filter_lt_length_iff_exists.2 ⟨a, ha, by simp⟩
    refine Nat.succ_le_of_lt (Nat.lt_of_le_of_lt
      (different_aux n _ (l'.filter fun b => !b == a)
        (Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_succ_le_succ h)) fun x hx => ?_) hlt)
    obtain ⟨h1, h2⟩ := List.mem_filter.1 hx
    exact List.mem_filter.2 ⟨hs x (List.mem_cons_of_mem _ h1), h2⟩

/-- (1) No more different numbers than a list that holds them all has entries. -/
theorem different_sub (l l' : List ℕ) (h : ∀ x ∈ l, x ∈ l') : different l ≤ l'.length :=
  different_aux _ l l' (Nat.le_refl _) h

/-! ## 2 The count from a containment -/

/-- (2) **The count from the containment, in the count's own letters.** hZ: at every stage but the
first and the last. -/
theorem budRest_of_sub (stages : List Fmt.M1.Stage) (ds : List Fmt.Drawn)
    (asks : List (List (List ℕ)))
    (hZ : ∀ j, j + 2 < stages.length →
      (stages.getD (j + 1) default).Z.a ≤ (stages.getD (j + 1) default).C.a)
    (hA : ∀ j, j + 1 < stages.length → ∀ q ∈ (((asks[seedAt stages j]?).getD [])[0]?).getD [],
      q ∈ (readOf stages ds j).map (· % 2 ^ (stages.getD (j + 1) default).C.a))
    (hN : ∀ j, j + 1 < stages.length → (readOf stages ds j).length ≤
      min (stages.getD (j + 1) default).C.r (stages.getD (j + 1) default).Z.r) :
    budRest stages ds asks = true := by
  unfold budRest
  rw [List.all_eq_true]
  intro j hj
  have hj' : j + 1 < stages.length := by
    have := List.mem_range.1 hj
    omega
  have hAj := hA j hj'
  have hNj := hN j hj'
  have hNin : ∀ y ∈ (if j + 2 < stages.length then (ds.getD (readAt stages j) noDraw).poss else []),
      j + 2 < stages.length ∧ y ∈ readOf stages ds j := by
    intro y hy
    by_cases hl : j + 2 < stages.length
    · rw [if_pos hl] at hy
      refine ⟨hl, ?_⟩
      unfold readOf
      rw [if_pos hl]
      exact hy
    · rw [if_neg hl] at hy
      cases hy
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  refine ⟨⟨fun x hx => ?_, ?_⟩, ?_⟩
  · obtain ⟨y, -, rfl⟩ := List.mem_map.1 (hAj x hx)
    exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · refine Nat.le_trans (different_sub _
      ((readOf stages ds j).map (· % 2 ^ (stages.getD (j + 1) default).C.a)) fun z hz => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (hAj y hy)
        exact List.mem_map.2 ⟨w, hw, (Nat.mod_mod _ _).symm⟩
      · exact List.mem_map.2 ⟨y, (hNin y hy).2, rfl⟩
    · rw [List.length_map]
      exact Nat.le_trans hNj (Nat.min_le_left _ _)
  · refine Nat.le_trans (different_sub _
      ((readOf stages ds j).map fun w => w % 2 ^ (stages.getD (j + 1) default).C.a %
        2 ^ (stages.getD (j + 1) default).Z.a) fun z hz => ?_) ?_
    · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hz
      rcases List.mem_append.1 hy with hy | hy
      · obtain ⟨w, hw, rfl⟩ := List.mem_map.1 (hAj y hy)
        exact List.mem_map.2 ⟨w, hw, rfl⟩
      · obtain ⟨hl, hy'⟩ := hNin y hy
        exact List.mem_map.2 ⟨y, hy', Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (hZ j hl))⟩
    · rw [List.length_map]
      exact Nat.le_trans hNj (Nat.min_le_right _ _)

/-- (3) **`Spec.budDue` (Sim/Spec.lean) holds**, at every job of the simulators. -/
theorem budDue {Pb : Type} (Js : SimJob Pb) : Spec.budDue Js := by
  intro ds asks hZ hA hN
  refine budRest_of_sub Js.stages ds asks (fun j hj => hZ _ ?_) (fun j hj q hq => ?_)
    fun j hj => hN j hj
  · rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  · rw [hA j hj] at hq
    exact mem_listOf q _ hq

/-! ## 3 What the test on the stages gives -/

theorem okFrom_low : ∀ (rest : List Fmt.M1.Stage) (s : Fmt.M1.Stage), okFrom s rest = true →
    (∀ x ∈ s :: rest, x.h ≤ x.k) ∧ ∀ j, j < rest.length →
      ((s :: rest).getD j default).Z.a ≤ ((s :: rest).getD j default).C.a
  | [], s, h => by
    simp only [okFrom, Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨fun x hx => ?_, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    obtain rfl := List.mem_singleton.1 hx
    omega
  | n :: rest, s, h => by
    simp only [okFrom, switchFitB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨i1, i2⟩ := okFrom_low rest n h.2
    refine ⟨fun x hx => ?_, fun j hj => ?_⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact h.1.1.1
      · exact i1 x hx
    · cases j with
      | zero => exact h.1.2.2
      | succ j => exact i2 j (Nat.lt_of_succ_lt_succ hj)

/-- (4) What `StagesOk` gives, stage by stage. -/
theorem stages_low (stages : List Fmt.M1.Stage) (h : StagesOk stages = true) :
    (∀ x ∈ stages, x.h ≤ x.k) ∧ ∀ j, j + 1 < stages.length →
      (stages.getD j default).Z.a ≤ (stages.getD j default).C.a := by
  match stages, h with
  | s :: n :: rest, h =>
    obtain ⟨i1, i2⟩ := okFrom_low (n :: rest) s h
    exact ⟨i1, fun j hj => i2 j (Nat.lt_of_succ_lt_succ hj)⟩

/-! ## 4 The places -/

theorem sum_take : ∀ (L : List Fmt.M1.Stage) (j : ℕ), j < L.length →
    ((L.take (j + 1)).map (·.k + 3)).sum =
      ((L.take j).map (·.k + 3)).sum + ((L.getD j default).k + 3)
  | [], _, h => absurd h (Nat.not_lt_zero _)
  | a :: L, 0, _ => by simp
  | a :: L, j + 1, h => by
    have ih := sum_take L j (Nat.lt_of_succ_lt_succ h)
    simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getD_cons_succ]
    omega

theorem openedTr_here (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (cur next : Fmt.M1.Stage)
    (o : ℕ) : openedTr D (next :: rest) cur o (1 + ((sgOf cur).h + (sgOf cur).g)) =
      Fmt.listOf (qNext rest.isEmpty cur next o D) := by
  rw [openedTr, if_neg (Nat.lt_irrefl _), if_pos rfl]

theorem openedTr_later (D : ℕ → Fmt.Drawn) (rest : List Fmt.M1.Stage) (cur next : Fmt.M1.Stage)
    (o i : ℕ) : openedTr D (next :: rest) cur o ((sgOf cur).h + (sgOf cur).g + 3 + i) =
      openedTr D rest next (oNext cur o) i := by
  rw [openedTr, if_neg (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- The choice between a later "CS" and the base case, one stage on. -/
theorem pick_succ (next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (j a b : ℕ) :
    (if j + 1 + 1 < (next :: rest).length then a else b) =
      if j + 1 < rest.length then a else b := by
  by_cases hc : j + 1 < rest.length
  · rw [if_pos hc, if_pos (show j + 1 + 1 < (next :: rest).length by
      simp only [List.length_cons]; omega)]
  · rw [if_neg hc, if_neg (show ¬ j + 1 + 1 < (next :: rest).length by
      simp only [List.length_cons]; omega)]

/-- (5) **Where `openedTr` stands at the switch out of stage number j.** The list of stages is
cur :: rest; o: the number of cur's first round. -/
theorem opened_at (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o j : ℕ),
    j < rest.length → (∀ x ∈ cur :: rest, x.h ≤ x.k) →
    openedTr D rest cur o
        ((((cur :: rest).take j).map (·.k + 3)).sum + 1 + ((cur :: rest).getD j default).k) =
      Fmt.listOf (((D (o + (((cur :: rest).take (j + 1)).map (·.k + 3)).sum +
        (if j + 1 < rest.length then 2 + ((cur :: rest).getD (j + 1) default).k else 1))).poss).map
          (· % 2 ^ ((cur :: rest).getD (j + 1) default).C.a))
  | [], _, _, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | next :: rest, cur, o, 0, _, hk => by
    have e : (sgOf cur).h + (sgOf cur).g = cur.k := Nat.add_sub_cancel' (hk cur List.mem_cons_self)
    have e' : (sgOf next).h + (sgOf next).g = next.k :=
      Nat.add_sub_cancel' (hk next (List.mem_cons_of_mem _ List.mem_cons_self))
    have i0 : (((cur :: next :: rest).take 0).map (·.k + 3)).sum + 1 +
        ((cur :: next :: rest).getD 0 default).k = 1 + ((sgOf cur).h + (sgOf cur).g) := by
      rw [e]
      show 0 + 1 + cur.k = 1 + cur.k
      omega
    have s1 : (((cur :: next :: rest).take (0 + 1)).map (·.k + 3)).sum = cur.k + 3 :=
      Nat.add_zero _
    have g1 : (cur :: next :: rest).getD (0 + 1) default = next := rfl
    rw [i0, openedTr_here, s1, g1]
    unfold qNext openAt oNext
    rw [e, e']
    cases rest with
    | nil =>
      simp only [List.isEmpty_nil, ↓reduceIte, List.length_cons, List.length_nil]
      rw [if_neg (by omega), Nat.add_assoc o cur.k 3]
      rfl
    | cons a r =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      rw [if_pos (by omega)]
      have i : o + cur.k + 3 + 2 + next.k = o + (cur.k + 3) + (2 + next.k) := by omega
      rw [i]
      rfl
  | next :: rest, cur, o, j + 1, hj, hk => by
    have e : (sgOf cur).h + (sgOf cur).g = cur.k := Nat.add_sub_cancel' (hk cur List.mem_cons_self)
    have hj' : j < rest.length := Nat.lt_of_succ_lt_succ hj
    have ih := opened_at D rest next (oNext cur o) j hj'
      fun x hx => hk x (List.mem_cons_of_mem _ hx)
    have i1 : (((cur :: next :: rest).take (j + 1)).map (·.k + 3)).sum + 1 +
        ((cur :: next :: rest).getD (j + 1) default).k =
        (sgOf cur).h + (sgOf cur).g + 3 + ((((next :: rest).take j).map (·.k + 3)).sum + 1 +
          ((next :: rest).getD j default).k) := by
      rw [e]
      show cur.k + 3 + (((next :: rest).take j).map (·.k + 3)).sum + 1 +
        ((next :: rest).getD j default).k = _
      omega
    have s2 : (((cur :: next :: rest).take (j + 1 + 1)).map (·.k + 3)).sum =
        cur.k + 3 + (((next :: rest).take (j + 1)).map (·.k + 3)).sum := rfl
    have g2 : (cur :: next :: rest).getD (j + 1 + 1) default =
        (next :: rest).getD (j + 1) default := rfl
    rw [i1, openedTr_later, ih, s2, g2, pick_succ]
    unfold oNext
    rw [e]
    generalize (if j + 1 < rest.length then 2 + ((next :: rest).getD (j + 1) default).k else 1) = Y
    have i2 : o + cur.k + 3 + (((next :: rest).take (j + 1)).map (·.k + 3)).sum + Y =
        o + (cur.k + 3 + (((next :: rest).take (j + 1)).map (·.k + 3)).sum) + Y := by omega
    rw [i2]

/-- (6) What `FitsBody` gives at that round. -/
theorem fits_at (D : ℕ → Fmt.Drawn) : ∀ (rest : List Fmt.M1.Stage) (cur : Fmt.M1.Stage) (o j : ℕ),
    j < rest.length → (∀ x ∈ cur :: rest, x.h ≤ x.k) → FitsBody D rest cur o →
    (D (o + (((cur :: rest).take (j + 1)).map (·.k + 3)).sum +
        (if j + 1 < rest.length then 2 + ((cur :: rest).getD (j + 1) default).k
          else 1))).poss.length ≤
      min ((cur :: rest).getD (j + 1) default).C.r ((cur :: rest).getD (j + 1) default).Z.r
  | [], _, _, _, hj, _, _ => absurd hj (Nat.not_lt_zero _)
  | next :: rest, cur, o, 0, _, hk, hF => by
    have e : (sgOf cur).h + (sgOf cur).g = cur.k := Nat.add_sub_cancel' (hk cur List.mem_cons_self)
    have e' : (sgOf next).h + (sgOf next).g = next.k :=
      Nat.add_sub_cancel' (hk next (List.mem_cons_of_mem _ List.mem_cons_self))
    have s1 : (((cur :: next :: rest).take (0 + 1)).map (·.k + 3)).sum = cur.k + 3 :=
      Nat.add_zero _
    have g1 : (cur :: next :: rest).getD (0 + 1) default = next := rfl
    unfold FitsBody at hF
    obtain ⟨-, -, -, -, hF'⟩ := hF
    rw [e] at hF'
    rw [s1, g1]
    cases rest with
    | nil =>
      unfold FitsBody at hF'
      obtain ⟨a, b, -, -⟩ := hF'
      simp only [List.length_cons, List.length_nil]
      rw [if_neg (by omega), ← Nat.add_assoc o cur.k 3]
      exact Nat.le_min.2 ⟨a, b⟩
    | cons a' r =>
      unfold FitsBody at hF'
      obtain ⟨a, b, -⟩ := hF'
      rw [e'] at a b
      simp only [List.length_cons]
      rw [if_pos (by omega)]
      have i : o + (cur.k + 3) + (2 + next.k) = o + cur.k + 3 + 2 + next.k := by omega
      rw [i]
      exact Nat.le_min.2 ⟨a, b⟩
  | next :: rest, cur, o, j + 1, hj, hk, hF => by
    have e : (sgOf cur).h + (sgOf cur).g = cur.k := Nat.add_sub_cancel' (hk cur List.mem_cons_self)
    have hj' : j < rest.length := Nat.lt_of_succ_lt_succ hj
    unfold FitsBody at hF
    obtain ⟨-, -, -, -, hF'⟩ := hF
    rw [e] at hF'
    have ih := fits_at D rest next (o + cur.k + 3) j hj'
      (fun x hx => hk x (List.mem_cons_of_mem _ hx)) hF'
    have s2 : (((cur :: next :: rest).take (j + 1 + 1)).map (·.k + 3)).sum =
        cur.k + 3 + (((next :: rest).take (j + 1)).map (·.k + 3)).sum := rfl
    have g2 : (cur :: next :: rest).getD (j + 1 + 1) default =
        (next :: rest).getD (j + 1) default := rfl
    rw [s2, g2, pick_succ]
    generalize (if j + 1 < rest.length then 2 + ((next :: rest).getD (j + 1) default).k else 1) = Y
      at ih ⊢
    have i2 : o + (cur.k + 3 + (((next :: rest).take (j + 1)).map (·.k + 3)).sum) + Y =
        o + cur.k + 3 + (((next :: rest).take (j + 1)).map (·.k + 3)).sum + Y := by omega
    rw [i2]
    exact ih

/-! ## 5 The statement -/

/-- (7) **The containment gives the count.** Both premises are public: `StagesOk` speaks of the
plan's stages; `FitsBody` of these and of how many positions each reading round samples. -/
theorem rest_of_opened (stages : List Fmt.M1.Stage) (hOk : StagesOk stages = true)
    (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (hF : FitsBody (laterOf stages ds) (stages.drop 1) (stages.headD default) 1)
    (h : budOpened stages 1 ds asks) : budRest stages ds asks = true := by
  obtain ⟨hk, hz⟩ := stages_low stages hOk
  match stages, hOk, hF, h, hk, hz with
  | s :: next :: rest, _, hF, h, hk, hz =>
    have e : (sgOf s).h + (sgOf s).g = s.k := Nat.add_sub_cancel' (hk s List.mem_cons_self)
    -- the round that reads the tree of switch j, among the second part's rounds
    have hidx : ∀ j, j + 1 < (s :: next :: rest).length →
        (laterOf (s :: next :: rest) ds
          (1 + (((s :: next :: rest).take (j + 1)).map (·.k + 3)).sum +
          (if j + 1 < (next :: rest).length then 2 + ((s :: next :: rest).getD (j + 1) default).k
            else 1))).poss = readOf (s :: next :: rest) ds j := by
      intro j hj
      have hs := sum_take (s :: next :: rest) j (by omega)
      have hs1 : (((s :: next :: rest).take (j + 1)).map (·.k + 3)).sum =
          s.k + 3 + (((next :: rest).take j).map (·.k + 3)).sum := by
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
      unfold laterOf readOf readAt seedAt roundOf
      show (ds.getD (_ - (2 + s.k)) noDraw).poss = _
      by_cases hl : j + 2 < (s :: next :: rest).length
      · have hl' : j + 1 < (next :: rest).length := by
          simp only [List.length_cons] at hl ⊢
          omega
        rw [if_pos hl, if_pos hl']
        show _ = (ds.getD (_ - (2 + s.k) + 1) noDraw).poss
        congr 2
        omega
      · have hl' : ¬ j + 1 < (next :: rest).length := by
          simp only [List.length_cons] at hl ⊢
          omega
        rw [if_neg hl, if_neg hl']
        show _ = (ds.getD (_ - (2 + s.k) + 3) noDraw).poss
        congr 2
        omega
    refine budRest_of_sub _ ds asks (fun j hj => hz (j + 1) (by omega)) (fun j hj q hq => ?_)
      fun j hj => ?_
    · have hj' : j < (next :: rest).length := by
        simp only [List.length_cons] at hj ⊢
        omega
      have h1 := h rfl (seedAt (s :: next :: rest) j) q hq
      have hs1 : j = 0 ∨ s.k + 3 ≤ (((s :: next :: rest).take j).map (·.k + 3)).sum := by
        cases j with
        | zero => exact Or.inl rfl
        | succ j =>
          refine Or.inr ?_
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
          omega
      have hi : 1 + ((sgOf ((s :: next :: rest).headD default)).h +
          (sgOf ((s :: next :: rest).headD default)).g) + seedAt (s :: next :: rest) j =
          (((s :: next :: rest).take j).map (·.k + 3)).sum + 1 +
            ((s :: next :: rest).getD j default).k := by
        show 1 + ((sgOf s).h + (sgOf s).g) + seedAt (s :: next :: rest) j = _
        rw [e]
        unfold seedAt roundOf
        show 1 + s.k + (_ - (2 + s.k)) = _
        rcases hs1 with rfl | hs1
        · simp
        · omega
      rw [hi] at h1
      have h2 : q ∈ openedTr (laterOf (s :: next :: rest) ds) (next :: rest) s 1
          ((((s :: next :: rest).take j).map (·.k + 3)).sum + 1 +
            ((s :: next :: rest).getD j default).k) := h1
      rw [opened_at _ (next :: rest) s 1 j hj' hk, hidx j hj] at h2
      exact mem_listOf q _ h2
    · have hj' : j < (next :: rest).length := by
        simp only [List.length_cons] at hj ⊢
        omega
      have h3 := fits_at _ (next :: rest) s 1 j hj' hk hF
      rw [hidx j hj] at h3
      exact h3

/-- (8) **So `budBoth` gives `testBud`, at every number.** -/
theorem test_of_both {Pb : Type} (Js : SimJob Pb) (hOk : StagesOk Js.p.nums.stages = true) (n : ℕ)
    (ds : List Fmt.Drawn) (asks : List (List (List ℕ)))
    (hF : n = 1 → FitsBody (laterOf Js.p.nums.stages ds) (Js.p.nums.stages.drop 1)
      (Js.p.nums.stages.headD default) 1)
    (h : budBoth Js n ds asks) : testBud Js n ds asks := by
  refine ⟨h.1, fun e => ?_⟩
  subst e
  exact rest_of_opened Js.p.nums.stages hOk ds asks (hF rfl) h.2

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.readOf
#print axioms ProofFile.Honest.K12.Light.different_aux
#print axioms ProofFile.Honest.K12.Light.different_sub
#print axioms ProofFile.Honest.K12.Light.budRest_of_sub
#print axioms ProofFile.Honest.K12.Light.budDue
#print axioms ProofFile.Honest.K12.Light.okFrom_low
#print axioms ProofFile.Honest.K12.Light.stages_low
#print axioms ProofFile.Honest.K12.Light.sum_take
#print axioms ProofFile.Honest.K12.Light.openedTr_here
#print axioms ProofFile.Honest.K12.Light.openedTr_later
#print axioms ProofFile.Honest.K12.Light.pick_succ
#print axioms ProofFile.Honest.K12.Light.opened_at
#print axioms ProofFile.Honest.K12.Light.fits_at
#print axioms ProofFile.Honest.K12.Light.rest_of_opened
#print axioms ProofFile.Honest.K12.Light.test_of_both
