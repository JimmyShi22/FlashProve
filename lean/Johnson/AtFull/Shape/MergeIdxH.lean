-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/MergeIdxH.lean: `mergeIdx` (Johnson/Desc/First/Shape/Makes.lean: a list of
numbers sorted, each number kept once) ONCE MORE, WITH A HINT: `mergeIdxH runs l`: WHERE THE HINT
PASSES A TEST THAT RUNS NO SORT, THE HINT WRITTEN OUT; ELSE mergeIdx l. AND THE TWO ARE EQUAL AT
EVERY HINT AND EVERY LIST: `mergeIdx_H`. No premise. Nine definitions, 14 theorems, six small tests
and one use of the law. It imports Makes.lean and Mathlib's Data/List/Sort.lean.

Purpose. mergeIdx sorts by List.mergeSort. Lean's kernel does not evaluate that sort; rewritten by
`Johnson.Unfolds.mergeSort_eq` it does, at a price: in a timed run at 33,501 numbers some three
minutes and 20 GB (seen in a run; not shown here). Where the value is known beforehand, the sort
need not be run to check it: a list that rises strictly and has l's members IS mergeIdx l. Whoever
has to evaluate a text that calls mergeIdx may rewrite by mergeIdx_H at a hint first.

The hint. A list of runs: (a, n) stands for a, a + 1, …, a + n - 1. The test `hintOk`: each run ends
at or below the next one's start; every member of l lies in a run; every place in the runs is met by
a member of l. The last is asked by one number: bit i is set where a member of l has the place i
among the runs' members (`posR`, `maskOf`), and the number must be 2 ^ (the number of places) - 1.
So the number has as many bits as the value has members, however large the members are.

WHERE A WRITER GETS THE HINT: off the value itself, by a program outside the library: for one, off
the written shape behind the step that calls mergeIdx. A HINT IS NO PREMISE AND NEEDS NO TRUST: the
law holds at every hint. A wrong hint fails the test, and the text falls back to mergeIdx: the value
is the same, the sort is run.

Main names.
* `totalR`, `expandR`, `runsOk`, `inRuns`, `posR`, `maskOf`, `hintOk`: the test's parts.
  **`mergeIdxH`**.
* `mergeIdx_spec`: mergeIdx l rises strictly and has l's members; over `fold_spec`, on the fold that
  drops a neighbour's repeat (`stepD`: that fold's step, by name).
* `expandR_rises`, `mem_expandR`: runs that rise, written out, rise strictly; their members.
  `posR_lt`, `posR_inj`: a member's place is below the number of places; two members with one place
  are one. `maskOf_testBit`.
* `hint_mem`: where the test accepts, the hint written out has l's members.
* **`mergeIdx_H`**: mergeIdx l = mergeIdxH runs l. By Mathlib's `List.Pairwise.eq_of_mem_iff`.

Limits. An equality of two functions. Nothing is said on what either costs. THE FALLBACK STILL HOLDS
THE CORE's SORT: whoever evaluates by the kernel at a hint that may fail rewrites that sort too. A
HINT WHOSE RUNS RISE AND COVER l BUT ARE FAR TOO LONG passes the test's first two clauses, and the
third must then make 2 ^ (the runs' total length) before it can say no: the value is still right;
the evaluation may not end in practice. A value that is not made of few runs wants a long hint: the
test walks the runs twice for each member of l (inRuns, posR). Seven `decide +kernel` stand in the
tests and the use: whoever counts such lines counts them. The small tests are at lists of at most
seven members; THE FALLBACK's VALUE IS TESTED NOWHERE BY EVALUATION (the kernel does not evaluate
the core's sort): that the fallback is taken at a wrong hint is. Nothing on soundness, completeness
or hiding.
-/
import Johnson.Desc.First.Shape.Makes
import Mathlib.Data.List.Sort

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape.MergeIdxH
open VerifiableInference.Desc.First.Shape (mergeIdx)

/-! ## 1 The text with a hint -/

/-- How many members the runs have. A run (a, n) is a, a + 1, …, a + n - 1; a run of length 0 has
no member and does no harm. -/
def totalR : List (Nat × Nat) → Nat
  | [] => 0
  | r :: rs => r.2 + totalR rs

/-- The runs written out. -/
def expandR : List (Nat × Nat) → List Nat
  | [] => []
  | r :: rs => List.range' r.1 r.2 ++ expandR rs

/-- Each run ends at or below the next one's start. -/
def runsOk : List (Nat × Nat) → Bool
  | r :: s :: rs => Nat.ble (r.1 + r.2) s.1 && runsOk (s :: rs)
  | _ => true

/-- x lies in one of the runs. -/
def inRuns (runs : List (Nat × Nat)) (x : Nat) : Bool :=
  runs.any fun r => Nat.ble r.1 x && Nat.blt x (r.1 + r.2)

/-- A member's place among the runs' members, from 0. At a number that lies in no run the value
means nothing (in front of a run it is that run's first member's place, by the cut-off subtraction;
behind all runs it is the number of places): hintOk asks posR of l's members alone, behind the test
that each lies in a run. -/
def posR : List (Nat × Nat) → Nat → Nat
  | [], _ => 0
  | r :: rs, x => if Nat.blt x (r.1 + r.2) then x - r.1 else r.2 + posR rs x

/-- The members of a list as the bits of one number. -/
def maskOf (l : List Nat) : Nat := l.foldl (fun m x => m ||| (1 <<< x)) 0

/-- The test on a hint: the runs rise; every member of l lies in a run; every place in the runs is
met by a member of l. -/
def hintOk (runs : List (Nat × Nat)) (l : List Nat) : Bool :=
  runsOk runs && l.all (inRuns runs) && maskOf (l.map (posR runs)) == 2 ^ totalR runs - 1

/-- **mergeIdx with a hint**: where the hint passes the test, the hint written out; else
mergeIdx. -/
def mergeIdxH (runs : List (Nat × Nat)) (l : List Nat) : List Nat :=
  if hintOk runs l then expandR runs else mergeIdx l

/-! ## 2 What mergeIdx returns -/

/-- The step of mergeIdx's fold. -/
def stepD (acc : List Nat) (a : Nat) : List Nat :=
  match acc with
  | b :: r => if a == b then b :: r else a :: acc
  | [] => [a]

/-- The fold over a rising list, from a falling stack that lies at or below it: a falling stack with
the members of both. -/
theorem fold_spec : ∀ (s acc : List Nat), s.Pairwise (· ≤ ·) → acc.Pairwise (· > ·) →
    (∀ b ∈ acc, ∀ a ∈ s, b ≤ a) →
    (s.foldl stepD acc).Pairwise (· > ·) ∧ ∀ x, x ∈ s.foldl stepD acc ↔ x ∈ acc ∨ x ∈ s
  | [], acc, _, h2, _ => ⟨h2, fun x => by simp⟩
  | a :: s, acc, h1, h2, h3 => by
    obtain ⟨ha, hs⟩ := List.pairwise_cons.1 h1
    rw [List.foldl_cons]
    cases acc with
    | nil =>
      have e0 : stepD [] a = [a] := rfl
      rw [e0]
      obtain ⟨p, m⟩ := fold_spec s [a] hs (List.pairwise_singleton _ _)
        (fun b hb c hc => by rw [List.mem_singleton.1 hb]; exact ha c hc)
      exact ⟨p, fun x => by rw [m]; simp⟩
    | cons b r =>
      have hba : b ≤ a := h3 b (List.mem_cons_self ..) a (List.mem_cons_self ..)
      by_cases e : a = b
      · have e' : stepD (b :: r) a = b :: r := by simp [stepD, e]
        rw [e']
        obtain ⟨p, m⟩ := fold_spec s (b :: r) hs h2
          (fun c hc d hd => h3 c hc d (List.mem_cons_of_mem _ hd))
        refine ⟨p, fun x => ?_⟩
        rw [m, e]
        simp only [List.mem_cons]
        tauto
      · have e' : stepD (b :: r) a = a :: b :: r := by simp [stepD, e]
        rw [e']
        obtain ⟨hb, -⟩ := List.pairwise_cons.1 h2
        have hlt : b < a := Nat.lt_of_le_of_ne hba (Ne.symm e)
        obtain ⟨p, m⟩ := fold_spec s (a :: b :: r) hs
          (List.pairwise_cons.2 ⟨fun c hc => by
            rcases List.mem_cons.1 hc with rfl | hc
            · exact hlt
            · exact Nat.lt_trans (hb c hc) hlt, h2⟩)
          (fun c hc d hd => by
            rcases List.mem_cons.1 hc with rfl | hc
            · exact ha d hd
            · exact h3 c hc d (List.mem_cons_of_mem _ hd))
        refine ⟨p, fun x => ?_⟩
        rw [m]
        simp only [List.mem_cons]
        tauto

/-- **mergeIdx l rises strictly and has l's members.** -/
theorem mergeIdx_spec (l : List Nat) :
    (mergeIdx l).Pairwise (· < ·) ∧ ∀ x, x ∈ mergeIdx l ↔ x ∈ l := by
  have hs : (l.mergeSort fun a b => decide (a ≤ b)).Pairwise (· ≤ ·) := by
    have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c h1 h2 => by simp only [decide_eq_true_eq] at *; omega)
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) l
    exact this.imp fun h => by simpa using h
  obtain ⟨p, m⟩ := fold_spec _ [] hs List.Pairwise.nil (fun b hb => by simp at hb)
  have e : mergeIdx l = ((l.mergeSort fun a b => decide (a ≤ b)).foldl stepD []).reverse := rfl
  rw [e]
  refine ⟨List.pairwise_reverse.2 p, fun x => ?_⟩
  rw [List.mem_reverse, m]
  simp

/-! ## 3 The runs -/

/-- inRuns, said with "there is". -/
theorem inRuns_iff (runs : List (Nat × Nat)) (x : Nat) :
    inRuns runs x = true ↔ ∃ r ∈ runs, r.1 ≤ x ∧ x < r.1 + r.2 := by
  simp [inRuns, Nat.ble_eq, Nat.blt_eq]

/-- The members of the runs written out are the numbers that lie in a run. -/
theorem mem_expandR : ∀ (runs : List (Nat × Nat)) (x : Nat),
    x ∈ expandR runs ↔ inRuns runs x = true
  | [], x => by simp [expandR, inRuns]
  | r :: rs, x => by
    rw [expandR, List.mem_append, mem_expandR rs x, List.mem_range'_1, inRuns_iff, inRuns_iff]
    simp

/-- Behind a run every later run's members lie at or above its end. -/
theorem above : ∀ (rs : List (Nat × Nat)) (r : Nat × Nat), runsOk (r :: rs) = true →
    ∀ x, inRuns rs x = true → r.1 + r.2 ≤ x
  | [], _, _, x, h => by simp [inRuns] at h
  | s :: rs, r, h, x, hx => by
    simp only [runsOk, Bool.and_eq_true, Nat.ble_eq] at h
    obtain ⟨t, ht, h1, h2⟩ := (inRuns_iff _ _).1 hx
    rcases List.mem_cons.1 ht with rfl | ht
    · omega
    · have := above rs s h.2 x ((inRuns_iff _ _).2 ⟨_, ht, h1, h2⟩)
      omega

/-- Runs that rise still rise without the first. -/
theorem runsOk_tail {r : Nat × Nat} {rs : List (Nat × Nat)} (h : runsOk (r :: rs) = true) :
    runsOk rs = true := by
  cases rs with
  | nil => rfl
  | cons s rs =>
    simp only [runsOk, Bool.and_eq_true] at h
    exact h.2

/-- **Runs that rise, written out, rise strictly.** -/
theorem expandR_rises : ∀ (runs : List (Nat × Nat)), runsOk runs = true →
    (expandR runs).Pairwise (· < ·)
  | [], _ => List.Pairwise.nil
  | r :: rs, h => by
    rw [expandR, List.pairwise_append]
    refine ⟨List.pairwise_lt_range', expandR_rises rs (runsOk_tail h), fun a ha b hb => ?_⟩
    have h1 := (List.mem_range'_1.1 ha).2
    have h2 := above rs r h b ((mem_expandR rs b).1 hb)
    omega

/-- In or behind the first run. -/
theorem inRuns_cons {r : Nat × Nat} {rs : List (Nat × Nat)} {x : Nat}
    (h : runsOk (r :: rs) = true) (hx : inRuns (r :: rs) x = true) :
    (r.1 ≤ x ∧ x < r.1 + r.2) ∨ (r.1 + r.2 ≤ x ∧ inRuns rs x = true) := by
  obtain ⟨t, ht, h1, h2⟩ := (inRuns_iff _ _).1 hx
  rcases List.mem_cons.1 ht with rfl | ht
  · exact .inl ⟨h1, h2⟩
  · have hr := (inRuns_iff rs x).2 ⟨t, ht, h1, h2⟩
    exact .inr ⟨above rs r h x hr, hr⟩

/-- A member's place is below the number of members. -/
theorem posR_lt : ∀ (runs : List (Nat × Nat)) (x : Nat), runsOk runs = true →
    inRuns runs x = true → posR runs x < totalR runs
  | [], x, _, h => by simp [inRuns] at h
  | r :: rs, x, h, hx => by
    rcases inRuns_cons h hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : Nat.blt x (r.1 + r.2) = true := by simpa [Nat.blt_eq] using h2
      simp only [posR, this, if_true, totalR]
      omega
    · have : Nat.blt x (r.1 + r.2) = false := by
        rw [Bool.eq_false_iff]; simp only [ne_eq, Nat.blt_eq]; omega
      have ih := posR_lt rs x (runsOk_tail h) h2
      simp only [posR, this, totalR]
      simpa using ih

/-- Two members with one place are one. -/
theorem posR_inj : ∀ (runs : List (Nat × Nat)) (x y : Nat), runsOk runs = true →
    inRuns runs x = true → inRuns runs y = true → posR runs x = posR runs y → x = y
  | [], x, _, _, h, _, _ => by simp [inRuns] at h
  | r :: rs, x, y, h, hx, hy, e => by
    have T : ∀ z, z < r.1 + r.2 → posR (r :: rs) z = z - r.1 := fun z hz => by
      have : Nat.blt z (r.1 + r.2) = true := by simpa [Nat.blt_eq] using hz
      simp [posR, this]
    have F : ∀ z, r.1 + r.2 ≤ z → posR (r :: rs) z = r.2 + posR rs z := fun z hz => by
      have : Nat.blt z (r.1 + r.2) = false := by
        rw [Bool.eq_false_iff]; simp only [ne_eq, Nat.blt_eq]; omega
      simp [posR, this]
    rcases inRuns_cons h hx with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
      rcases inRuns_cons h hy with ⟨b1, b2⟩ | ⟨b1, b2⟩
    · rw [T x a2, T y b2] at e
      omega
    · rw [T x a2, F y b1] at e
      omega
    · rw [F x a1, T y b2] at e
      omega
    · rw [F x a1, F y b1] at e
      exact posR_inj rs x y (runsOk_tail h) a2 b2 (by omega)

/-! ## 4 The mask -/

/-- A bit of the fold: it was set at the start, or its number is a member. -/
theorem fold_testBit (i : Nat) : ∀ (l : List Nat) (m : Nat),
    (l.foldl (fun m x => m ||| (1 <<< x)) m).testBit i = (m.testBit i || decide (i ∈ l))
  | [], m => by simp
  | a :: l, m => by
    rw [List.foldl_cons, fold_testBit i l, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    by_cases h : a = i
    · subst h
      simp
    · have h' : ¬ i = a := fun e => h e.symm
      simp [h, h']

/-- Bit i of the mask is set just where i is a member. -/
theorem maskOf_testBit (l : List Nat) (i : Nat) : (maskOf l).testBit i = decide (i ∈ l) := by
  rw [maskOf, fold_testBit]
  simp

/-! ## 5 The law -/

/-- Where the test accepts, the hint written out has l's members. -/
theorem hint_mem {runs : List (Nat × Nat)} {l : List Nat} (h : hintOk runs l = true) (x : Nat) :
    x ∈ expandR runs ↔ x ∈ l := by
  simp only [hintOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  constructor
  · intro hx
    have hx' := (mem_expandR runs x).1 hx
    have hb : (maskOf (l.map (posR runs))).testBit (posR runs x) = true := by
      rw [h3, Nat.testBit_two_pow_sub_one]
      exact decide_eq_true (posR_lt runs x h1 hx')
    rw [maskOf_testBit, decide_eq_true_eq, List.mem_map] at hb
    obtain ⟨y, hy, e⟩ := hb
    rw [← posR_inj runs y x h1 (h2 y hy) hx' e]
    exact hy
  · intro hx
    exact (mem_expandR runs x).2 (h2 x hx)

/-- **THE LAW: mergeIdx IS mergeIdxH, AT EVERY HINT AND EVERY LIST.** -/
theorem mergeIdx_H (runs : List (Nat × Nat)) (l : List Nat) : mergeIdx l = mergeIdxH runs l := by
  unfold mergeIdxH
  by_cases h : hintOk runs l = true
  · rw [if_pos h]
    obtain ⟨p, m⟩ := mergeIdx_spec l
    have h1 : runsOk runs = true := by
      simp only [hintOk, Bool.and_eq_true] at h
      exact h.1.1
    exact List.Pairwise.eq_of_mem_iff p (expandR_rises runs h1) fun a => by rw [m, hint_mem h]
  · rw [if_neg h]

/-! ## 6 Six small tests of the text, by Lean's kernel; and one use of the law -/

/-- A right hint, at a list with repeats: the hint written out; no sort is run. -/
example : mergeIdxH [(0, 3), (7, 2)] [8, 1, 0, 7, 2, 1, 8] = [0, 1, 2, 7, 8] := by decide +kernel

/-- A USE OF THE LAW, no test of it: mergeIdx's own value there, had without its sort. -/
example : mergeIdx [8, 1, 0, 7, 2, 1, 8] = [0, 1, 2, 7, 8] :=
  (mergeIdx_H [(0, 3), (7, 2)] _).trans (by decide +kernel)

/-- Runs that touch pass: written out they still rise strictly. -/
example : mergeIdxH [(0, 2), (2, 2)] [3, 0, 2, 1] = [0, 1, 2, 3] := by decide +kernel

/-- A run of length 0 among the runs passes and adds nothing. -/
example : mergeIdxH [(0, 2), (5, 0), (7, 1)] [7, 1, 0] = [0, 1, 7] := by decide +kernel

/-- No member, no run. -/
example : mergeIdxH [] [] = [] := by decide +kernel

/-- Six wrong hints are refused: a member outside the runs; a place that no member meets; runs that
do not rise; runs that overlap; a run at the empty list; no run at a list with a member. -/
example : (hintOk [(0, 3)] [8, 1, 0, 2] || hintOk [(0, 4)] [1, 0, 2] ||
    hintOk [(7, 2), (0, 3)] [8, 1, 0, 7, 2] || hintOk [(0, 3), (2, 2)] [0, 1, 2, 3] ||
    hintOk [(0, 1)] [] || hintOk [] [0]) = false := by decide +kernel

/-- At a wrong hint the text is mergeIdx's: by the test's own no. -/
example : mergeIdxH [(0, 2)] [2, 0, 1] = mergeIdx [2, 0, 1] := if_neg (by decide +kernel)

end Johnson.AtFull.Shape.MergeIdxH

#print axioms Johnson.AtFull.Shape.MergeIdxH.fold_spec
#print axioms Johnson.AtFull.Shape.MergeIdxH.mergeIdx_spec
#print axioms Johnson.AtFull.Shape.MergeIdxH.inRuns_iff
#print axioms Johnson.AtFull.Shape.MergeIdxH.mem_expandR
#print axioms Johnson.AtFull.Shape.MergeIdxH.above
#print axioms Johnson.AtFull.Shape.MergeIdxH.runsOk_tail
#print axioms Johnson.AtFull.Shape.MergeIdxH.expandR_rises
#print axioms Johnson.AtFull.Shape.MergeIdxH.inRuns_cons
#print axioms Johnson.AtFull.Shape.MergeIdxH.posR_lt
#print axioms Johnson.AtFull.Shape.MergeIdxH.posR_inj
#print axioms Johnson.AtFull.Shape.MergeIdxH.fold_testBit
#print axioms Johnson.AtFull.Shape.MergeIdxH.maskOf_testBit
#print axioms Johnson.AtFull.Shape.MergeIdxH.hint_mem
#print axioms Johnson.AtFull.Shape.MergeIdxH.mergeIdx_H
#print axioms Johnson.AtFull.Shape.MergeIdxH.totalR
#print axioms Johnson.AtFull.Shape.MergeIdxH.expandR
#print axioms Johnson.AtFull.Shape.MergeIdxH.runsOk
#print axioms Johnson.AtFull.Shape.MergeIdxH.inRuns
#print axioms Johnson.AtFull.Shape.MergeIdxH.posR
#print axioms Johnson.AtFull.Shape.MergeIdxH.maskOf
#print axioms Johnson.AtFull.Shape.MergeIdxH.hintOk
#print axioms Johnson.AtFull.Shape.MergeIdxH.mergeIdxH
#print axioms Johnson.AtFull.Shape.MergeIdxH.stepD
