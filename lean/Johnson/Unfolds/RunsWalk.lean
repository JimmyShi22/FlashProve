-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/RunsWalk.lean: TWO WALKS ALONG A LIST WRITTEN AS RUNS (`expand`,
Johnson/G/Runs.lean), SO THAT THE LIST NEED NOT BE LAID OUT: general laws; nothing is evaluated.

  `seedsR q k l`: the members with q, each with its number (counted from k): one walk along the
    runs. **`zipIdx_filter_expand`**: ((expand l).zipIdx k).filter (fun x => q x.1) = seedsR q k l.
  `getR l j`: member number j: one walk along the runs. **`getElem?_expand`**: (expand l)[j]? = getR
    l j.
  `seedsN q k l`: the members with q, each with its number AND THE MEMBER BEHIND IT: ONE WALK.
  **`seedsN_zero`**:
    seedsN q 0 l = (seedsR q 0 l).map fun r => (r, getR l (r.2 + 1)).
  `zipIdx_filter_unrunG` | `getElem?_unrunG`: the same at unrunG recs runs, over valRuns recs runs.

Limits. That Lean's kernel gets through a given list of runs is seen where a theorem is checked.
Nothing on soundness.
-/
import Johnson.G.Runs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds

open Johnson.G (force force_eq)
open Johnson.G.Runs (expand valRuns unrunG unrunG_eq)

variable {α : Type}

/-- The members with q, each with its number, along the runs. The number is evaluated at each run.
-/
def seedsR (q : α → Bool) : Nat → List (Nat × α) → List (α × Nat)
  | _, [] => []
  | k, x :: xs =>
    (if q x.2 then (List.range' k x.1).map fun i => (x.2, i) else []) ++
      force (k + x.1) fun v => seedsR q v xs

/-- Member number j, along the runs. What is left of the number is evaluated at each run. -/
def getR : List (Nat × α) → Nat → Option α
  | [], _ => none
  | x :: xs, j => if j < x.1 then some x.2 else force (j - x.1) fun v => getR xs v

theorem zipIdx_replicate (r : α) : ∀ (c k : Nat),
    (List.replicate c r).zipIdx k = (List.range' k c).map fun i => (r, i)
  | 0, _ => rfl
  | c + 1, k => by
    rw [List.replicate_succ, List.zipIdx_cons, List.range'_succ, List.map_cons,
      zipIdx_replicate r c (k + 1)]

theorem filter_run (q : α → Bool) (r : α) (c k : Nat) :
    ((List.replicate c r).zipIdx k).filter (fun x => q x.1) =
      if q r then (List.range' k c).map fun i => (r, i) else [] := by
  rw [zipIdx_replicate]
  by_cases h : q r = true
  · rw [if_pos h]
    refine List.filter_eq_self.2 fun x hx => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact h
  · rw [if_neg h]
    refine List.filter_eq_nil_iff.2 fun x hx => ?_
    obtain ⟨i, _, rfl⟩ := List.mem_map.1 hx
    exact h

/-- **The members with q and their numbers, along the runs.** -/
theorem zipIdx_filter_expand (q : α → Bool) : ∀ (l : List (Nat × α)) (k : Nat),
    ((expand l).zipIdx k).filter (fun x => q x.1) = seedsR q k l
  | [], _ => rfl
  | x :: xs, k => by
    show ((List.replicate x.1 x.2 ++ expand xs).zipIdx k).filter (fun y => q y.1) =
      (if q x.2 then (List.range' k x.1).map fun i => (x.2, i) else []) ++
        force (k + x.1) fun v => seedsR q v xs
    rw [List.zipIdx_append, List.filter_append, filter_run, List.length_replicate, force_eq,
      zipIdx_filter_expand q xs (k + x.1)]

/-- **Member number j, along the runs.** -/
theorem getElem?_expand : ∀ (l : List (Nat × α)) (j : Nat), (expand l)[j]? = getR l j
  | [], _ => rfl
  | x :: xs, j => by
    show (List.replicate x.1 x.2 ++ expand xs)[j]? =
      if j < x.1 then some x.2 else force (j - x.1) fun v => getR xs v
    rw [force_eq]
    by_cases h : j < x.1
    · rw [if_pos h, List.getElem?_append_left (by rw [List.length_replicate]; exact h),
        List.getElem?_replicate, if_pos h]
    · rw [if_neg h, List.getElem?_append_right (by rw [List.length_replicate]; omega),
        List.length_replicate, getElem?_expand xs (j - x.1)]

/-! ## The members with q, each with its number AND THE MEMBER BEHIND IT: one walk -/

/-- The first member, along the runs. -/
def nextR : List (Nat × α) → Option α
  | [] => none
  | x :: xs => if x.1 = 0 then nextR xs else some x.2

/-- The members with q, each with its number and the member behind it, along the runs: ONE WALK. -/
def seedsN (q : α → Bool) : Nat → List (Nat × α) → List ((α × Nat) × Option α)
  | _, [] => []
  | k, x :: xs =>
    (if q x.2 then (List.range' k x.1).map fun i =>
        ((x.2, i), if i + 1 < k + x.1 then some x.2 else nextR xs) else []) ++
      force (k + x.1) fun v => seedsN q v xs

theorem nextR_eq : ∀ l : List (Nat × α), nextR l = (expand l)[0]?
  | [] => rfl
  | x :: xs => by
    show (if x.1 = 0 then nextR xs else some x.2) = (List.replicate x.1 x.2 ++ expand xs)[0]?
    by_cases h : x.1 = 0
    · rw [if_pos h, h, List.replicate_zero, List.nil_append, nextR_eq xs]
    · rw [if_neg h, List.getElem?_append_left (by rw [List.length_replicate]; omega),
        List.getElem?_replicate, if_pos (by omega)]

theorem seedsR_ge (q : α → Bool) : ∀ (l : List (Nat × α)) (k : Nat), ∀ r ∈ seedsR q k l, k ≤ r.2
  | [], _, r, h => nomatch h
  | x :: xs, k, r, h => by
    have h' : r ∈ (if q x.2 then (List.range' k x.1).map fun i => (x.2, i) else []) ++
        force (k + x.1) fun v => seedsR q v xs := h
    rw [force_eq, List.mem_append] at h'
    rcases h' with h1 | h2
    · by_cases c : q x.2 = true
      · rw [if_pos c] at h1
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h1
        exact (List.mem_range'_1.1 hi).1
      · rw [if_neg c] at h1
        exact nomatch h1
    · have := seedsR_ge q xs (k + x.1) r h2
      omega

/-- **One walk gives what the two give.** -/
theorem seedsN_eq (q : α → Bool) : ∀ (l : List (Nat × α)) (k : Nat),
    seedsN q k l = (seedsR q k l).map fun r => (r, (expand l)[r.2 + 1 - k]?)
  | [], _ => rfl
  | x :: xs, k => by
    show (if q x.2 then (List.range' k x.1).map fun i =>
        ((x.2, i), if i + 1 < k + x.1 then some x.2 else nextR xs) else []) ++
        (force (k + x.1) fun v => seedsN q v xs) =
      ((if q x.2 then (List.range' k x.1).map fun i => (x.2, i) else []) ++
        force (k + x.1) fun v => seedsR q v xs).map
          fun r => (r, (List.replicate x.1 x.2 ++ expand xs)[r.2 + 1 - k]?)
    rw [force_eq, force_eq, List.map_append, seedsN_eq q xs (k + x.1)]
    congr 1
    · by_cases c : q x.2 = true
      · rw [if_pos c, if_pos c, List.map_map]
        refine List.map_congr_left fun i hi => ?_
        obtain ⟨h1, h2⟩ := List.mem_range'_1.1 hi
        show ((x.2, i), if i + 1 < k + x.1 then some x.2 else nextR xs) =
          ((x.2, i), (List.replicate x.1 x.2 ++ expand xs)[i + 1 - k]?)
        by_cases d : i + 1 < k + x.1
        · rw [if_pos d, List.getElem?_append_left (by rw [List.length_replicate]; omega),
            List.getElem?_replicate, if_pos (by omega)]
        · rw [if_neg d, List.getElem?_append_right (by rw [List.length_replicate]; omega),
            List.length_replicate, nextR_eq, show i + 1 - k - x.1 = 0 by omega]
      · rw [if_neg c, if_neg c]
        rfl
    · refine List.map_congr_left fun r hr => ?_
      have hg := seedsR_ge q xs (k + x.1) r hr
      rw [List.getElem?_append_right (by rw [List.length_replicate]; omega),
        List.length_replicate, show r.2 + 1 - k - x.1 = r.2 + 1 - (k + x.1) by omega]

theorem seedsN_zero (q : α → Bool) (l : List (Nat × α)) :
    seedsN q 0 l = (seedsR q 0 l).map fun r => (r, getR l (r.2 + 1)) := by
  rw [seedsN_eq]
  refine List.map_congr_left fun r _ => ?_
  rw [Nat.sub_zero, getElem?_expand]

theorem zipIdx_filter_unrunG (q : α → Bool) (recs : List α) (runs : List (Nat × Nat)) (k : Nat) :
    ((unrunG recs runs).zipIdx k).filter (fun x => q x.1) = seedsR q k (valRuns recs runs) := by
  rw [unrunG_eq, zipIdx_filter_expand]

theorem getElem?_unrunG (recs : List α) (runs : List (Nat × Nat)) (j : Nat) :
    (unrunG recs runs)[j]? = getR (valRuns recs runs) j := by
  rw [unrunG_eq, getElem?_expand]

end Johnson.Unfolds

#print axioms Johnson.Unfolds.zipIdx_filter_expand
#print axioms Johnson.Unfolds.getElem?_expand
#print axioms Johnson.Unfolds.nextR_eq
#print axioms Johnson.Unfolds.seedsR_ge
#print axioms Johnson.Unfolds.seedsN_eq
#print axioms Johnson.Unfolds.seedsN_zero
#print axioms Johnson.Unfolds.zipIdx_filter_unrunG
#print axioms Johnson.Unfolds.getElem?_unrunG
