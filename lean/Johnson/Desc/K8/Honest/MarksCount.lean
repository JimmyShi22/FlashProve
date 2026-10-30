-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/MarksCount.lean: THE SMALLNESS TEST: THE LIBRARY's LIST OF READS IS AS LONG
AS THE TILING TEST's TWO NUMBERS OF SEGMENTS TOGETHER (`readsList`,
OnBytes/Tie/Pv/Tail/EndLoops.lean; `tablesTile`, OnBytes/Model/Tail.lean). Lemmas; none of the
library's goals.

  `length_reads`   the list's length: each table on a matrix of the list and on vector 0 or 2 counts
                   once for each of its segments
  `walk_segs`      the tiling's walk adds up the segments of the stretches that it passes
  `tile_segs`      a yes of the tiling test on a vector yields the sum of its tables' segments
  `count_of_tile`  each table lies on a matrix of the list; the tiling test says yes on vectors 0
                   and 2, with s1 and s3 segments: then the list of reads has s1 + s3 members
Limits. Nothing says that the tables tile at any state of a run.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqTailReturns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest.Marks
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open OnBytes.Tie.Pv.Tail.Port (readsList segsOf)

/-! ## 1 The length of the list of reads -/

theorem length_flatMap' {α β : Type} (f : α → List β) : ∀ l : List α,
    (l.flatMap f).length = (l.map fun a => (f a).length).sum
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.length_append, length_flatMap' f l, List.map_cons, List.sum_cons]

theorem length_segsOf (tl : HTailF2) (mu un : Nat) (Fn : HFun) :
    (segsOf tl mu un Fn).length =
      if (Fn.mat == mu && Fn.tree == un) = true then segs tl Fn else 0 := by
  unfold segsOf
  by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
  · rw [if_pos hc, if_pos hc, List.length_map, List.length_range]
    have hm : Fn.mat = mu := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hc.1
    subst hm
    rfl
  · rw [if_neg hc, if_neg hc]
    rfl

theorem length_flat (tl : HTailF2) (mu un : Nat) : ∀ T : List HFun,
    (T.flatMap (segsOf tl mu un)).length =
      ((T.filter fun Fn => Fn.mat == mu && Fn.tree == un).map (segs tl)).sum
  | [] => rfl
  | Fn :: T => by
    rw [List.flatMap_cons, List.length_append, length_segsOf, length_flat tl mu un T,
      List.filter_cons]
    by_cases hc : (Fn.mat == mu && Fn.tree == un) = true
    · rw [if_pos hc, if_pos hc, List.map_cons, List.sum_cons]
    · rw [if_neg hc, if_neg hc, Nat.zero_add]

theorem filt_succ (n un : Nat) (v : HFun → Nat) : ∀ T : List HFun,
    ((T.filter fun Fn => decide (Fn.mat < n + 1) && Fn.tree == un).map v).sum =
      ((T.filter fun Fn => decide (Fn.mat < n) && Fn.tree == un).map v).sum +
        ((T.filter fun Fn => Fn.mat == n && Fn.tree == un).map v).sum
  | [] => rfl
  | Fn :: T => by
    have ih := filt_succ n un v T
    simp only [List.filter_cons, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    split_ifs <;> (try simp only [List.map_cons, List.sum_cons]) <;> omega

theorem sum_below (un : Nat) (v : HFun → Nat) (T : List HFun) : ∀ n : Nat,
    ((List.range n).map fun mu =>
      ((T.filter fun Fn => Fn.mat == mu && Fn.tree == un).map v).sum).sum =
      ((T.filter fun Fn => decide (Fn.mat < n) && Fn.tree == un).map v).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_below un v T n, filt_succ]
    simp

/-- The length of the list of reads. -/
theorem length_reads (tl : HTailF2) (funs : Array HFun) :
    (readsList tl funs).length =
      ((funs.toList.filter fun Fn => decide (Fn.mat < tl.NM) && Fn.tree == 0).map (segs tl)).sum +
        ((funs.toList.filter fun Fn => decide (Fn.mat < tl.NM) && Fn.tree == 2).map (segs tl)).sum
    := by
  unfold readsList
  rw [length_flatMap']
  have e : ∀ mu, (([0, 2] : List Nat).flatMap fun un =>
      funs.toList.flatMap (segsOf tl mu un)).length =
      ((funs.toList.filter fun Fn => Fn.mat == mu && Fn.tree == 0).map (segs tl)).sum +
        ((funs.toList.filter fun Fn => Fn.mat == mu && Fn.tree == 2).map (segs tl)).sum := by
    intro mu
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append,
      length_flat]
  simp only [e]
  rw [List.sum_map_add, sum_below, sum_below]

/-! ## 2 The tiling's walk counts the segments -/

theorem foldl_none {α β : Type} (f : Option β → α → Option β) (hn : ∀ x, f none x = none) :
    ∀ xs : List α, xs.foldl f none = none
  | [] => rfl
  | x :: xs => by rw [List.foldl_cons, hn, foldl_none f hn xs]

theorem walk_segs {f : Option (Nat × Nat) → Nat × Nat × Nat → Option (Nat × Nat)}
    (hn : ∀ x, f none x = none)
    (hs : ∀ p s x, f (some (p, s)) x =
      if (x.2.1 != 0 && x.1 == p) = true then some (p + x.2.1, s + x.2.2) else none) :
    ∀ (xs : List (Nat × Nat × Nat)) (p s p' s' : Nat), xs.foldl f (some (p, s)) = some (p', s') →
      s' = s + (xs.map fun x => x.2.2).sum
  | [], p, s, p', s', h => by
    have e : (p, s) = (p', s') := Option.some.inj h
    exact (congrArg Prod.snd e).symm
  | x :: xs, p, s, p', s', h => by
    rw [List.foldl_cons, hs] at h
    by_cases hc : (x.2.1 != 0 && x.1 == p) = true
    · rw [if_pos hc] at h
      rw [walk_segs hn hs xs _ _ _ _ h, List.map_cons, List.sum_cons]
      omega
    · rw [if_neg hc, foldl_none f hn] at h
      cases h

/-- A yes of the tiling test yields the sum of the tables' segments. -/
theorem tile_segs {tl : HTailF2} {funs : Array HFun} {un s : Nat}
    (h : tl.tablesTile funs un = some s) :
    ((funs.toList.filter fun Fn => Fn.tree == un).map (segs tl)).sum = s := by
  unfold HTailF2.tablesTile at h
  dsimp only at h
  obtain ⟨⟨p, sg⟩, hw, he⟩ := Option.bind_eq_some_iff.1 h
  have w := walk_segs (fun _ => rfl) (fun _ _ _ => rfl) _ _ _ _ _ hw
  dsimp only at he
  split at he
  · have hsg : sg = s := Option.some.inj he
    rw [((List.mergeSort_perm _ _).map fun x : Nat × Nat × Nat => x.2.2).sum_eq, List.map_map]
      at w
    have w' : sg = 0 + ((funs.toList.filter fun Fn => Fn.tree == un).map (segs tl)).sum := w
    omega
  · cases he

/-! ## 3 The count -/

/-- **The list of reads has as many members as the tables have segments.** -/
theorem count_of_tile {tl : HTailF2} {funs : Array HFun} {s1 s3 : Nat}
    (hin : ∀ Fn ∈ funs.toList, Fn.mat < tl.NM) (h0 : tl.tablesTile funs 0 = some s1)
    (h2 : tl.tablesTile funs 2 = some s3) : (readsList tl funs).length = s1 + s3 := by
  have e : ∀ un, (funs.toList.filter fun Fn => decide (Fn.mat < tl.NM) && Fn.tree == un) =
      funs.toList.filter fun Fn => Fn.tree == un := fun un =>
    List.filter_congr fun Fn h => by rw [decide_eq_true (hin Fn h), Bool.true_and]
  rw [length_reads, e, e, tile_segs h0, tile_segs h2]

end VerifiableInference.Desc.First.K8.Honest.Marks

#print axioms VerifiableInference.Desc.First.K8.Honest.Marks.length_reads
#print axioms VerifiableInference.Desc.First.K8.Honest.Marks.tile_segs
#print axioms VerifiableInference.Desc.First.K8.Honest.Marks.count_of_tile
