-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/UnitsIs.lean: for an attention segment's shape S, the number of units of the scores as
`unitsB S` counts it (Johnson/Desc/First/Link/K9RowsAsk.lean) is the field nKFp of the planner's counts
(`Attention.Counts.of S`, OnBytes/Model/AttentionPlan.lean). It holds for every shape: nothing is assumed about S.
Statements with their proofs; no definition; nothing is evaluated.

How. Both go through the shape's calls in list order. At a call of kind kfd both add one for each of the two segments
fm and fd that the call holds; at any other call both add nothing. The planner's step for a call of kind kr changes two
other fields alone. The induction along the calls has the frame of `units_fold`
(Johnson/Desc/First/Link/Law/K9PosAttPaid.lean), which bounds the same units by another count.

  `plane_keeps`, `planes_keep`, `kr_keeps`   the step for a call of kind kr leaves nKFp as it was
  `scores_held`, `scores_not_held`, `scores_count`   the step for a call of kind kfd adds the number of the listed
      segments that the call holds
  `call_kfd`, `call_other`   one call
  `units_fold_is`   a list of calls, whatever number its first call bears and whatever counts the pass starts from
  `units_is`   the end: unitsB S = (Attention.Counts.of S).nKFp

Limits. The other four fields of the counts are not spoken of. Nothing is said on whether a shape's calls are the ones
that a verifier runs. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or
hiding.
-/
import Johnson.Desc.First.Link.Law.K9PosAttPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9

open OnBytes OnBytes.Model
open VerifiableInference.Desc.K9Asks (unitsB)

/-! ## 1 The step for a call of kind kr -/

/-- `Counts.plane`, the planner's step for one segment of a call of kind kr, leaves nKFp as it was, at any call. -/
theorem plane_keeps (k : Attention.ACall) (x : Attention.Counts) (s : Attention.Seg) :
    (Attention.Counts.plane k x s).nKFp = x.nKFp := by
  unfold Attention.Counts.plane
  split <;> rfl

/-- So does that step taken along a list of segments. -/
theorem planes_keep (k : Attention.ACall) : ∀ (l : List Attention.Seg) (x : Attention.Counts),
    (l.foldl (Attention.Counts.plane k) x).nKFp = x.nKFp
  | [], _ => rfl
  | s :: l, x => by
    rw [List.foldl_cons, planes_keep k l, plane_keeps]

/-- The first half of one call's step leaves nKFp as it was. -/
theorem kr_keeps (k : Attention.ACall) (x : Attention.Counts) :
    (if k.kind == Attention.Table.kr then
      [Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) x else x).nKFp = x.nKFp := by
  split
  · exact planes_keep k _ x
  · rfl

/-! ## 2 The step for a call of kind kfd -/

/-- `Counts.scores`, the planner's step for one segment of a call of kind kfd, adds one to nKFp if the call holds it. -/
theorem scores_held (S : Attention.Shape) (k : Attention.ACall) (x : Attention.Counts) {s : Attention.Seg}
    (h : k.holds s = true) : (Attention.Counts.scores S k x s).nKFp = x.nKFp + 1 := by
  unfold Attention.Counts.scores
  split
  · rfl
  · rename_i h'
    exact absurd h h'

/-- That step leaves nKFp as it was if the call does not hold the segment. -/
theorem scores_not_held (S : Attention.Shape) (k : Attention.ACall) (x : Attention.Counts) {s : Attention.Seg}
    (h : ¬ k.holds s = true) : (Attention.Counts.scores S k x s).nKFp = x.nKFp := by
  unfold Attention.Counts.scores
  split
  · rename_i h'
    exact absurd h' h
  · rfl

/-- Taken along a list of segments, that step adds to nKFp the number of the list's members that the call holds. -/
theorem scores_count (S : Attention.Shape) (k : Attention.ACall) :
    ∀ (l : List Attention.Seg) (x : Attention.Counts),
      (l.foldl (Attention.Counts.scores S k) x).nKFp = x.nKFp + (l.filter fun s => k.holds s).length
  | [], _ => rfl
  | s :: l, x => by
    rw [List.foldl_cons, scores_count S k l]
    by_cases h : k.holds s = true
    · rw [scores_held S k x h, List.filter_cons_of_pos (p := fun s => k.holds s) h, List.length_cons]
      omega
    · rw [scores_not_held S k x h, List.filter_cons_of_neg (p := fun s => k.holds s) h]

/-! ## 3 One call -/

/-- A call of kind kfd adds to nKFp the number of the segments fm and fd that it holds. -/
theorem call_kfd (S : Attention.Shape) (x : Attention.Counts) (k : Attention.ACall)
    (hk : (k.kind == Attention.Table.kfd) = true) :
    (Attention.Counts.call S x k).nKFp =
      x.nKFp + ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => k.holds s).length := by
  show (if k.kind == Attention.Table.kfd then
      [Attention.Seg.fm, Attention.Seg.fd].foldl (Attention.Counts.scores S k)
        (if k.kind == Attention.Table.kr then
          [Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) x else x)
    else
      (if k.kind == Attention.Table.kr then
        [Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) x else x)).nKFp = _
  rw [if_pos hk, scores_count, kr_keeps]

/-- A call of another kind leaves nKFp as it was. -/
theorem call_other (S : Attention.Shape) (x : Attention.Counts) (k : Attention.ACall)
    (hk : ¬ (k.kind == Attention.Table.kfd) = true) : (Attention.Counts.call S x k).nKFp = x.nKFp := by
  show (if k.kind == Attention.Table.kfd then
      [Attention.Seg.fm, Attention.Seg.fd].foldl (Attention.Counts.scores S k)
        (if k.kind == Attention.Table.kr then
          [Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) x else x)
    else
      (if k.kind == Attention.Table.kr then
        [Attention.Seg.rm, Attention.Seg.rd].foldl (Attention.Counts.plane k) x else x)).nKFp = _
  rw [if_neg hk, kr_keeps]

/-! ## 4 All calls -/

/-- The units of a list of calls, added to the nKFp that the pass starts from, are the nKFp after the planner's pass. -/
theorem units_fold_is (S : Attention.Shape) :
    ∀ (l : List Attention.ACall) (k : ℕ) (x : Attention.Counts),
      ((l.zipIdx k).flatMap fun y =>
        if y.1.kind == Attention.Table.kfd then
          ([Attention.Seg.fm, Attention.Seg.fd].filter fun s => y.1.holds s).map
            fun s => (y.2, y.1, s)
        else []).length + x.nKFp = (l.foldl (Attention.Counts.call S) x).nKFp
  | [], _, x => by simp
  | c :: l, k, x => by
    rw [List.zipIdx_cons, List.flatMap_cons, List.length_append, List.foldl_cons]
    have ih := units_fold_is S l (k + 1) (Attention.Counts.call S x c)
    by_cases hk : (c.kind == Attention.Table.kfd) = true
    · have hc := call_kfd S x c hk
      simp only [hk, if_true, List.length_map]
      omega
    · have hc := call_other S x c hk
      simp only [hk, if_false, List.length_nil, Bool.false_eq_true]
      omega

/-- **The units of the scores that `unitsB` counts are the planner's nKFp.** -/
theorem units_is (S : Attention.Shape) : unitsB S = (Attention.Counts.of S).nKFp := by
  unfold unitsB Attention.Counts.of Attention.unitsOf
  rw [← Array.foldl_toList]
  have h := units_fold_is S S.calls.toList 0 {}
  simpa using h

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.plane_keeps
#print axioms ProofFile.Honest.K9.planes_keep
#print axioms ProofFile.Honest.K9.kr_keeps
#print axioms ProofFile.Honest.K9.scores_held
#print axioms ProofFile.Honest.K9.scores_not_held
#print axioms ProofFile.Honest.K9.scores_count
#print axioms ProofFile.Honest.K9.call_kfd
#print axioms ProofFile.Honest.K9.call_other
#print axioms ProofFile.Honest.K9.units_fold_is
#print axioms ProofFile.Honest.K9.units_is
