-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/RowsOfLater.lean: the kind "the code switch" (K2): WHAT
`segmentGroupRows` (Honest/K2/Closing.lean) RETURNS AT THE MESSAGES OF A SEGMENT's LATER SENDINGS, ENTRY
BY ENTRY: the sister of Honest/K2/Law/RowsOfSegment.lean, which speaks of the first sending: where
it returns, the rows number (first sending's messages but the mask) + q of its list are what
`messageRows` returns at the stretch number base + these + (1 where the mask's stretch is handed
over) + q. Statements with their proofs; no definition.

  `laterFold_list`, `laterOf_list`   the later sendings' list in closed form: the messages of the
                 sendings behind the first, in a row, number q with the own data number o + q
  `rowsCore_later`    the end at `rowsCore` (Honest/K2/Law/SegmentAlike.lean)
  `segmentRows_later`   THE END

o := the first sending's messages but the mask, less the carrying message and the kept copies where
a segment lies in front: the number among the segment's OWN messages at which the later sendings
begin.

By: `OkGives` and its steps, `laidRow_at` (RowsOfSegment.lean); `mapM_count`
(Honest/K2/Law/GroupCount.lean); `segmentRows_eq` (SegmentAlike.lean).

Limits. On a text with refusals: k is a letter: no sentence on what a stretch holds. Whose the later
sendings are is not said. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.RowsOfSegment
import Johnson.Desc.ProofFile.Honest.K2.Law.GroupCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left)
open Reads

/-- The fold of `laterStep`, in closed form. -/
theorem laterFold_list (own : Nat → Nat → Nat → Cb.Gl.E) :
    ∀ (l : List (Array OnBytes.OracleNotice)) (acc : List Laid) (o : Nat),
      (l.foldl (laterStep own) (acc, o)).1 =
        acc ++ (l.flatMap (·.toList)).zipIdx.map fun x => (x.1.shape, own (o + x.2))
  | [], acc, o => by simp
  | a :: l, acc, o => by
    rw [List.foldl_cons]
    show (l.foldl (laterStep own)
      (acc ++ a.toList.zipIdx.map fun x => (x.1.shape, own (o + x.2)), o + a.size)).1 = _
    rw [laterFold_list own l, List.flatMap_cons, List.zipIdx_append, List.map_append,
      List.append_assoc]
    congr 2
    conv_rhs => rw [List.zipIdx_eq_map_add, List.map_map]
    refine List.map_congr_left fun x _ => ?_
    obtain ⟨y, j⟩ := x
    show (y.shape, own (o + a.size + j)) = (y.shape, own (o + (0 + a.toList.length + j)))
    rw [Array.length_toList, Nat.zero_add, Nat.add_assoc]

/-- The later sendings' list. -/
theorem laterOf_list (S : SegmentPub) (ps : Bool) (own : Nat → Nat → Nat → Cb.Gl.E) :
    (laterOf S ps own).1 =
      ((S.sent.drop 1).flatMap (·.toList)).zipIdx.map fun x =>
        (x.1.shape, own ((S.sent.headD #[]).size - 1 -
          (if ps then 1 + S.sizes.kept.length else 0) + x.2)) := by
  unfold laterOf
  rw [laterFold_list, List.nil_append]

/-- The end at `rowsCore`. -/
theorem rowsCore_later (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) (A : List Laid) (B : List Laid × Nat)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    OkGives (fun R : GroupRows =>
      ∀ q s d, B.1[q]? = some (s, d) → ∃ r, R.rows[A.length + q]? = some r ∧
        (k (base + ((S.sent.headD #[]).size - 1) + (if withFresh then 1 else 0) + q)).bind
          (messageRows table S.sizes.codes s none d) = .ok r)
      (rowsCore table S ps prevKept A B k base withFresh) := by
  unfold rowsCore
  dsimp only
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.guard ?_
  refine OkGives.bind fun r₀ h₀ => ?_
  have hlen : r₀.length = A.length := by
    have c := mapM_count (fun x : Laid × Nat =>
      (k (base + x.2)).bind (messageRows table S.sizes.codes x.1.1 none x.1.2)) A.zipIdx
    rw [h₀] at c
    exact c.trans List.length_zipIdx
  refine OkGives.ite (fun _ => ?_) fun _ => ?_
  all_goals
    refine OkGives.bind fun fr _ => ?_
    refine OkGives.bind fun r₁ h₁ => ?_
    intro R hR
    obtain rfl := Except.ok.inj hR
    intro q s d hx
    obtain ⟨r, hr, hg⟩ := laidRow_at table S.sizes.codes k
      (base + ((S.sent.headD #[]).size - 1) + (if withFresh then 1 else 0)) h₁ hx
    refine ⟨r, ?_, hg⟩
    show (r₀ ++ r₁)[A.length + q]? = some r
    rw [← hlen, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hr]

/-- **THE END.** x: the message number q of the sendings behind the first, in a row. -/
theorem segmentRows_later {table : FreshTable} {S : SegmentPub} {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E}
    {k : Nat → Except String Stretch} {base : Nat} {withFresh : Bool} {R : GroupRows}
    (h : segmentGroupRows table S prev prevKept own k base withFresh = .ok R) {q : Nat}
    {x : OnBytes.OracleNotice} (hx : ((S.sent.drop 1).flatMap (·.toList))[q]? = some x) :
    ∃ r, R.rows[(S.sent.headD #[]).size - 1 + q]? = some r ∧
      (k (base + ((S.sent.headD #[]).size - 1) + (if withFresh then 1 else 0) + q)).bind
        (messageRows table S.sizes.codes x.shape none
          (own ((S.sent.headD #[]).size - 1 -
            (if prev.isSome then 1 + S.sizes.kept.length else 0) + q))) = .ok r := by
  rw [segmentRows_eq] at h
  have hB : (laterOf S prev.isSome own).1[q]? = some (x.shape,
      own ((S.sent.headD #[]).size - 1 -
        (if prev.isSome then 1 + S.sizes.kept.length else 0) + q)) := by
    rw [laterOf_list, List.getElem?_map, List.getElem?_zipIdx, hx]
    simp
  have g := rowsCore_later table S prev.isSome prevKept (inFirstOf S prev own)
    (laterOf S prev.isSome own) k base withFresh R h q _ _ hB
  have hA : (inFirstOf S prev own).length = (S.sent.headD #[]).size - 1 := by
    unfold inFirstOf
    rw [List.length_map, List.length_zipIdx, List.length_take, Array.length_toList]
    omega
  rw [hA] at g
  exact g

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.laterFold_list
#print axioms ProofFile.Honest.K2.Law.laterOf_list
#print axioms ProofFile.Honest.K2.Law.rowsCore_later
#print axioms ProofFile.Honest.K2.Law.segmentRows_later
