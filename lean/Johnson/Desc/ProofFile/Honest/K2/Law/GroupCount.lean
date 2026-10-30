-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/GroupCount.lean: the kind "the code switch" (K2): WHERE THE
ROWS OF A GROUP ARE MADE (`segmentGroupRows`, `groupRowsOf`, Honest/K2/Closing.lean) THERE ARE AS MANY
ROWS AS MEMBERS. Statements with their proofs. A law on texts: it says nothing on what a run shows.

"At each return" is said as `Alike` (Honest/K2/Law/Alike.lean) of a run with itself, at a relation
that reads its first side alone: so that file's tools walk the text.

  `Alike.guardNot`  a tool: a refusal under a condition; behind it the condition's "no" is in hand
  `mapM_count`      a tool: a list walked by a function that may refuse: as many results as members
  `rowsCore_count`, `segmentRows_count`, `groupRowsOf_count`   the count, text by text
  `groupRowsOf_rows`   the same, plainly: if `groupRowsOf` returns R, R has as many rows as members

Limits. Nothing on what the rows hold. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentAlike

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left)

theorem Alike.guardNot {α β : Type} {R : α → β → Prop} {c : Prop} [Decidable c] {e : String}
    {f : PUnit → Except String α} {g : PUnit → Except String β}
    (h : ¬c → Alike R (f PUnit.unit) (g PUnit.unit)) :
    Alike R (if c then (throw e : Except String PUnit) >>= f else pure PUnit.unit >>= f)
      (if c then (throw e : Except String PUnit) >>= g else pure PUnit.unit >>= g) := by
  by_cases hc : c
  · rw [if_pos hc, if_pos hc]
    exact Alike.error e
  · rw [if_neg hc, if_neg hc]
    exact h hc

theorem mapM_count {α γ : Type} (f : α → Except String γ) : ∀ l : List α,
    Alike (fun (r : List γ) (_ : List γ) => r.length = l.length) (l.mapM f) (l.mapM f)
  | [] => by
    rw [List.mapM_nil]
    exact rfl
  | a :: l => by
    rw [List.mapM_cons]
    refine Alike.bind (R := Any) (Alike.same (fun _ => trivial) (f a)) fun b _ _ => ?_
    refine Alike.bind (mapM_count f l) fun r _ hr => ?_
    show (b :: r).length = (a :: l).length
    rw [List.length_cons, List.length_cons, hr]

theorem rowsCore_count (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) (A : List Laid) (B : List Laid × Nat)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    Alike (fun (R : GroupRows) (_ : GroupRows) => R.rows.length = R.members.length)
      (rowsCore table S ps prevKept A B k base withFresh)
      (rowsCore table S ps prevKept A B k base withFresh) := by
  unfold rowsCore
  dsimp only
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guardNot fun hf => ?_
  refine Alike.bind (mapM_count _ _) fun r₀ _ h₀ => ?_
  refine Alike.ite ?_ ?_
  · refine Alike.bind (R := Any) (Alike.same (fun _ => trivial) _) fun _ _ _ => ?_
    refine Alike.bind (mapM_count _ _) fun r₁ _ h₁ => ?_
    show (r₀ ++ r₁).length = (List.map _ (List.zip _ _)).length
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hf
    simp [h₀, h₁, hf]
  · refine Alike.bind (R := Any) (Alike.ok trivial) fun _ _ _ => ?_
    refine Alike.bind (mapM_count _ _) fun r₁ _ h₁ => ?_
    show (r₀ ++ r₁).length = (List.map _ (List.zip _ _)).length
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hf
    simp [h₀, h₁, hf]

theorem segmentRows_count (table : FreshTable) (S : SegmentPub) (prev : Option Left)
    (prevKept : List OnBytes.OracleShape) (own : Nat → Nat → Nat → Cb.Gl.E)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    Alike (fun (R : GroupRows) (_ : GroupRows) => R.rows.length = R.members.length)
      (segmentGroupRows table S prev prevKept own k base withFresh)
      (segmentGroupRows table S prev prevKept own k base withFresh) := by
  rw [segmentRows_eq]
  exact rowsCore_count table S _ prevKept _ _ k base withFresh

theorem groupRowsOf_count (table : FreshTable) (segs : List SegmentPub)
    (own : Nat → Nat → Nat → Nat → Cb.Gl.E) (heard : List Fmt.Drawn)
    (k : Nat → Except String Stretch) :
    Alike (fun (R : GroupRows) (_ : GroupRows) => R.rows.length = R.members.length)
      (groupRowsOf table segs own heard k) (groupRowsOf table segs own heard k) := by
  unfold groupRowsOf
  cases segs.getLast? with
  | none => exact Alike.error _
  | some S =>
    dsimp only
    exact Alike.bind (R := fun a b => a = b) (Alike.same (fun _ => rfl) _) fun x _ hxy =>
      hxy ▸ segmentRows_count table S _ _ _ k _ false

/-- **Where the rows of a group are made there are as many rows as members.** -/
theorem groupRowsOf_rows {table : FreshTable} {segs : List SegmentPub}
    {own : Nat → Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {k : Nat → Except String Stretch} {R : GroupRows}
    (h : groupRowsOf table segs own heard k = .ok R) : R.rows.length = R.members.length := by
  have h₀ := groupRowsOf_count table segs own heard k
  rw [h] at h₀
  exact h₀

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.Alike.guardNot
#print axioms ProofFile.Honest.K2.Law.mapM_count
#print axioms ProofFile.Honest.K2.Law.rowsCore_count
#print axioms ProofFile.Honest.K2.Law.segmentRows_count
#print axioms ProofFile.Honest.K2.Law.groupRowsOf_count
#print axioms ProofFile.Honest.K2.Law.groupRowsOf_rows
