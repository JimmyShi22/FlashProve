-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/GroupMembers.lean: the kind "the code switch" (K2): THE MEMBERS
OF THE ROWS THAT AN HONEST PROVER's CLOSING MAKES OF A SEGMENT (`segmentGroupRows`,
Honest/K2/Closing.lean) ARE A PUBLIC TERM OF THE SEGMENT. Two definitions with code; two statements
with their proofs.

  `segFlags` a segment's members' flags "kept", in the order of sending: `segmentGroupRows`' own term, by
                    name; ps: a fold stands in front
  `membersOfSeg` the members: shapes and flags, off `SegmentPub` and ps alone: `segmentGroupRows`' own
                    last line, with its two lists of messages taken at zero data (`inFirstOf`,
                    `laterOf`, Honest/K2/Law/SegmentAlike.lean): of these lists the shapes alone are
                    read
  `rowsCore_members` where `rowsCore` (SegmentAlike.lean: `segmentGroupRows`' text with the two lists as
                    letters) returns R, R.members is that line at these lists: said with `Alike` of
                    a run and itself, as `rowsCore_count` (Law/GroupCount.lean) is, and proved as
                    that is
  `segmentRows_members` `segmentGroupRows table S prev prevKept own k base withFresh = .ok R` ⊢
                    `R.members = membersOfSeg S prev.isSome`: whatever the table, the data, the
                    carried stretches and the fold in front

By: `segmentRows_eq`, `inFirst_same`, `later_same`, `map_fst_same`, `SameShapes.append`
(SegmentAlike.lean) · the `Alike` laws (Law/Alike.lean). NEAR, NOT CALLED: `segmentRows_alike`
(SegmentAlike.lean): two runs' members are the same: it says "the same", not which.

Limits. Where `segmentGroupRows` refuses nothing is said. Nothing on the rows' entries. `membersOfSeg` is
a second text of one line of `segmentGroupRows`: `segmentRows_members` holds the two together. Nothing on
any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.GroupCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (Left GroupMember zeroG)

/-- A segment's members' flags "kept", in the order of sending. ps: a fold stands in front. -/
def segFlags (S : SegmentPub) (ps : Bool) : List Bool :=
  (if ps then false :: S.sizes.target.kept.toList.map (·.keptAgain) else []) ++ S.ownKept

/-- **A segment's group's members, off what is public of the segment.** -/
def membersOfSeg (S : SegmentPub) (ps : Bool) : List GroupMember :=
  (((inFirstOf S none (fun _ _ _ => zeroG) ++ (laterOf S ps fun _ _ _ => zeroG).1).map (·.1)).zip
    (segFlags S ps)).map fun x => ⟨x.1, x.2⟩

theorem rowsCore_members (table : FreshTable) (S : SegmentPub) (ps : Bool)
    (prevKept : List OnBytes.OracleShape) (A : List Laid) (B : List Laid × Nat)
    (k : Nat → Except String Stretch) (base : Nat) (withFresh : Bool) :
    Alike (fun (R : GroupRows) (_ : GroupRows) =>
        R.members = (((A ++ B.1).map (·.1)).zip (segFlags S ps)).map fun x => ⟨x.1, x.2⟩)
      (rowsCore table S ps prevKept A B k base withFresh)
      (rowsCore table S ps prevKept A B k base withFresh) := by
  unfold rowsCore
  dsimp only
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.guard ?_
  refine Alike.bind (R := Any) (Alike.same (fun _ => trivial) _) fun _ _ _ => ?_
  refine Alike.ite ?_ ?_
  · refine Alike.bind (R := Any) (Alike.same (fun _ => trivial) _) fun _ _ _ => ?_
    refine Alike.bind (R := Any) (Alike.same (fun _ => trivial) _) fun _ _ _ => ?_
    exact rfl
  · refine Alike.bind (R := Any) (Alike.ok trivial) fun _ _ _ => ?_
    refine Alike.bind (R := Any) (Alike.same (fun _ => trivial) _) fun _ _ _ => ?_
    exact rfl

/-- **Where a group's rows are made, its members are the public ones.** -/
theorem segmentRows_members {table : FreshTable} {S : SegmentPub} {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E}
    {k : Nat → Except String Stretch} {base : Nat} {withFresh : Bool} {R : GroupRows}
    (h : segmentGroupRows table S prev prevKept own k base withFresh = .ok R) :
    R.members = membersOfSeg S prev.isSome := by
  have h₀ := rowsCore_members table S prev.isSome prevKept (inFirstOf S prev own)
    (laterOf S prev.isSome own) k base withFresh
  rw [← segmentRows_eq, h] at h₀
  have e : R.members = _ := h₀
  rw [e]
  unfold membersOfSeg
  rw [map_fst_same ((inFirst_same S prev none own fun _ _ _ => zeroG).append
    (later_same S prev.isSome own fun _ _ _ => zeroG))]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.segFlags
#print axioms ProofFile.Honest.K2.Law.membersOfSeg
#print axioms ProofFile.Honest.K2.Law.rowsCore_members
#print axioms ProofFile.Honest.K2.Law.segmentRows_members
