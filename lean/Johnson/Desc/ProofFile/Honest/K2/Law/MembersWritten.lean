-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MembersWritten.lean: the kind "the code switch" (K2): AT THE 25
WRITTEN SEGMENTS THE PUBLIC MEMBERS OF A SEGMENT (`membersOfSeg`, Law/GroupMembers.lean) ARE THE
LIBRARY's WRITTEN LIST's MEMBERS WITH ITS WRITTEN FLAGS. Two definitions with code; one test that
accepts and three that reject, each a theorem by the kernel's evaluation (`decide +kernel`).

  `segMembersAt` the members of the written segment number l (`segsW`, Law/PlacesWritten.lean), as
                    pairs (shape, flag "kept"), with "a fold stands in front" := l ≠ 0; the empty
                    list where there is no such segment
  `listMembersAt` link l's written list's members (`membersOf`, `linksFullLit`, `kbAt shapeFull`:
                    the library's), as such pairs
  `segMembers_written` the two lists are equal at every l < 25
  `segMembers_rejects` at l = 25, where we have no segment and the library's 26th written list has
                    one member: not equal
  `segMembers_rejects_flag` at the real segment 1 with every flag turned: not equal
  `segMembers_rejects_shape` at the real segment 1 with one main row more in every shape: not equal

Why pairs: `GroupMember` (Johnson/Desc/K2/Honest/FoldEnd.lean) has no decidable equality;
Law/MembersJoin.lean goes back from pairs to members.

Limits. CLOSED FACTS AT THE FULL SIZE's WRITTEN LISTS: they say nothing of any other shape. The
three rejections show that the test can fail in three ways, at one segment for two of them; not that
it catches every fault. That the written segments are a description's is said elsewhere
(`segments_at_head`, Law/PlacesWritten.lean). Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.GroupMembers
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten
import Johnson.Desc.First.Close.Law.ShapesReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc.K2.Honest (GroupMember)
open VerifiableInference.Desc.First.Close (kbAt)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (linksFullLit)

/-- A written segment's members, as pairs (shape, flag "kept"); nothing where there is no
segment. -/
def segMembersAt (l : Nat) : List (OnBytes.OracleShape × Bool) :=
  match segsW[l]? with
  | some Sg => (membersOfSeg Sg (l != 0)).map fun m => (m.shape, m.kept)
  | none => []

/-- The written list's members of link l, as such pairs. -/
def listMembersAt (l : Nat) : List (OnBytes.OracleShape × Bool) :=
  (VerifiableInference.Desc.First.Close.membersOf (linksFullLit.getD l [])).map fun i =>
    (((linksFullLit.getD l []).get i).1, kbAt shapeFull l (linksFullLit.getD l []) i)

/-- **The test accepts at all 25 written segments.** -/
theorem segMembers_written :
    ((List.range 25).all fun l => segMembersAt l == listMembersAt l) = true := by
  decide +kernel

/-- **Three negative tests**: it rejects where we have no segment; at a real segment with every flag
turned; and at a real segment with one main row more in every shape. -/
theorem segMembers_rejects : (segMembersAt 25 == listMembersAt 25) = false := by decide +kernel

theorem segMembers_rejects_flag :
    ((segMembersAt 1).map (fun x => (x.1, !x.2)) == listMembersAt 1) = false := by decide +kernel

theorem segMembers_rejects_shape :
    ((segMembersAt 1).map (fun x => ({ x.1 with mainRows := x.1.mainRows + 1 }, x.2)) ==
      listMembersAt 1) = false := by decide +kernel

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.segMembersAt
#print axioms ProofFile.Honest.K2.Law.listMembersAt
#print axioms ProofFile.Honest.K2.Law.segMembers_written
#print axioms ProofFile.Honest.K2.Law.segMembers_rejects
#print axioms ProofFile.Honest.K2.Law.segMembers_rejects_flag
#print axioms ProofFile.Honest.K2.Law.segMembers_rejects_shape
