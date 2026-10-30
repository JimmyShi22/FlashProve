-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/MadeFit.lean: the closing of a segment (K10): the public test `rowsFit`
(Honest/K10/Job.lean) on the rows that the lot's job makes, from what a statement's group holds.

  `rowsFit_of_parts`   the test says yes where the group holds a written list's members, the group is in order, the two
                       sides have one list of codes and one pair of numbers, both message lengths are powers of two, the
                       members' numbers rise, and the rows' members have the written shapes and marks in that order
  `out_members`        the members that the job hands on have the shapes and marks of the shared text's

Limits. Every fact is a premise here.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.MadeParts
import Johnson.Desc.First.Close.Law.LayoutOfShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes.Means (GroupOk)
open VerifiableInference.Desc.First.Close (ShapesAre)
open ProofFile.Honest.K2 (SegmentPub GroupRows)

/-- **The public test on the rows, from what the statement's group holds.** -/
theorem rowsFit_of_parts {T : OnBytes.Statement} {G : OnBytes.Group} {lo : List (OnBytes.OracleShape × Nat)}
    {kb : Fin lo.length → Bool} {no : Fin lo.length → Nat} {Rd : GroupData}
    (H : ShapesAre T G lo kb no) (hOk : GroupOk T G) (c0 : T.codes = Rd.codes) (c1 : G.code = Rd.code)
    (c2 : G.maskCode = Rd.maskCode) (p1 : OnBytes.powerOfTwo Rd.base.ell = true)
    (p2 : OnBytes.powerOfTwo Rd.zk.ell = true)
    (hr : rising ((VerifiableInference.Desc.First.Close.membersOf lo).map no) = true)
    (hm : Rd.members.map (fun m => (m.shape, m.kept)) =
      (VerifiableInference.Desc.First.Close.membersOf lo).map fun i => ((lo.get i).1, kb i)) :
    rowsFit T G Rd = true := by
  have hlen : Rd.members.length = (VerifiableInference.Desc.First.Close.membersOf lo).length := by
    have := congrArg List.length hm
    simpa using this
  unfold rowsFit
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨c0, c1⟩, c2⟩, p1⟩, p2⟩, ?_⟩, hOk.marks⟩, ?_⟩, ?_⟩
  · rw [H.members]
    exact hr
  · rw [H.size]
    exact hlen
  · rw [List.all_eq_true]
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
    have hj' : j < (G.members.toList.zipIdx).length ∧ j < Rd.members.length := by
      simpa using hj
    have hj1 : j < (VerifiableInference.Desc.First.Close.membersOf lo).length := hlen ▸ hj'.2
    have hjm : j < G.members.toList.length := hj'.1.trans_eq (by simp)
    have eM : G.members.toList[j] = no (VerifiableInference.Desc.First.Close.membersOf lo)[j] := by
      simp only [H.members, List.getElem_map]
    have eK : G.kept.getD j false = kb (VerifiableInference.Desc.First.Close.membersOf lo)[j] := by
      have e : G.kept[j]? = some (kb (VerifiableInference.Desc.First.Close.membersOf lo)[j]) := by
        rw [← Array.getElem?_toList, H.kept, List.getElem?_map, List.getElem?_eq_getElem hj1]
        rfl
      rw [Array.getD_eq_getD_getElem?, e]
      rfl
    have eR : (Rd.members[j].shape, Rd.members[j].kept) =
        ((lo.get (VerifiableInference.Desc.First.Close.membersOf lo)[j]).1,
          kb (VerifiableInference.Desc.First.Close.membersOf lo)[j]) := by
      have e := congrArg (fun L => L[j]?) hm
      simp only [List.getElem?_map, List.getElem?_eq_getElem hj'.2, List.getElem?_eq_getElem hj1,
        Option.map_some, Option.some.injEq] at e
      exact e
    obtain ⟨e1, e2⟩ := Prod.mk.inj eR
    have mi : (VerifiableInference.Desc.First.Close.membersOf lo)[j] ∈
        VerifiableInference.Desc.First.Close.membersOf lo := List.getElem_mem _
    obtain ⟨y, hy, ey⟩ := Option.map_eq_some_iff.1 (H.shape _ mi)
    have memG : no (VerifiableInference.Desc.First.Close.membersOf lo)[j] ∈ G.members.toList := by
      rw [H.members]
      exact List.mem_map_of_mem mi
    have g1 := hOk.mainCode _ memG y hy
    have g2 := hOk.maskCode _ memG y hy
    rw [ey] at g1 g2
    simp only [List.getElem_zip, List.getElem_zipIdx, Nat.zero_add, eM, eK, e1, e2, hy, Option.map_some,
      Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true]
    exact ⟨⟨⟨by rw [ey], trivial⟩, g1⟩, g2⟩

/-- The members that the job hands on have the shapes and marks of the shared text's. -/
theorem out_members (S : SegmentPub) {R : GroupRows} (hc : R.rows.length = R.members.length) :
    (rowsOut S R).members.map (fun m => (m.shape, m.kept)) = R.members.map fun m => (m.shape, m.kept) := by
  show ((R.members.zip R.rows).map fun x => memberOf x.1 x.2).map (fun m => (m.shape, m.kept)) = _
  rw [List.map_map]
  have e : (((fun m : MemberRows => (m.shape, m.kept)) ∘ fun x => memberOf x.1 x.2) :
      VerifiableInference.Desc.K2.Honest.GroupMember × Johnson.Prover.Send.Rows → _) =
      (fun m => (m.shape, m.kept)) ∘ Prod.fst := rfl
  rw [e, ← List.map_map, List.map_fst_zip (by omega)]

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.rowsFit_of_parts
#print axioms ProofFile.Honest.K10.out_members
