-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormDoorLaws.lean: THE FORM's HALF: **THE DOOR INTO A PROXIMITY TEST**: the
front's part of guardedProximityTestParts (Johnson/Desc/K12/JoinGuarded.lean) returns ok and turns nothing; and the front,
the batching, the frame's question and the first fold say yes in a row, with the records between
written out.

Main names.
  rowL_of_clauses   the converse of the library's rowL_clauses
    (Johnson/Desc/First/Batch/Law/DoorTests.lean): the sentences give the test's yes.
  front5_yes        the front's part says yes, and turns nothing.
  door_yes          THE STATEMENT: from TestFront, BatOwes, FrontOwes, the plan's two tests (batCut,
    foldCut) and the library's test on the view's format (roundsFit).

Limits. The three records are premises HERE. Behind the link's six front blocks they follow from
these blocks' yes: door_premises (DoorPay.lean), under five premises; at the full size, with the
plan's share paid: door_full (DoorFull.lean), which link_yes' proof spends at the honest link
prover's rounds (BodyInv0Full.lean). Of a record where verify() stands nothing is shown. They are
also met together at one made-up small example. It ends behind the first fold:
the switch, the later stages and the base case are not here, so nothing is said of the block's own
decision. Nothing on soundness or completeness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormDoor
import Johnson.Prover.Link.FormBatLaws
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- **The sentences give the test's yes.** -/
theorem rowL_of_clauses (S : Statement) (g : Nat) (G : Group) (row : Row)
    (hG : S.groups[g]? = some G) (h : K9L.RowClauses S G row) :
    ∀ c ∈ Ground.rowL S g row, c.2 = true := by
  have hall : Ground.ok (Ground.rowL S g row) = true := by
    simp only [Ground.ok, Ground.rowL, List.all_cons, List.all_nil, Bool.and_eq_true,
      Bool.and_true, ← Own.tensorInOrder_agrees, ← Own.placeFits_agrees,
      ← Own.coeffsInside_agrees, ← Own.formFits_agrees, ← Own.allZero_agrees]
    simp only [Ground.has, hG, Option.map_some, Option.getD_some, Option.isSome_some]
    simp only [Array.all_eq_true_iff_forall_mem, List.all_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    exact ⟨trivial, by simp [h.noTest], by simpa using h.noSample, h.terms, h.units,
      fun w hw => ⟨⟨⟨(h.runs w hw).1, (h.runs w hw).2.1⟩, (h.runs w hw).2.2.1⟩,
        (h.runs w hw).2.2.2⟩, h.forms, h.pads⟩
  unfold Ground.ok at hall
  exact fun c hc => List.all_eq_true.1 hall c hc

section Door
variable {p : P12} {cur nxt : Fmt.M1.Stage} {t : T12} {G : Group} {i n : Nat × Nat} {id : Nat}

/-- **The front's part says yes, and turns nothing.** -/
theorem front5_yes (hp : t.pass = .nothing) (hG : t.st.groups[t.g]? = some G)
    (F : FrontOwes p t G) : (guardedProximityTestParts.front p).decide t [] [] = .ok t := by
  have hE : frontE t.st t.book t.g t.mask = .ok () :=
    (Seat.frontE_ok _ _ _ _).2 ⟨F.front, G, hG, fun row hr =>
      rowL_of_clauses t.st t.g G row hG (F.rows row hr)⟩
  have hJ : (frontJ p).decide t [] [] = .ok t := by
    simp only [frontJ, hp]
    rw [hE]
    rfl
  show (do
    VerifiableInference.Desc.need
      "(f): the plan's count of roots in front of the test is not the record's"
      (p.nums.free == t.roots)
    let t' ← (frontJ p).decide t [] []
    VerifiableInference.Desc.need
      "(p): the record's codes or the place's rounds fail a public clause of the chain"
      (H2K.Pub.pubOk p t'.st.codes)
    pure t' : Except String T12) = _
  rw [F.roots, hJ]
  show (do
    VerifiableInference.Desc.need
      "(f): the plan's count of roots in front of the test is not the record's"
      (t.roots == t.roots)
    VerifiableInference.Desc.need
      "(p): the record's codes or the place's rounds fail a public clause of the chain"
      (H2K.Pub.pubOk p t.st.codes)
    pure t : Except String T12) = _
  rw [F.pub, beq_self_eq_true]
  rfl

/-- **THE DOOR**: the front, the batching, the frame's question and the first fold say yes in a row,
and the records between are written out. -/
theorem door_yes (H : TestFront p cur nxt t G i n id) (cutB cutF : List Fmt.DeclaredRound)
    (B : BatOwes p cutB t G) (F : FrontOwes p t G) (hB : batCut cutB = true)
    (hF : foldCut cur.k cutF = true) (rsB rsF : List Fmt.RoundView) (fB : roundsFit cutB rsB = true)
    (fF : roundsFit cutF rsF = true) :
    ∃ row,
      (guardedProximityTestParts.front p).decide t [] [] = .ok t ∧
      (guardedProximityTestParts.bat p cutB).decide t (rsB.map noDigest) [] = .ok (batT t G row) ∧
      (guardedProximityTestParts.group (batT t G row)).any (firstFits cur) = true ∧
      (guardedProximityTestParts.fold p 0 cur cutF).decide (batT t G row) (rsF.map noDigest) [] =
        .ok (foldT (batT t G row) row (layoutOf t.st G) ⟨i.1, i.2, cur.k, cur.h⟩ n id
          (rsF.map noDigest)) := by
  obtain ⟨row, hr, hb⟩ := bat5_yes H cutB B hB rsB fB
  exact ⟨row, front5_yes B.pass H.group F, hb, group_batT H row,
    fold5_yes (foldFront_first H _ row hr) hF rsF fF⟩

end Door

end Johnson.Prover.Link

#print axioms Johnson.Prover.Link.rowL_of_clauses
#print axioms Johnson.Prover.Link.front5_yes
#print axioms Johnson.Prover.Link.door_yes
