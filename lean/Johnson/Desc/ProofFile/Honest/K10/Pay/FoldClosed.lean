-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K10/Pay/FoldClosed.lean: closed facts at the written values of the full size, which the tests
in front of the fold of a segment's closing (K10) spend. Each is a statement on constants alone; the ones by `decide +kernel`
are evaluated by Lean's kernel. No state is named.

  `groups_k_pos`    every group of the written request's shape has at least one row variable
  `unkept_written`  each of the 25 written lists has a member that is not kept
  `codes_written`   both written codes are there; the mask code's logN is at most the main code's; its message length is at
                    least 17 = 2 * 8 + 1
  `mask_written`    at each of the 25 links the written list of message shapes has, at the number of the fresh mask, a
                    message with no main row, one mask row under the written mask code, and no answer
  `mask_below`      at each of the 25 links that number lies below the table's count of messages at the closing

Limits. Nothing here speaks of a run. The full size alone.
-/
import Johnson.Desc.First.Close.Law.MaskAtFull
import Johnson.Desc.First.Close.Law.ReqKept
import Johnson.Desc.First.Close.Law.LayoutOfShapes
import Johnson.LPFE1R.ShapeAtNoFull
import Johnson.Desc.ReqLit.Full
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (kbAt maskNo seatsPlanW)
open VerifiableInference.Desc.First (toldCut)
open VerifiableInference.Desc.First.K2Hands (MList)
open VerifiableInference.Desc.ReqLit (shapeFull shapeFull_groups)
open Johnson.G (linksFullLit codesFull2)

/-- Every group of the written request's shape has at least one row variable. -/
theorem groups_k_pos : ∀ G ∈ (OnBytes.reqGroups shapeFull).toList, 1 ≤ G.k := by
  intro G hG
  have h1 : (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain)) ∈
      (OnBytes.reqGroups shapeFull).toList.map (fun G =>
        (G.k, G.h, G.target.kept.toList.map fun x => (x.shape.mainRows, x.keptAgain))) :=
    List.mem_map.2 ⟨G, hG, rfl⟩
  rw [shapeFull_groups] at h1
  have h2 : ∀ y ∈ ((8, 0, []) ::
      ((List.replicate 12 [(7, 0, [(9, false), (3, true)]), (8, 0, [(3, false)])]).flatten ++
        [(1, 0, [])]) : List (Nat × Nat × List (Nat × Bool))), 1 ≤ y.1 := by
    decide
  exact h2 _ h1

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- Each of the 25 written lists has a member that is not kept. -/
theorem unkept_written : ((List.range 25).all fun l =>
    (VerifiableInference.Desc.First.Close.membersOf (linksFullLit.getD l [])).any fun i =>
      !kbAt shapeFull l (linksFullLit.getD l []) i) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The two written codes are there, and they fit each other and the largest fold. -/
theorem codes_written :
    shapeFull.code < codesFull2.base.size ∧ shapeFull.maskCode < codesFull2.mask.size ∧
      (codesFull2.mask.getD shapeFull.maskCode default).logN ≤
        (codesFull2.base.getD shapeFull.code default).logN ∧
      17 ≤ (codesFull2.mask.getD shapeFull.maskCode default).ell := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At each of the 25 links: the written message at the fresh mask's number has no main row, one mask row under the
written mask code, and no answer. -/
theorem mask_written : ((List.range 25).all fun l =>
    (MList[maskNo seatsPlanW P5T.psFull l]?).any fun o =>
      o.mainRows == 0 && o.maskRows == 1 && o.maskCode == shapeFull.maskCode && o.answers == 0) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- At each of the 25 links the fresh mask's number lies below the table's count of messages at the closing. -/
theorem mask_below : ((List.range 25).all fun l =>
    decide (maskNo seatsPlanW P5T.psFull l <
      (P5T.N0Full.withTold IM.placesW toldCut).msgsAt IM.placesW[14 * l + IM.nAt l + 5]?)) = true := by
  decide +kernel

/-- The fresh mask's message, link by link. -/
theorem mask_written_at {l : Nat} (hl : l < 25) : ∃ o, MList[maskNo seatsPlanW P5T.psFull l]? = some o ∧
    o.mainRows = 0 ∧ o.maskRows = 1 ∧ o.maskCode = shapeFull.maskCode ∧ o.answers = 0 := by
  have hw : (MList[maskNo seatsPlanW P5T.psFull l]?).any (fun o : OnBytes.OracleShape =>
      o.mainRows == 0 && o.maskRows == 1 && o.maskCode == shapeFull.maskCode && o.answers == 0) = true :=
    List.all_eq_true.1 mask_written l (List.mem_range.2 hl)
  cases e : MList[maskNo seatsPlanW P5T.psFull l]? with
  | none =>
    rw [e] at hw
    cases hw
  | some o =>
    rw [e] at hw
    have hw' : (o.mainRows == 0 && o.maskRows == 1 && o.maskCode == shapeFull.maskCode &&
        o.answers == 0) = true := hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hw'
    obtain ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩ := hw'
    exact ⟨o, rfl, a1, a2, a3, a4⟩

/-- The fresh mask's number lies below the table's count, link by link. -/
theorem mask_below_at {l : Nat} (hl : l < 25) : maskNo seatsPlanW P5T.psFull l <
    (P5T.N0Full.withTold IM.placesW toldCut).msgsAt IM.placesW[14 * l + IM.nAt l + 5]? :=
  of_decide_eq_true (List.all_eq_true.1 mask_below l (List.mem_range.2 hl))

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.groups_k_pos
#print axioms ProofFile.Honest.K10.unkept_written
#print axioms ProofFile.Honest.K10.codes_written
#print axioms ProofFile.Honest.K10.mask_written
#print axioms ProofFile.Honest.K10.mask_below
#print axioms ProofFile.Honest.K10.mask_written_at
#print axioms ProofFile.Honest.K10.mask_below_at
