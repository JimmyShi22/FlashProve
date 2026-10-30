-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/K13/WFillAtHead.lean: kind K13, the members' batching: THE FILLING OF W's MAIN ROWS
(`wDataAt`, Johnson/Desc/ProofFile/Honest/K13/WData.lean) UNDER THE LIBRARY's HEAD h (`P5J.AtMgA`: a
hypothesis): ITS PUBLIC TESTS ACCEPT AT THE HEAD's PUBLIC DATA; THE NUMBER OF CHALLENGES THAT IT
COUNTS IS THE NUMBER OF ROUNDS IN FRONT OF NUMBER 356 OF THE FIRST CHAIN; W's ONE MAIN ROW IS OVER
THE EXTENSION FIELD, ITS MESSAGE IS SAMPLED, AND W's 2^kCol ENTRIES FILL THAT ROW WHOLE; NO PLACE OF
A SAMPLE's PAD LIES IN IT; EACH ENTRY IS LAID. Statements with their proofs, five of them closed
facts by Lean's kernel; no definition. PUBLIC DATA ALONE: codes, a shape, counts of rounds and rows,
addresses. THE FULL SIZE AND THE FORMAT's SECOND HASH FUNCTION (`OnBytes.secondHashFunction`) ALONE.

Main names: `wPublicW`, `wPublicW_bites`, `wShapeW`, `wRowW`, `rounds356W`: the closed facts, at the
library's written codes, shape and description. `k13_wRow_at_head`: **one main row; one mask row;
the message length of W's code is 2^kCol; kCol is 18.** `k13_wHeard_at_head`: **`wHeard Zp` is
48,290.** `k13_wHeard_is_rounds`: **that is `roundsTo cF.blocksInOrder 356`.** `k13_wPublic_at_head`: **the
public tests accept.** `k13_wShape_at_head`: **mainDeg is 3; the message has answers.**
`k13_noPad_at_head`: **the frame's list `padInMain` is empty at W's shape.**
`wData_clear_of_maskRow`, `k13_wClear_at_head`: the frame's test `RowData.clear` accepts.
`k13_wLays_at_head`: **for e below 2^kCol: `lays` accepts at the row and place of the layout's index
of e, and that place holds the number e.**

What serves what. `k13_wPublic_at_head` and `k13_wLays_at_head`: WPair.lean (Honest/K13/) joins the
filling with kind K1's job at W's place, general in the public data; whether `lays` accepts anywhere
it leaves open: under h it accepts at 2^kCol places, so `wPair_data` has W's entry on its right side
there, and `wPair_lays_in_shape` is not idle. `k13_wHeard_at_head`, `k13_wHeard_is_rounds`: the
count of challenges. Number 356 is the sub-protocol at W's place "M:4" (`m4_place`,
Honest/K13/ExchangeM4At.lean; the library's `m4_written`, Johnson/AtFull/Desc/Lots/K13LotRows.lean).
`k13_wShape_at_head`, `k13_wRow_at_head`, `k13_noPad_at_head`: toward the premises of K1's law on a
main row's entry (`main_data_e`, Honest/K1/DataLaw.lean): its premise "(r, j) is none of
`padInMain`'s places" holds at every (r, j) by `k13_noPad_at_head`. `k13_wClear_at_head`: one clause
of K1's seat's public test (`placeSeatOk`, Honest/K1/PlaceJob.lean).

How. Under h the first chain's parameters are the written ones (`m3_written`,
Honest/K13/GuardsAtM3.lean: the library's six equations `FirstWritten`); the batching's first round
is number 48,270 (the library's `P5J.from_written`, Johnson/HB/LLHARD/OptsWhereLaid.lean, with
`plans_written`, as that file's own `whereB_at_name` goes); the head's description is alike to the
written one (`planAlike_at_head`, Honest/K14/WrittenAtHead.lean), so the first 356 sub-protocols
have the same rounds (the library's `alike₂_rounds`). Then the closed facts. `k13_wLays_at_head`:
`wData_lays_index` and `wNo_index` (Honest/K13/WDataLaid.lean). `wData_clear_of_maskRow`: at
letters, by the texts.

Limits. CONDITIONAL ON h (it has a member: the library's `headMember_zFull`,
AtFullSide/Top/HeadMemberAtFull.lean). AT THE FULL SIZE `RowData.clear`'s FIRST CLAUSE RUNS OVER
NOTHING: W's shape has a mask row, so no place of the sample's pad lies in a main row; its two spot
checks are answered by the bounds that `lays` tests itself: `k13_wClear_at_head` says no more than
that. The public tests read the count of challenges in one clause alone (2 + kCol ≤ n):
`k13_wPublic_at_head` holds nothing of 48,290; `wPublicW_bites`, the negative test, turns the last
clause (two rows on the pile). FROM THESE STATEMENTS TO `main_data_e`'s OWN PREMISES THE ROAD IS NOT
TYPED: that law asks at `shapeAt P k`: between lies K1's `w_shape_zero`
(Honest/K1/Law/ShapeAtW.lean). That number 356 stands at W's place is not shown here. `lays`,
`clear` and the public tests read neither the filler nor the instance: these stand in the statements
as letters. THAT `RowData.readyAt` ACCEPTS AT A LIST HEARD IS NOT SAID: it reads the filler's pile.
That the filler yields the verifier's pile's weights and points: not claimed. What an entry holds:
not said here. `RowData.clear`, `padInMain` and `roundsTo` are the frame's texts: these statements
hold at the frame's texts as they lie beneath this file. `rounds356W` stands at the written
description WP, whose values were printed by Lean's evaluator. Five evaluations in Lean's kernel,
which no independent checker has replayed; over one of them the depth of recursion is raised. This
file's imports reach Johnson/Goal/.

What is not claimed. What a mask row is for. It is none of the library's goals. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K13.WDataLaid
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.HB.LLHARD.OptsWhereLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K13
open OnBytes OnBytes.Params
open ProofFile.Honest ProofFile.Honest.K13
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain alike₂_rounds)
open VerifiableInference.PlanWritten (proofSizedFull plans_written)
open P2Law.ProofPlan (WP)
open P5J (AtMgA TS)
open ProofFile.Honest.K14 (planAlike_at_head)

/-- At the written codes and shape, at 48,290 challenges heard and 13 rows on the pile, the
filling's public tests accept. -/
theorem wPublicW :
    wPublic proofSizedFull.codes proofSizedFull.batch.shape 48290 13 = true := by
  decide +kernel

/-- A negative test: with one row on the pile the tests reject (their last clause). -/
theorem wPublicW_bites :
    wPublic proofSizedFull.codes proofSizedFull.batch.shape 48290 1 = false := by
  decide +kernel

/-- At the written shape W's main rows are over the extension field, and W's message is sampled. -/
theorem wShapeW : proofSizedFull.batch.shape.w.mainDeg = 3 ∧
    proofSizedFull.batch.shape.w.answers ≠ 0 := by
  decide +kernel

/-- At the written codes and shape: W has one main row and one mask row; the message length of its
code is 2^kCol; kCol is 18: SO W's 2^kCol ENTRIES FILL THE ONE MAIN ROW WHOLE. -/
theorem wRowW : proofSizedFull.batch.shape.w.mainRows = 1 ∧
    proofSizedFull.batch.shape.w.maskRows = 1 ∧
    wEll proofSizedFull.codes proofSizedFull.batch.shape = 2 ^ proofSizedFull.batch.shape.kCol ∧
    proofSizedFull.batch.shape.kCol = 18 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- At the written description the first 356 sub-protocols of the first chain have 48,290 rounds. -/
theorem rounds356W : ((WP.first.blocksInOrder.take 356).flatMap (·.rounds)).length = 48290 := by
  decide +kernel

/-- Where W's shape has a mask row the frame's test `RowData.clear` accepts at the filling, at all
codes, counts, fillers and instances: ITS FIRST CLAUSE RUNS OVER NOTHING (`padInMain` is empty); its
two spot checks are answered by the bounds that `lays` tests itself. -/
theorem wData_clear_of_maskRow {Xi : Type} (codes : Codes) (Sh : LinShape) (n u : ℕ)
    (pile : PileOf Xi) (x : Xi) (hm : Sh.w.maskRows ≠ 0) :
    (wData codes Sh n u pile x).clear wAddr (wEll codes Sh) Sh.w = true := by
  have e : padInMain (wEll codes Sh) Sh.w = [] := by
    unfold padInMain
    rw [if_pos (by rw [Bool.or_eq_true]; exact Or.inl (bne_iff_ne.2 hm))]
  have l1 : (wData codes Sh n u pile x).lays wAddr Sh.w.mainRows 0 = false := by
    show (wAddr == wAddr && wPublic codes Sh n u && decide (Sh.w.mainRows < Sh.w.mainRows) &&
      decide (0 < wEll codes Sh) && decide (wNo codes Sh Sh.w.mainRows 0 < 2 ^ Sh.kCol)) = false
    rw [decide_eq_false (Nat.lt_irrefl _)]
    simp
  have l2 : ∀ r, (wData codes Sh n u pile x).lays wAddr r (wEll codes Sh) = false := by
    intro r
    show (wAddr == wAddr && wPublic codes Sh n u && decide (r < Sh.w.mainRows) &&
      decide (wEll codes Sh < wEll codes Sh) &&
      decide (wNo codes Sh r (wEll codes Sh) < 2 ^ Sh.kCol)) = false
    rw [decide_eq_false (Nat.lt_irrefl _)]
    simp
  unfold RowData.clear
  rw [e, l1]
  simp [l2]

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}

/-- **THE SAME UNDER THE HEAD**: one main row; one mask row; the message length of W's code is
2^kCol; kCol is 18. CONDITIONAL on h. -/
theorem k13_wRow_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    Zp.first.lin.w.mainRows = 1 ∧ Zp.first.lin.w.maskRows = 1 ∧
      wEll Zp.first.codes Zp.first.lin = 2 ^ Zp.first.lin.kCol ∧ Zp.first.lin.kCol = 18 := by
  rw [(m3_written h).1, (m3_written h).2.1]
  exact wRowW

/-- **HOW MANY CHALLENGES THE FILLING COUNTS, UNDER THE HEAD.** CONDITIONAL on h. -/
theorem k13_wHeard_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) : wHeard Zp = 48290 := by
  obtain ⟨Z', hZ', p1, _, _⟩ := plans_written h.scope (P5T.laid_of_at h.laid)
  obtain rfl : Z' = Zp := Except.ok.inj (hZ'.symm.trans h.laid.pub)
  unfold wHeard
  rw [P5J.from_written hZ' p1]
  show 48270 + 2 + _ = 48290
  rw [(k13_wRow_at_head h).2.2.2]

/-- **THAT IS THE NUMBER OF ROUNDS IN FRONT OF NUMBER 356.** CONDITIONAL on h. -/
theorem k13_wHeard_is_rounds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    wHeard Zp = roundsTo cF.blocksInOrder 356 := by
  have A := planAlike_at_head h
  have e : (((P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder.take 356).flatMap
      (·.rounds)).length = 48290 := by
    rw [← alike₂_rounds _ _ (List.forall₂_take 356 A.first)]
    exact rounds356W
  rw [k13_wHeard_at_head h]
  exact e.symm

/-- **THE FILLING's PUBLIC TESTS ACCEPT AT THE HEAD's PUBLIC DATA.** CONDITIONAL on h. -/
theorem k13_wPublic_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    wPublic Zp.first.codes Zp.first.lin (wHeard Zp) Zp.first.pendingRows = true := by
  rw [k13_wHeard_at_head h, (m3_written h).1, (m3_written h).2.1, (m3_written h).2.2.2.1]
  exact wPublicW

/-- **W's MAIN ROWS ARE OVER THE EXTENSION FIELD; ITS MESSAGE IS SAMPLED.** CONDITIONAL on h. -/
theorem k13_wShape_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) :
    Zp.first.lin.w.mainDeg = 3 ∧ Zp.first.lin.w.answers ≠ 0 := by
  rw [(m3_written h).2.1]
  exact wShapeW

/-- **UNDER THE HEAD NO PLACE OF A SAMPLE's PAD LIES IN A MAIN ROW OF W**: W's shape has a mask row,
so the frame's list `padInMain` is empty, at every length. CONDITIONAL on h. -/
theorem k13_noPad_at_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) (ell : ℕ) :
    padInMain ell Zp.first.lin.w = [] := by
  unfold padInMain
  rw [if_pos (by rw [(k13_wRow_at_head h).2.1]; rfl)]

/-- **The frame's test `RowData.clear` accepts at the filling, under the head**, at every filler,
ground and instance: one clause of kind K1's seat's public test (`placeSeatOk`,
Honest/K1/PlaceJob.lean). AT THE FULL SIZE ITS FIRST CLAUSE RUNS OVER NOTHING: `k13_noPad_at_head`.
CONDITIONAL on h. -/
theorem k13_wClear_at_head {Xi : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (pile : ProofFile.Pub → ProofFile.Ground → PileOf Xi) (G : ProofFile.Ground) (x : Xi) :
    (wDataAt pile Zp G x).clear wAddr (wEll Zp.first.codes Zp.first.lin) Zp.first.lin.w = true := by
  exact wData_clear_of_maskRow _ _ _ _ _ _ (by rw [(k13_wRow_at_head h).2.1]; decide)

/-- **UNDER THE HEAD EACH ENTRY OF W BELOW 2^kCol IS LAID, AT THE ROW AND PLACE OF THE LAYOUT's
INDEX**: `lays` accepts there, and the place holds that entry's number. CONDITIONAL on h; he: e is
below 2^kCol. -/
theorem k13_wLays_at_head {Xi : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh)
    (pile : ProofFile.Pub → ProofFile.Ground → PileOf Xi) (G : ProofFile.Ground) (x : Xi) {e : ℕ}
    (he : e < 2 ^ Zp.first.lin.kCol) :
    (wDataAt pile Zp G x).lays wAddr
        ((linLayW Zp.first.codes Zp.first.lin).index e %
          2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits)
        ((linLayW Zp.first.codes Zp.first.lin).index e /
          2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits) = true ∧
      wNo Zp.first.codes Zp.first.lin
        ((linLayW Zp.first.codes Zp.first.lin).index e %
          2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits)
        ((linLayW Zp.first.codes Zp.first.lin).index e /
          2 ^ (linLayW Zp.first.codes Zp.first.lin).rowBits) = e :=
  ⟨wData_lays_index _ _ _ _ _ _ (k13_wPublic_at_head h) he,
    wNo_index (by
      have q := k13_wPublic_at_head h
      unfold wPublic at q
      simp only [Bool.and_eq_true] at q
      exact q.1.1.1) he⟩

end AtFullSide.K13

#print axioms AtFullSide.K13.wPublicW
#print axioms AtFullSide.K13.wPublicW_bites
#print axioms AtFullSide.K13.wShapeW
#print axioms AtFullSide.K13.wRowW
#print axioms AtFullSide.K13.rounds356W
#print axioms AtFullSide.K13.wData_clear_of_maskRow
#print axioms AtFullSide.K13.k13_wRow_at_head
#print axioms AtFullSide.K13.k13_wHeard_at_head
#print axioms AtFullSide.K13.k13_wHeard_is_rounds
#print axioms AtFullSide.K13.k13_wPublic_at_head
#print axioms AtFullSide.K13.k13_wShape_at_head
#print axioms AtFullSide.K13.k13_noPad_at_head
#print axioms AtFullSide.K13.k13_wClear_at_head
#print axioms AtFullSide.K13.k13_wLays_at_head
