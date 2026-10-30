--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Part4/Widths.lean: THE PROXIMITY TEST OF THE LAST CHAIN (the kind
K12, at the place W of the proof file): THE PROOFS OF THE STATEMENTS OF
Honest/K12/Part4/WidthsStatements.lean: the three trees that the test takes over from the two
earlier chains have the declared widths 3, 12 and 36.

WHAT IT IS NOT. What that file's head says: widths are public numbers, nothing on what a table
holds; the first chain's two stand under premises on the thread's table and on the shared sending's
record at the members 2 and 356, which are paid elsewhere; the shared chain's one stands at the
term tableShared. Closed facts are evaluated in Lean's kernel (toldWidthsOfTheTakenTrees,
omegaWidthWritten, each with a control); they are replayed by no independent checker. It stands over
fifteen files of another house that lie in no sealed tree (Honest/K12/AtFile/TableShared.lean,
BookLines.lean and what lies beneath them). Nothing on completeness, on soundness or on what a proof
hides.

WHAT IT IS. Calls and ties; no new mathematics.
  A SENDING's TREE. The thread's table is the text treeTbl (the premise OwnTrees); the book covers
  the part (lentCut_isSome, Honest/K1/ScriptAtLaw.lean), so the text is scriptTable (treeTbl_some);
  the tables' two numbers are those that the sending's own block states (treeTables_oracles,
  Honest/K1/TableShape.lean).
  AT THE PROOF FILE. Under the head what the first chain's members tell is the written list
  (toldOf_of_cut, tests_at_head) and so is the count of trees in front (treesTo_at_head,
  Honest/K2/Law/PlacesWritten.lean); the numbers are read off that list by the kernel.
  THE SHARED CHAIN. words_low and covers_head (the other house's), and one closed line on the width.
-/
import Johnson.Desc.ProofFile.Honest.K12.Part4.WidthsStatements
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K1.TableShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Part4
open OnBytes (TableKey)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull toldOf_of_cut)
open VerifiableInference.Desc.K2.Honest.Returns (tests_at_head)
open VerifiableInference.Desc.K1 (realSized)
open P5J (AtMgA CellsM TS)
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open ProofFile.Honest.FirstThread (Script WtF lettersHead OwnTrees)
open ProofFile.Honest.K1 (SendJob PlaceIn treeTbl dueR treeTbl_some scriptTable lentCut lentCut_isSome
  bookCovers treeTables treeTables_oracles rowsLaid wordlessTable)
open ProofFile.Honest.K2.Law (treesTo_at_head)
open ProofFile.Honest.K12 (TestJob)
open ProofFile.Honest.K12.Light (written_at_head qAt_written)
open ProofFile.Honest.K12.AtFile (tableShared tableWidth words_low covers_head)
open ProofFile.Honest.K14 (treesU)

/-! ## 1 Closed facts -/

set_option maxRecDepth 1000000 in
theorem toldWidthsOfTheTakenTrees : ToldWidthsOfTheTakenTrees := by
  unfold ToldWidthsOfTheTakenTrees
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: THE LINES CAN SAY NO: behind member 356 the count is 83, not 82; and member 356 tells
no second tree. By evaluation in Lean's kernel. -/
theorem toldWidths_control :
    treesTold toldFull 357 = 83 ∧ ((toldFull[356]?).bind (·[1]?)).isNone = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A CLOSED FACT at the typed sizes: the shared chain's own tree 1 has 36 words, and the first of
its two sendings makes at most three trees. By evaluation in Lean's kernel. -/
theorem omegaWidthWritten : (realSized.all fun q =>
    tableWidth (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape) 1 == 36 &&
      decide (treesU (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape).P ≤ 3)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at 37 the line says no. -/
theorem omegaWidthWritten_control : (realSized.all fun q =>
    tableWidth (ProofFile.Honest.K12.Light.planOf q.2 q.1.shape) 1 == 37) = false := by
  decide +kernel

/-! ## 2 A sending's own tree -/

/-- What a sending's block tells, one list behind the other, is its first round's list. -/
theorem told_is_first_round (P : VerifiableInference.Desc.K1.Par) :
    (VerifiableInference.Desc.K1.oracles P).flatten =
      (VerifiableInference.Desc.K1.oracles P).headD [] := by
  unfold VerifiableInference.Desc.K1.oracles
  simp

/-- It tells as many oracle messages as the plan has trees. -/
theorem told_length (P : VerifiableInference.Desc.K1.Par) :
    (VerifiableInference.Desc.K1.oracles P).flatten.length = P.trees.length := by
  unfold VerifiableInference.Desc.K1.oracles
  simp

theorem ownTreeOfASendingHasItsToldWidth : OwnTreeOfASendingHasItsToldWidth := by
  intro Bk S Cl V Wl Xt Pb W X T member trees wit job own₀ off block hOwn _ hor hcoins j hj told
    htold k v hd
  rw [hOwn.table j hj k v hd]
  have hcov : bookCovers Bk 0 ⟨job.P.place, 0⟩ (dueR job.P job.ride) = true := by
    unfold bookCovers
    rw [hcoins]
    exact decide_eq_true ⟨Nat.le_refl _, Nat.le_refl _⟩
  have hs : (lentCut k 0 ⟨job.P.place, 0⟩ (dueR job.P job.ride)).isSome = true := by
    rw [lentCut_isSome k 0 (by omega)]
    exact hcov
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hs
  rw [treeTbl_some 0 wit job own₀ j k c hc v hd]
  show (((treeTables job.P (rowsLaid job own₀ c (wit v) hd))[j]?).getD wordlessTable).words =
    told.words
  rw [hor, told_is_first_round] at htold
  have q := congrArg (·[j]?) (treeTables_oracles job.P (rowsLaid job own₀ c (wit v) hd))
  simp only [List.getElem?_map, htold, Option.map_some] at q
  cases hT : (treeTables job.P (rowsLaid job own₀ c (wit v) hd))[j]? with
  | none =>
    rw [hT] at q
    cases q
  | some table =>
    rw [hT] at q
    exact congrArg Prod.snd (Option.some.inj q)

/-! ## 3 At the proof file -/

theorem firstChainsTakenTreesHaveTheirWidths : FirstChainsTakenTreesHaveTheirWidths := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    wit opening lastSending own₀ offOpening offLast blockOpening blockLast hb2 ho2 hc2 hT2 hb356
    ho356 hc356 hT356
  obtain ⟨t2, t356, w1, w82⟩ := toldWidthsOfTheTakenTrees
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hTold : (cF.blocksInOrder.map fun y => y.oracles.flatten) = toldFull :=
    toldOf_of_cut (tests_at_head h.toAtMg O).2.1
  have n2 : treesTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 2 =
      0 := (treesTo_at_head h.toAtMg O 2).trans t2
  have n356 : treesTo (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread.bs
      356 = 82 := (treesTo_at_head h.toAtMg O 356).trans t356
  have hb2' : cF.blocksInOrder[2]? = some blockOpening := hb2
  have hb356' : cF.blocksInOrder[356]? = some blockLast := hb356
  have e2 : toldFull[2]? = some blockOpening.oracles.flatten := by
    rw [← hTold, List.getElem?_map, hb2']
    rfl
  have e356 : toldFull[356]? = some blockLast.oracles.flatten := by
    rw [← hTold, List.getElem?_map, hb356']
    rfl
  rw [e2] at w1
  rw [e356] at w82
  obtain ⟨told1, ht1, hw1⟩ := Option.map_eq_some_iff.1 w1
  obtain ⟨told82, ht82, hw82⟩ := Option.map_eq_some_iff.1 w82
  have ht1' : blockOpening.oracles.flatten[1]? = some told1 := ht1
  have ht82' : blockLast.oracles.flatten[0]? = some told82 := ht82
  have hj1 : 1 < opening.P.trees.length := by
    rw [← told_length, ← ho2]
    exact (List.getElem?_eq_some_iff.1 ht1').1
  have hj82 : 0 < lastSending.P.trees.length := by
    rw [← told_length, ← ho356]
    exact (List.getElem?_eq_some_iff.1 ht82').1
  constructor
  · intro k v hd
    have a := ownTreeOfASendingHasItsToldWidth Bk _ _ _ _ _ _ _ _ _ 2 _ wit opening own₀ offOpening
      blockOpening hT2 hb2 ho2 hc2 1 hj1 told1 ht1' k v hd
    rw [n2, hw1] at a
    exact a
  · intro k v hd
    have a := ownTreeOfASendingHasItsToldWidth Bk _ _ _ _ _ _ _ _ _ 356 _ wit lastSending own₀
      offLast blockLast hT356 hb356 ho356 hc356 0 hj82 told82 ht82' k v hd
    rw [n356, hw82] at a
    exact a

theorem sharedChainsTakenTreeHasItsWidth : SharedChainsTakenTreeHasItsWidth := by
  intro o Z D r Zp Np cF h Bk W₀ Rc X₀ weights rand testOnU testOnOmega own₀ hB k v hd
  obtain ⟨c2, c5, -, -⟩ := covers_head h hB
  obtain ⟨y, hy, Wr⟩ := written_at_head h
  have a := omegaWidthWritten
  rw [hy] at a
  simp only [Option.all_some, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at a
  have h3 : treesU (VerifiableInference.Desc.K1.qAt Zp Np) ≤ 3 := by
    rw [qAt_written Wr Np]
    exact a.2
  rw [words_low _ weights rand testOnU testOnOmega own₀ h3 1 (by omega) k v hd c2 c5,
    qAt_written Wr Np]
  exact a.1

theorem widthsOfTheThreeTakenTrees : WidthsOfTheThreeTakenTrees := by
  intro W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    wit opening lastSending own₀ offOpening offLast blockOpening blockLast Ws Rs Xs weights rand
    testOnU testOnOmega ownShared hb2 ho2 hc2 hT2 hb356 ho356 hc356 hT356 hB
  obtain ⟨a, b⟩ := firstChainsTakenTreesHaveTheirWidths W₀ Rc Tr X Z D r Zp Np cF x h Ky X₀ H Bk Q
    test carryX item n₁ n₂ b₀ Vd Rd Kp w wit opening lastSending own₀ offOpening offLast
    blockOpening blockLast hb2 ho2 hc2 hT2 hb356 ho356 hc356 hT356
  exact ⟨a, b, sharedChainsTakenTreeHasItsWidth OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg Bk Ws Rs Xs
    weights rand testOnU testOnOmega ownShared hB⟩

end ProofFile.Honest.K12.Part4

#print axioms ProofFile.Honest.K12.Part4.toldWidthsOfTheTakenTrees
#print axioms ProofFile.Honest.K12.Part4.toldWidths_control
#print axioms ProofFile.Honest.K12.Part4.omegaWidthWritten
#print axioms ProofFile.Honest.K12.Part4.omegaWidthWritten_control
#print axioms ProofFile.Honest.K12.Part4.told_is_first_round
#print axioms ProofFile.Honest.K12.Part4.told_length
#print axioms ProofFile.Honest.K12.Part4.ownTreeOfASendingHasItsToldWidth
#print axioms ProofFile.Honest.K12.Part4.firstChainsTakenTreesHaveTheirWidths
#print axioms ProofFile.Honest.K12.Part4.sharedChainsTakenTreeHasItsWidth
#print axioms ProofFile.Honest.K12.Part4.widthsOfTheThreeTakenTrees
