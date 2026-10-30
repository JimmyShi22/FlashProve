-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLTableHead.lean

It states no goal. No property of the protocol is claimed.

AT THE LIBRARY's OWN THREAD OF THE FIRST
CHAIN (`lettersHead`, Honest/Thread/FirstHead.lean) WHOSE SCRIPT IS THE JOINED ONE (`joinQ`,
Honest/Thread/Join.lean): THE TABLES AND FIXED NUMBERS OF THE CLOSING PROXIMITY TEST's FIVE OWN TREES
(own 77 to 81), in the words in which `plays_head_L` (K12/AtFile/ClosingAtHead.lean) asks them
(htable, hfixed), AND OF THE TREE THAT THE TEST OPENS (own 76): the last code switch's own.

  `writtenTrees_353`, `writtenTrees_352`   by Lean's kernel: row 353 of the written cut has one
                          tree, the rows before it 76 in all; row 352 has none (equations of numbers: no control)
  `finish_trees_L`, `treesTo_353`, `roundsTo_353`   the block at 353 declares one tree; 76 trees and
                          48235 rounds stand in front of it
  `closingTestStages_at_head`  the test's place has six stages
  `closingTestTable_at_joinedScript`          `plays_head_L`'s premise htable, to the letter, at the joined Script
  `closingTestFixed_at_joinedScript`          its premise hfixed, to the letter, at the joined Script
  `finishTable_at_joinedScript`     the thread's table at own 76 is `switchTableAt` at table number 0, as a
                          function; its fixed number is `roundsTo cF.blocksInOrder 353`, that is 48235

By what. LotLTable.lean's four; `test_trees_L`, `treesLens_at_head`, `roundsTo_354` (K12/OffAt354.lean);
`places_at_L`, `finish_two_rounds` (K12/AtProof/CutAtL.lean); `numbersL_at_head`
(K12/AtProof/LotAtDoor.lean); `nums_head_L` (AtFullSide/K12/RestTiesAtHeadL.lean).

Hypotheses. h: the head. hb: 354 (353) is no number of a job of the shared sending. htl: the record
of the other senders holds at 354 the test's lot of trees, AT THE JOB `jobL` AT THE FILLED DOOR, AT
THE SAME own₀, AT n₀ = the rounds in front of the member AND AT ok = "always yes"; at 353 the switch's
own table at the place pl, the letters of `jobL`.

Limits.
- The jobs and the record are letters: hb and htl are premises here; LotLTableFirstScript.lean pays them
  (`numbers_apart_first`, `testLot_at_first`, `finishLot_at_first`).
- At a record whose lot at 354 has another ok, another own₀ or another n₀ nothing is said.
- The equations hold at all coins; where the frame lends a part nothing they speak of a table
  without a word. Nothing is asked of the book.
- Full size, the format's second hash function alone.
- Where this file names `plays_head_L`, it is the law of that name in K12/AtFile/ClosingAtHead.lean.
  It is not beneath this file: LotLTableFirstScript.lean lays these ends into it by a Lean term.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotLTable
import Johnson.Desc.ProofFile.Honest.K12.AtProof.LotAtDoor
import Johnson.Desc.ProofFile.Honest.K12.OffAt354
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import AtFullSide.K12.RestTiesAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain Place Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.PlanWritten (cutFirstFull)
open ProofFile.Honest.FirstThread (lettersHead Script WtF Others joinQ roundsTo_succ)
open ProofFile.Honest.K1 (SendJob PlaceIn)
open ProofFile.Honest.K12.AtProof (jobL doorAtL numbersL_at_head places_at_L finish_two_rounds)
open P5J (AtMg AtMgA CellsM TS)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 Counts -/

set_option maxRecDepth 1000000 in
/-- By the kernel: row 353 of the written cut has one tree; the 353 rows before it have 76. -/
theorem writtenTrees_353 :
    (cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length)[353]? = some 1 ∧
      ((cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 353).sum = 76 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A second fact, no control: row 352 has no tree, and the 352 rows before it have 76 too. -/
theorem writtenTrees_352 :
    (cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length)[352]? = some 0 ∧
      ((cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 352).sum = 76 := by
  decide +kernel

section counts
variable {o : ProofFile.SecondHashFunctionArgument}

/-- **The block at 353 declares one tree.** -/
theorem finish_trees_L (h : AtMg o Z D₀ r Zp Np cF) {b : Block S ProofFile.Cl}
    (hb : cF.blocksInOrder[353]? = some b) : (b.oracles.flatMap id).length = 1 := by
  have e : (cF.blocksInOrder.map fun b => (b.oracles.flatMap id).length)[353]? = some 1 := by
    rw [treesLens_at_head h]
    exact writtenTrees_353.1
  rw [List.getElem?_map, hb] at e
  exact Option.some.inj e

/-- **76 trees are declared before member 353.** -/
theorem treesTo_353 (h : AtMg o Z D₀ r Zp Np cF) : treesTo cF.blocksInOrder 353 = 76 := by
  unfold treesTo
  rw [List.length_flatMap, List.map_take, treesLens_at_head h]
  exact writtenTrees_353.2

/-- **48235 rounds are declared before member 353.** -/
theorem roundsTo_353 (h : AtMg o Z D₀ r Zp Np cF) : roundsTo cF.blocksInOrder 353 = 48235 := by
  obtain ⟨⟨b, hb, -⟩, -⟩ := places_at_L h
  have e := roundsTo_succ hb
  rw [roundsTo_354 h, finish_two_rounds h hb] at e
  omega

/-- **The test's place has six stages.** -/
theorem closingTestStages_at_head (h : AtMg o Z D₀ r Zp Np cF) :
    (H2U.p12OfMade Zp.made).nums.stages.length = 6 := by
  rw [numbersL_at_head h, Light.nums_head_L h]
  decide +kernel

end counts

/-! ## 2 The tables -/

section
variable (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X Xj Xk : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (cells : Local W₀ Rc ProofFile.Inst Tr → CellsM OnBytes.Flat.numsFull)
  (tok : Local W₀ Rc ProofFile.Inst Tr → P5J.At.Tok) (arr : ℕ → ℕ → ℕ)
  (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn Xj) (ownK : Xk)
  (jobs : List (ℕ × SendJob (PlaceIn Xj) Xk)) (O : Others Bk (Local W₀ Rc ProofFile.Inst Tr))
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
  (closing : K2.Closing) (pl : K2.SwitchPlace)

/-- **`plays_head_L`'s premise htable, at the joined Script.** -/
theorem closingTestTable_at_joinedScript (hb : 354 ∉ jobs.map (·.1)) (own₀ : X) {n₀ : ℕ}
    (hn₀ : n₀ = roundsTo cF.blocksInOrder 354)
    (htl : O.tl 354 = testTreeLot 0 (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
      own₀ n₀ (fun _ _ _ => true)) :
    ∀ τ, τ + 1 < (H2U.p12OfMade Zp.made).nums.stages.length →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀ Vd
          Rd Kp w).thread.table (.own (treesTo cF.blocksInOrder 354 + τ)) =
        testTbl (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁
            n₂ b₀ Vd Rd Kp w).thread.chain
          (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl) own₀
          ((lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀
            Vd Rd Kp w).thread.front + roundsTo cF.blocksInOrder 354) (fun _ _ _ => true) τ := by
  intro τ hτ
  obtain ⟨-, blk, hblk, -⟩ := places_at_L h.toAtMg
  rw [closingTestStages_at_head h.toAtMg] at hτ
  have e : (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂
      b₀ Vd Rd Kp w).thread.front + roundsTo cF.blocksInOrder 354 = n₀ := by
    rw [hn₀]
    exact Nat.zero_add _
  rw [e]
  exact testTable_at_joined (bs := cF.blocksInOrder) (front := 0) (arr := arr) (wit := wit) (own₀ := ownK)
    (jobs := jobs) (O := O) cells tok (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs
    O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread rfl rfl rfl rfl 0 _ own₀ n₀ _ hb htl hblk
    (by rw [test_trees_L h.toAtMg hblk]; omega)

/-- **`plays_head_L`'s premise hfixed, at the joined Script.** -/
theorem closingTestFixed_at_joinedScript (hb : 354 ∉ jobs.map (·.1)) (own₀ : X) (n₀ : ℕ)
    (htl : O.tl 354 = testTreeLot 0 (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) D readers closing pl)
      own₀ n₀ (fun _ _ _ => true)) :
    ∀ τ, τ + 1 < (H2U.p12OfMade Zp.made).nums.stages.length →
      (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀ Vd
          Rd Kp w).thread.fixed (.own (treesTo cF.blocksInOrder 354 + τ)) =
        (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀ Vd
            Rd Kp w).thread.front + roundsTo cF.blocksInOrder 354 +
          seedRound (H2U.p12OfMade Zp.made).nums.stages τ := by
  intro τ hτ
  obtain ⟨-, blk, hblk, -⟩ := places_at_L h.toAtMg
  rw [closingTestStages_at_head h.toAtMg] at hτ
  exact testFixed_at_joined (bs := cF.blocksInOrder) (front := 0) (arr := arr) (wit := wit) (own₀ := ownK)
    (jobs := jobs) (O := O) cells tok (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs
    O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread rfl rfl rfl rfl 0 _ own₀ n₀ _ hb htl hblk
    (by rw [test_trees_L h.toAtMg hblk]; omega)

/-- **The tree that the test opens, own 76, at the joined Script**: the last code switch's table
number 0, as a function of coins, input and challenges; fixed by the rounds in front of member 353.
-/
theorem finishTable_at_joinedScript (hb : 353 ∉ jobs.map (·.1)) (Sd : K2.Sender)
    (htl : O.tl 353 =
      ⟨fun j k v hd => (pl.place, K2.switchTableAt Bk 0 Sd D readers closing pl k v hd j),
        fun _ => 0⟩) :
    (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀ Vd Rd
        Kp w).thread.table (.own 76) =
      (fun k v hd => (pl.place, K2.switchTableAt Bk 0 Sd D readers closing pl k v hd 0)) ∧
    (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX item n₁ n₂ b₀ Vd Rd
        Kp w).thread.fixed (.own 76) = roundsTo cF.blocksInOrder 353 ∧
    roundsTo cF.blocksInOrder 353 = 48235 := by
  obtain ⟨⟨blk, hblk, -⟩, -⟩ := places_at_L h.toAtMg
  have e := switchTable_at_joined (bs := cF.blocksInOrder) (front := 0) (arr := arr) (wit := wit)
    (own₀ := ownK) (jobs := jobs) (O := O) cells tok (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK
    jobs O) test carryX item n₁ n₂ b₀ Vd Rd Kp w).thread rfl rfl rfl rfl hb hblk 0 Sd D readers
    closing pl htl (j := 0) (by rw [finish_trees_L h.toAtMg hblk]; omega)
  have e76 : treesTo (lettersHead h H (joinQ cF.blocksInOrder 0 cells tok arr wit ownK jobs O) test carryX
      item n₁ n₂ b₀ Vd Rd Kp w).thread.bs 353 + 0 = 76 := treesTo_353 h.toAtMg
  rw [e76] at e
  exact ⟨e.1, e.2.trans (Nat.zero_add _), roundsTo_353 h.toAtMg⟩

end

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.writtenTrees_353
#print axioms ProofFile.Honest.K12.writtenTrees_352
#print axioms ProofFile.Honest.K12.finish_trees_L
#print axioms ProofFile.Honest.K12.treesTo_353
#print axioms ProofFile.Honest.K12.roundsTo_353
#print axioms ProofFile.Honest.K12.closingTestStages_at_head
#print axioms ProofFile.Honest.K12.closingTestTable_at_joinedScript
#print axioms ProofFile.Honest.K12.closingTestFixed_at_joinedScript
#print axioms ProofFile.Honest.K12.finishTable_at_joinedScript
