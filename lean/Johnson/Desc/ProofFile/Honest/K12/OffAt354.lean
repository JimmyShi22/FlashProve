-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/OffAt354.lean: THE PROXIMITY TEST's BLOCK IN THE FIRST CHAIN,
NUMBER 354: HOW MANY TREES IT DECLARES, HOW MANY TREES AND ROUNDS STAND IN FRONT OF IT, AND THAT OUR
LOT OF TREES' off STAYS WITHIN ITS ROUNDS. PUBLIC DATA ALONE: counts. No definition, seven theorems.

Why. (1) The frame's authors' `ofLots_hfix` (Honest/Thread/ScriptLots.lean) asks of every lot of
trees that off j is at most the number of rounds of its sub-protocol, for j below the number of
trees declared there; another group of authors asked us for that at our member. (2)
ShareAtHead.lean, OwnedAtHead.lean and the files over them write 77 for the first switch's tree and
354 for the member, by hand. Here 77 is shown to be `treesTo cF.blocksInOrder 354`.

  `treesLens_at_head`   a helper: the number of trees that each block of the first chain declares,
                 read off the fifth field of the library's written cut
  `writtenTrees_354`, `writtenTrees_bite`   by Lean's kernel: row 354 of that cut has five trees,
                 the rows before it 77 in all; a control: with row 354 the sum is 82
  `test_trees_L`   the block at 354 declares five trees
  `treesTo_354`, `roundsTo_354`   `treesTo cF.blocksInOrder 354` = 77, `roundsTo cF.blocksInOrder 354` = 48237
  `off_at_354`   the hypothesis of `ofLots_hfix` at b = 354 and `testTreeLot`

By what. AtProof/CutAtL.lean has the like for rounds, and is called: `test_rounds_L` (33 rounds),
`front_rounds_L` (48237 in front). For trees: `First.toldOf_cut`
(Johnson/Desc/First/CutAtNumbers.lean) and `OnBytes.Road.K4.cut_of_head`
(Johnson/Road/K4/K4HeadWritten.lean). `seedRound_le_LFull` (LotsLaid.lean).

Near it, not called. `seedRound_LFull` (ScriptLotsAtL.lean): the five values of off at the record,
3, 10, 16, 22, 29. `H2K12.trees_front_of`, `roots_behind_no`
(Johnson/Loose/H2K12/ClosedAtHead354.lean): 77 and 82 again, as counts of trees in the data of the
first 48237 and 48270 rounds. `k6_row_at_head` (Honest/K6/Law/RoundsWritten.lean): every member's
whole written row, under the stronger head at the concrete earlier hash.

Limits.
- All that binds whoever builds on ScriptLots.lean (its head) binds here.
- hst IS A HYPOTHESIS: `off_at_354` is about a job whose stages are the written record's. That the
  job laid at member 354 is such a job is not shown here.
- h, the head, is assumed; at a public part beyond it nothing is said.
- `off_at_354` SAYS LESS THAN IS SO. It bounds off by 33. By the numbers, off τ is the very round at
  which row 354 tells its tree number τ; no theorem says that.
- It is about `testTreeLot`. The step from a record's tl at 354 to that lot is `testTl_at`
  (ScriptLots.lean), not made here.
- `treesTo_354` and `roundsTo_354` are called by no file yet: the files named under "Why" still
  write 77.
- Counts only: nothing on what the rounds or the trees hold.
- The one control tries the sum of 77. `off_at_354` has none; at j = 5 the bound would still hold.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.CutAtL
import Johnson.Desc.ProofFile.Honest.K12.LotsLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.PlanWritten (cutFirstFull)
open ProofFile.Honest.K12.AtProof (test_rounds_L front_rounds_L)

variable {Bk : ProverCoinCounts} {W X : Type} {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
  {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- A helper: the number of trees that each block of the first chain declares is the length of what
the written cut's row tells. -/
theorem treesLens_at_head (h : P5J.AtMg o Z D r₀ Zp Np cF) :
    cF.blocksInOrder.map (fun b => (b.oracles.flatMap id).length) = cutFirstFull.map fun r =>
      (r.2.2.2.2.1.flatMap (·.2)).length := by
  have e := VerifiableInference.Desc.First.toldOf_cut cF.blocksInOrder
  rw [OnBytes.Road.K4.cut_of_head h] at e
  have e' := congrArg (List.map List.length) e
  unfold VerifiableInference.Desc.First.toldOf at e'
  rw [List.map_map, List.map_map] at e'
  rw [show (fun b : Block P5J.TS ProofFile.Cl => (b.oracles.flatMap id).length) =
    List.length ∘ fun b => b.oracles.flatten from funext fun b => by
      show (b.oracles.flatMap id).length = b.oracles.flatten.length
      rw [List.flatMap_id]]
  exact e'

set_option maxRecDepth 1000000 in
/-- By the kernel: row 354 of the written cut has five trees; the 354 rows before it have 77. -/
theorem writtenTrees_354 :
    (cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length)[354]? = some 5 ∧
      ((cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 354).sum = 77 := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: with row 354 the sum is 82. -/
theorem writtenTrees_bite :
    ((cutFirstFull.map fun r => (r.2.2.2.2.1.flatMap (·.2)).length).take 355).sum = 82 := by
  decide +kernel

/-- **The block at 354 declares five trees.** -/
theorem test_trees_L (h : P5J.AtMg o Z D r₀ Zp Np cF) {b : Block P5J.TS ProofFile.Cl}
    (hb : cF.blocksInOrder[354]? = some b) :
    (b.oracles.flatMap id).length = 5 := by
  have e : (cF.blocksInOrder.map fun b => (b.oracles.flatMap id).length)[354]? = some 5 := by
    rw [treesLens_at_head h]
    exact writtenTrees_354.1
  rw [List.getElem?_map, hb] at e
  exact Option.some.inj e

/-- **77 trees are declared before member 354**: the first switch's tree has the number 77. -/
theorem treesTo_354 (h : P5J.AtMg o Z D r₀ Zp Np cF) : treesTo cF.blocksInOrder 354 = 77 := by
  unfold treesTo
  rw [List.length_flatMap, List.map_take, treesLens_at_head h]
  exact writtenTrees_354.2

/-- **48237 rounds are declared before member 354.** -/
theorem roundsTo_354 (h : P5J.AtMg o Z D r₀ Zp Np cF) : roundsTo cF.blocksInOrder 354 = 48237 :=
  front_rounds_L h

/-- **`ofLots_hfix`'s hypothesis at member 354 and `testTreeLot`**, under h and hst. -/
theorem off_at_354 (h : P5J.AtMg o Z D r₀ Zp Np cF) (ch : ℕ) (J : TestJob W X)
    (hst : J.p.nums.stages = H2K.Member.piLFull.nums.stages) (own₀ : X) (n₀ : ℕ)
    (ok : W → List Fmt.Drawn → (ℕ → Stretch) → Bool) :
    ∀ blk, cF.blocksInOrder[354]? = some blk → ∀ j, j < (blk.oracles.flatMap id).length →
      (testTreeLot (Bk := Bk) ch J own₀ n₀ ok).off j ≤ blk.rounds.length := by
  intro blk hb j hj
  rw [test_trees_L h hb] at hj
  rw [test_rounds_L h hb]
  show seedRound J.p.nums.stages j ≤ 33
  rw [hst]
  exact seedRound_le_LFull j hj

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.treesLens_at_head
#print axioms ProofFile.Honest.K12.writtenTrees_354
#print axioms ProofFile.Honest.K12.writtenTrees_bite
#print axioms ProofFile.Honest.K12.test_trees_L
#print axioms ProofFile.Honest.K12.treesTo_354
#print axioms ProofFile.Honest.K12.roundsTo_354
#print axioms ProofFile.Honest.K12.off_at_354
