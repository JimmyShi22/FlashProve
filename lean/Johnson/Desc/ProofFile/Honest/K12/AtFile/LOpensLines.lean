-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LOpensLines.lean: the field `opens` of `FrontAtT`
(ClosingAtL.lean) at the first chain's closing proximity test: all of it but the columns. The test
opens one tree that was sent in front of it: the finish's, of depth 23, tree number 76 of the chain,
with 77 trees sent in front.

  `opensFit_written`      a closed line: `opensFitB` (K12/OpensFitB.lean) at the written place, the
                          depths [23], the sources [own 76] and 77 trees sent
  `opensFit_written_no`   controls: 76 or 78 trees sent · depth 22 · own 75: it says no
  `closingDepth_written`  a closed line: at the written finish the sending's tree 0 has depth 23
  `opens_of_columns`      under the library's head (`P5J.AtMg`): the field `opens` at a job J' that
                          is `jobL` patched at a stand, from two premises on the tables at hand
  `opens_at_stand`        the same at a stand of a thread over the head's chain, without hSent

The two premises of `opens_of_columns`.
  hSent      77 trees are sent in front
  hColumns   at each position below 2 ^ 23 the column at hand of tree own 76 is the column of the
             job's one tree

Limits.
- hColumns IS A PREMISE. It ties the thread's tables to the job's tree, which is made of the coins
  lent to the test's parts. It is shown at no stand here.
- `colAt` is the empty list where no table is at hand: hColumns does not say that one is there.
- The full size alone: the library's written values.
- Nothing on completeness, on soundness or on hiding.
NOT IN FRONT OF A LAW OVER COINS: `opens_of_columns` and `opens_at_stand` bear this label; the rule
is at its home, the head of Johnson/Bind/ForProver/FiveFieldsAt.lean. Their ground: hColumns ties
the letters E and c to a run's coins; the thread from `Thr` as a premise.
Terms: the head of LShapeTest.lean; Johnson/Desc/ProofFile/Honest/K12/RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.ClosingStand
import Johnson.Desc.ProofFile.Honest.K12.OpensFitB
import Johnson.Desc.ProofFile.Honest.K12.OffAt354
import Johnson.Desc.ProofFile.Honest.Thread.First
import Johnson.AtFull.Shape.TestNumbersAtHead
import AtFullSide.K12.FitsAtHeadL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Chain Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Member (piLFull)
open ProofFile.Honest.K12 (TestJob atStand firstPart restPart restCoins OpensFit OldAt opensFitB
  opensFit_of_B)
open P5J (TS)

set_option maxRecDepth 1000000 in
/-- **The declared openings are the term's**, at the written place. -/
theorem opensFit_written : opensFitB false piLFull.nums.stages
    (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23] [.own 76] 77 = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Controls, each with one argument changed. -/
theorem opensFit_written_no :
    (opensFitB false piLFull.nums.stages (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23]
        [.own 76] 76 ||
      opensFitB false piLFull.nums.stages (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23]
        [.own 76] 78 ||
      opensFitB false piLFull.nums.stages (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [22]
        [.own 76] 77 ||
      opensFitB false piLFull.nums.stages (proximityTestKind guardedProximityTestParts piLFull : Block T12 Unit).rounds [23]
        [.own 75] 77) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- At the written finish the sending's tree 0 has depth 23. -/
theorem closingDepth_written : finishW.any (fun p =>
    (((VerifiableInference.Desc.Own.treesMade p.sizes.codes (sentL p)).getD {}).shapes.getD 0
      default).logN == 23) = true := by decide +kernel

variable {W₀ Rc Xi Tr X : Type}
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D₀ : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The field `opens` of `FrontAtT`, from the count of trees and the columns at hand.** -/
theorem opens_of_columns (h : P5J.AtMg o Z D₀ r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (m : Mid (Local W₀ Rc Xi Tr) X) (E : Env) (T : T12) (J' : TestJob (Local W₀ Rc Xi Tr) X)
    (hJ : J' = atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) m.st.input
      (frontOf m) T)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J'])
    (hSent : E.sent = 77)
    (hColumns : ∀ y, y < 2 ^ 23 → colAt E.tree (.own 76) y =
      ((J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).getD 0 (0, fun _ => [])).2 y) :
    ∃ depths src₀,
      (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).map (·.1) = depths ∧
      OpensFit J' (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAt E (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) src₀ := by
  subst hJ
  have e : H2U.p12OfMade Zp.made = piLFull := Johnson.AtFull.Shape.p12_at_head h
  have eF : finishAt Zp G = finishW := by
    unfold finishAt finishW
    rw [places_head h hG]
  have hd : (((VerifiableInference.Desc.Own.treesMade pl.sizes.codes
      (sentL pl)).getD {}).shapes.getD 0 default).logN = 23 := by
    have k := closingDepth_written
    rw [← eF, hf] at k
    exact beq_iff_eq.1 k
  refine ⟨[23], fun k => [Fmt.TreeSource.own 76].getD k (.own 0), ?_, ?_, ?_, ?_⟩
  · show [(((VerifiableInference.Desc.Own.treesMade pl.sizes.codes (sentL pl)).getD {}).shapes.getD
      0 default).logN] = [23]
    rw [hd]
  · rw [hSent]
    refine opensFit_of_B _ _ _ _ _ ?_
    show opensFitB false (H2U.p12OfMade Zp.made).nums.stages
      (proximityTestKind guardedProximityTestParts (H2U.p12OfMade Zp.made) : Block T12 Unit).rounds [23] [.own 76] 77 = true
    rw [e]
    exact opensFit_written
  · intro k hk n hn
    have hk1 : k < 1 := hk
    obtain rfl : k = 0 := by omega
    have hn' : Fmt.TreeSource.own 76 = .own n := hn
    injection hn' with hn''
    rw [hSent]
    omega
  · intro k hk y hy
    have hk1 : k < 1 := hk
    obtain rfl : k = 0 := by omega
    have hy' : y < 2 ^ (((VerifiableInference.Desc.Own.treesMade pl.sizes.codes
        (sentL pl)).getD {}).shapes.getD 0 default).logN := hy
    rw [hd] at hy'
    exact hColumns y hy'

variable {Bk : ProverCoinCounts} {P Cells Tok M : Type}

/-- **The same at a stand of a thread over the head's chain**, without the premise on the count of
trees. -/
theorem opens_at_stand (h : P5J.AtMg o Z D₀ r Zp Np cF) {G : ProofFile.Ground}
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some G) {pl : K2.SwitchPlace}
    (hf : finishAt Zp G = some pl) (door : Local W₀ Rc Xi Tr → Front X → T12) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : K2.Closing)
    (L : ProofFile.Honest.FirstThread.Letters Bk ProofFile.Cl W₀ Rc Xi Tr X P Cells Tok M)
    (hbs : L.bs = cF.blocksInOrder) {k : Coins Bk} {s : TS} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
    (hT : Thr L.thread 354 k s m E) (T : T12) (J' : TestJob (Local W₀ Rc Xi Tr) X)
    (hJ : J' = atStand (jobL (H2U.p12OfMade Zp.made) door D readers closing pl) m.st.input
      (frontOf m) T)
    (c : RowCoins [(firstPart J' : Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X), restPart J'])
    (hColumns : ∀ y, y < 2 ^ 23 → colAt E.tree (.own 76) y =
      ((J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).getD 0 (0, fun _ => [])).2 y) :
    ∃ depths src₀,
      (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))).map (·.1) = depths ∧
      OpensFit J' (proximityTestKind guardedProximityTestParts J'.p : Block T12 Unit).rounds depths src₀ E.sent ∧
      OldAt E (J'.trees₀ m.st.input (frontOf m) (restCoins J' c.2.1).mem
        (J'.first m.st.input (frontOf m) (restCoins J' c.2.1))) src₀ := by
  have hSent : E.sent = 77 := by
    obtain ⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩ := hT
    have e : L.thread.bs = cF.blocksInOrder := hbs
    rw [h3, e]
    exact ProofFile.Honest.K12.treesTo_354 h
  exact opens_of_columns h hG hf door D readers closing m E T J' hJ c hSent hColumns

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.opens_at_stand
#print axioms ProofFile.Honest.K12.AtProof.opensFit_written
#print axioms ProofFile.Honest.K12.AtProof.opensFit_written_no
#print axioms ProofFile.Honest.K12.AtProof.closingDepth_written
#print axioms ProofFile.Honest.K12.AtProof.opens_of_columns
