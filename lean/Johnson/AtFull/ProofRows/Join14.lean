-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/ProofRows/Join14.lean: the third step of the proof file's seat
(`LPFD.Full.proofDataAndDecisionOfDescription`, Johnson/Desc/Laid/ProofFull.lean): the FOURTEEN entry tests
(`LPFD.lawsAsk`, Johnson/Desc/Laid/ProofAsks.lean) all accept, FROM WHAT THEY READ.

It compiles only where `lawsAsk` has the fourteenth test (`every M Desc.LinkJoin.rowsMadeB`).
A twin for a `lawsAsk` of thirteen tests is not in this library; a tree could hold only one of
the two. So the three small laws on rows 1, 9 and 10 stand here, and the names here lie one
namespace deeper (`Fourteen`). The one premise more than with thirteen tests: k₄, row 14's test
at Zp.

  `rows_none`: in scope, at any o for the second hash: from two returns (the public data W of
    `publicOfO`; the public part Zp of `ProofFile.pureRoad.pub`), nine premises at written values and
    eleven tests with code on W and Zp: `LPFD.firstNo (LPFD.lawsAsk o Z.pol Z.lay Z.KL F D) = none`.
  `laid_of_rows`: with `F.planWord = none` besides: `proofDataAndDecisionOfDescription` returns, at the written data.

Which row reads what.
  row 1 (the declared rounds are the written ones): the parameter file's strict scan, F.roundsDeclaredByBlocks and
    F.tableDepth. In scope the scan returns at the full size's key (`seat_eq_in_scope`): two
    equations are left.
  rows 2 to 8 (attention): each makes the public data anew by `publicOfO` and asks `K5Asks.rowW k`
    of it: stated here over that return.
  row 9 (`madeRow`): four tests on Zp; for each a law says "the written value is accepted": four
    premises are left, two of them bundles of equations (`MadeWritten`, `FirstWritten`).
  row 10 (`cutRow`): F's three chains' cuts: three equations are left.
  rows 11 to 13 (`K3Asks.digEntry`, `readsEntry`, `headEntry`): tests on Zp: kept as tests.
  row 14 (`LinkJoin.rowsMadeB`, Johnson/Desc/First/Link/RowsRun.lean): a test on Zp: kept as a test.
D is read by no row. The data's return follows from row 1's two equations (`data_proofFull`).

Limits. A JOINING: calls of laws that stand elsewhere. IT PAYS NO PREMISE: that the files are in
scope, the two returns, the nine premises and the eleven tests are shown nowhere here. No soundness
is claimed.

-/
import Johnson.Desc.Laid.ProofFull
import Johnson.Desc.Laid.AsksFirstLaw
import Johnson.Goal.Numbers.PlanWrittenRow
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.ProofRows.Fourteen
open VerifiableInference VerifiableInference.PlanWritten
open Johnson.G Johnson.G.OfPlan VerifiableInference.Number
open VerifiableInference.Desc (FileDescription)
open VerifiableInference.Desc.First.Att.P (K5Asks.rowW)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {W : OnBytes.Model.Verify.Public} {Zp : ProofFile.Pub}
  {F : FileDescription ProofFile.Inst}

/-- Row 1, in scope, from its two equations. -/
theorem row1 (hZ : VerifierAndGoals.InScope Z = true)
    (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull) (hd : F.tableDepth = 32) :
    seatPinnedProof Z.pol F = true := by
  rw [seat_eq_in_scope F hZ]
  unfold descPinnedProof descPinned declPinned
  rw [if_pos rfl]
  exact (declIs_iff _ _ _ _ _).2 ⟨hw, hd⟩

/-- Row 9's test, from its four equations. -/
theorem row9 (m₁ : MadeWritten Zp.p.chains.made) (m₂ : FirstWritten Zp.first)
    (m₃ : Zp.made.proof = proofSendsFull) (m₄ : xShapeOf Zp.p.X = xShapeFull) :
    madeRow Zp = true := by
  unfold madeRow
  rw [madeIs_of m₁, firstIs_of m₂, proofSendsIs_of m₃, xShapeIs_of m₄]
  rfl

/-- Row 10's test, from its three equations. -/
theorem row10 (c₁ : cutOf F.first.blocksInOrder = cutFirstFull) (c₂ : cutOf F.shared.blocksInOrder = cutSharedFull)
    (c₃ : cutOf F.second.blocksInOrder = cutSecondFull) : cutRow F Zp = true := by
  unfold cutRow cutIs
  rw [c₁, c₂, c₃]
  exact same_self

/-- **In scope, where the two returns, the nine premises at written values and the eleven tests hold
(all named premises), all fourteen entry tests accept.** -/
theorem rows_none (hZ : VerifierAndGoals.InScope Z = true) (D : OnBytes.Maker.WholeD)
    (hW : publicOfO o Z.pol Z.KL (some Z.lay) = .ok W)
    (hP : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp)
    (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull) (hd : F.tableDepth = 32)
    (att : ∀ k < 7, K5Asks.rowW k W = true)
    (m₁ : MadeWritten Zp.p.chains.made) (m₂ : FirstWritten Zp.first)
    (m₃ : Zp.made.proof = proofSendsFull) (m₄ : xShapeOf Zp.p.X = xShapeFull)
    (c₁ : cutOf F.first.blocksInOrder = cutFirstFull) (c₂ : cutOf F.shared.blocksInOrder = cutSharedFull)
    (c₃ : cutOf F.second.blocksInOrder = cutSecondFull)
    (k₁ : Desc.K3Asks.digEntry Zp = true) (k₂ : Desc.K3Asks.readsEntry Zp = true)
    (k₃ : Desc.K3Asks.headEntry Zp = true) (k₄ : Desc.LinkJoin.rowsMadeB Zp = true) :
    LPFD.firstNo (LPFD.lawsAsk o Z.pol Z.lay Z.KL F D) = none := by
  have hM : Desc.Door.planOf o Z.pol Z.lay Z.KL = some Zp := by
    unfold Desc.Door.planOf
    rw [hP]
    rfl
  have a : ∀ k < 7, Desc.First.Att.P.K5Asks.rowO k o Z.pol Z.lay Z.KL = true := by
    intro k hk
    unfold Desc.First.Att.P.K5Asks.rowO
    rw [hW]
    exact att k hk
  rw [LPFD.firstNo_none]
  intro t ht
  simp only [LPFD.lawsAsk, hM, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row1 hZ hw hd
  · exact a 0 (by omega)
  · exact a 1 (by omega)
  · exact a 2 (by omega)
  · exact a 3 (by omega)
  · exact a 4 (by omega)
  · exact a 5 (by omega)
  · exact a 6 (by omega)
  · simp only [Desc.Door.atFull, Option.any_some, row9 m₁ m₂ m₃ m₄, Bool.or_true]
  · simp only [Desc.Door.atFull, Option.any_some, row10 c₁ c₂ c₃, Bool.or_true]
  · simpa only [Desc.Door.every, Option.any_some] using k₁
  · simpa only [Desc.Door.every, Option.any_some] using k₂
  · simpa only [Desc.Door.every, Option.any_some] using k₃
  · simpa only [Desc.Door.every, Option.any_some] using k₄

/-- **Under the same premises and `F.planWord = none`, the seat's third step returns, at the written
data.** -/
theorem laid_of_rows (hZ : VerifierAndGoals.InScope Z = true) (hn : F.planWord = none)
    (hW : publicOfO o Z.pol Z.KL (some Z.lay) = .ok W)
    (hP : ProofFile.pureRoad.pub o Z.pol Z.lay Z.KL = .ok Zp)
    (hw : writtenOf "proof file" F.roundsDeclaredByBlocks = .ok dryProofFull) (hd : F.tableDepth = 32)
    (att : ∀ k < 7, K5Asks.rowW k W = true)
    (m₁ : MadeWritten Zp.p.chains.made) (m₂ : FirstWritten Zp.first)
    (m₃ : Zp.made.proof = proofSendsFull) (m₄ : xShapeOf Zp.p.X = xShapeFull)
    (c₁ : cutOf F.first.blocksInOrder = cutFirstFull) (c₂ : cutOf F.shared.blocksInOrder = cutSharedFull)
    (c₃ : cutOf F.second.blocksInOrder = cutSecondFull)
    (k₁ : Desc.K3Asks.digEntry Zp = true) (k₂ : Desc.K3Asks.readsEntry Zp = true)
    (k₃ : Desc.K3Asks.headEntry Zp = true) (k₄ : Desc.LinkJoin.rowsMadeB Zp = true) :
    LPFD.Full.proofDataAndDecisionOfDescription o Z.pol Z.lay Z.KL F = .ok (writtenPFull, LPFD.Full.proofDecisionOfDescription F) := by
  unfold LPFD.Full.proofDataAndDecisionOfDescription
  rw [hn]
  simp only [data_proofFull F hw hd,
    rows_none hZ writtenPFull hW hP hw hd att m₁ m₂ m₃ m₄ c₁ c₂ c₃ k₁ k₂ k₃ k₄]

end Johnson.AtFull.ProofRows.Fourteen

#print axioms Johnson.AtFull.ProofRows.Fourteen.row1
#print axioms Johnson.AtFull.ProofRows.Fourteen.row9
#print axioms Johnson.AtFull.ProofRows.Fourteen.row10
#print axioms Johnson.AtFull.ProofRows.Fourteen.rows_none
#print axioms Johnson.AtFull.ProofRows.Fourteen.laid_of_rows
