-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
AtFullSide/Honest/TermMade.lean: the maker's return at a filling read through the maps `matrixInput` and
`tableCoins` of E2E/TheHonestProver.lean.

  `range_matrixInput`  its named member is in range
  `matrixInput_trace_served`  where the matrix holds an index that serves the request, the trace is there
  `fillZ`       `widerFillAtC matrixInput` read through the identity on the index and `tableCoins`
  `atPure_returns_of_asks`  under the head, the maker returns at any filling over the matrices, read
                through these maps, where what it asks of that filling holds
  `atPure_returns_through`  the same at `fillZ`

Limits.
  * That `tableCoins` forgets nothing that the committer's columns read is not shown here.
  * Both returns are conditional on the head, on the library's test on the public files and on the
    book's return at the written description. `O` is a letter. `atPure_returns_of_asks` takes
    what the maker asks as a premise.
  * Nothing is said of what the returned prover does.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import E2E.TheHonestProver
import Johnson.Desc.ProofFile.Honest.ThruMade

set_option autoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open K5 AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes.Slice (frS frZ)
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

/-- The named member is in range. -/
theorem range_matrixInput : matrixInput.inRange matrixInput.dummy = true := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf
    (VerifiableInference.OnPublicFiles.Flat.matrixOf fullIn.dummy)).isSome = true
  rw [VerifiableInference.OnPublicFiles.Flat.indexOf_eq le_rfl le_rfl
    (VerifiableInference.OnPublicFiles.Flat.holds_matrixOf fullIn.dummy)]
  rfl

/-- **Where the matrix holds an index and that index serves the request, the trace is there.** -/
theorem matrixInput_trace_served {Zq : ProofFile.Pub} {M : FullSizeMatrix} {i : Cm.Idx} {ξ : ProofFile.Inst}
    {x : Inst.Model.Instance Inst.Model.ppref}
    (hi : VerifiableInference.OnPublicFiles.Flat.indexOf M = some i) (hx : ProofFile.instOf ξ = some x)
    (hs : OnBytes.HonestTrace.ServesAt Zq.p.X i x) :
    matrixInput.trace Zq M ξ =
      some ⟨OnBytes.HonestTrace.cellOf Zq.p.X (OnBytes.HonestTrace.theTrace Zq.p.X i x)⟩ := by
  show (VerifiableInference.OnPublicFiles.Flat.indexOf M).bind (fun i => fullIn.trace Zq i ξ) = _
  rw [hi]
  exact fullIn_trace_served hx hs

/-- The filling at the library's types. -/
def fillZ (Z : VerifierAndGoals.PublicFiles) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    OnlineProverParts FullSizeMatrix (protocolAtFiles Z).EncodingRandomness Cells Unit Unit :=
  OnlineProverParts.through id (tableCoins Z) matrixInput.dummy (widerFillAtC matrixInput o' S O)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **onlineProverFromPublicFiles returns at any filling over the matrices, read through the maps.** CONDITIONAL: h, hl,
hB, and what the maker asks of that filling. -/
theorem atPure_returns_of_asks (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (P : OnlineProverParts FullSizeMatrix IndexCommitterCoins Cells Unit Unit)
    (asks : ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks P Zp G (P5J.F0T OnBytes.secondHashFunction Zp Np cF))
    (range : P.inRange matrixInput.dummy = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (OnlineProverParts.through id (tableCoins Z) matrixInput.dummy P) = .ok A ∧
      A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G :=
  atPure_returns_fill h hl hB _ fun G hG =>
    makerAsks_through id (tableCoins Z) matrixInput.dummy (asks G hG) range

/-- **onlineProverFromPublicFiles returns at the filling at the library's types.** CONDITIONAL: h, hl, hB. -/
theorem atPure_returns_through (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole P2Law.ProofPlan.WP Johnson.G.proofSendsFull.1
      Johnson.G.proofSendsFull.2.1 Johnson.G.proofSendsFull.2.2
      (mergesByName P2Law.ProofPlan.WP.first.blocksInOrder) = .ok B)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (fillZ Z o' S O) = .ok A ∧ A.Z = Zp ∧
      A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G :=
  atPure_returns_of_asks h hl hB _ (makerAsks_widerC_at h hl hB matrixInput o' S O range_matrixInput) range_matrixInput

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.range_matrixInput
#print axioms ProofFile.Honest.Term.matrixInput_trace_served
#print axioms ProofFile.Honest.Term.atPure_returns_of_asks
#print axioms ProofFile.Honest.Term.atPure_returns_through
