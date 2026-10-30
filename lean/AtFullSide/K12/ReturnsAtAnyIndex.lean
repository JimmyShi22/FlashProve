-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/ReturnsAtAnyIndex.lean: the maker onlineProverFromPublicFiles returns at the filling with every proximity
test laid (onlineProverPartsInUse, K1/Law/WSideAtFill.lean), at any index type whose named member is in
range; and so at that filling at the matrices, read through the coins' map: the filling of the
honest prover.

  makerAsks_fillW_at       what onlineProverFromPublicFiles asks of the filling holds, at any I
  atPure_returns_fillW_at  onlineProverFromPublicFiles returns there; the book's return is paid
  atPure_returns_term      onlineProverFromPublicFiles returns at the filling at matrixInput read through tableCoins
  second_ne_nil_term       the prover that it returns holds the last chain's pair

By what. makerAsks_widerC_at (Honest/ThruMade.lean) in the place of makerAsks_widerC_fullIn; the
rest is the proof of makerAsks_fillW (ReturnsAtFillW.lean), which reads the index through I alone.

Limits.
- Conditional on the library's head and its test on the public files.
- That onlineProverFromPublicFiles returns says nothing of what its prover plays.
- ready is not treated here.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.SecondMadeW
import AtFullSide.Honest.TermMade

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Block Chain Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K5
open P2Law.ProofPlan (WP)
open Johnson.G (proofSendsFull)
open P5J (AtMgA TS)
open ProofFile (Pub Ground SecondHashFunctionArgument blankBy pureRoad)
open VerifiableInference.Desc (alike₂_place)
open ProofFile.Honest.Term (matrixInput tableCoins range_matrixInput makerAsks_through makerAsks_widerC_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **What the maker asks, at the filling, at any index type.** CONDITIONAL: h, hl, hB. -/
theorem makerAsks_fillW_at {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (hB : ∃ B, bookWhole WP proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName WP.first.blocksInOrder) = .ok B)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (range : I.inRange I.dummy = true) :
    ∀ G, blankBy pureRoad.links Zp = some G →
      MakerAsks (onlineProverPartsInUse I o' S O) Zp G
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) := by
  intro G hG
  have a := makerAsks_widerC_at h hl hB I o' S O range G hG
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have pa := ProofFile.Honest.K14.planAlike_at_head h
  obtain ⟨p1, p2, p3, p4⟩ := written_places_all
  have e1 := alike₂_place _ _ pa.first
  have e2 := alike₂_place _ _ pa.shared
  have e3 := alike₂_place _ _ pa.second
  rw [e1] at p1
  rw [e2] at p2 p3
  rw [e3] at p4
  refine ⟨(strays_firstOf_iff _ Zp G _).2 fun M hM => ?_, ?_, ?_, a.range⟩
  · rw [widerFillAtCPUOWM_lots] at hM
    simp only [List.mem_append, List.mem_singleton] at hM
    rcases hM with ((h1 | rfl) | rfl) | rfl
    · exact (strays_firstOf_iff _ Zp G _).1 a.first M
        (List.mem_append_left _ h1)
    · exact (strays_firstOf_iff _ Zp G _).1 a.first _
        (List.mem_append_right _ (List.mem_singleton.2 rfl))
    · exact proxLotAt_clean I S G Op
    · refine K10.strays_nil fun y hy => ?_
      rw [wHalf_place I o' O Zp G y hy]
      exact p1
  · show strays _ (sharedWithUO I Zp) = []
    cases hs : nowSharedBy (I.weights Zp) Zp with
    | error e =>
      rw [sharedWithUO_error I hs]
      rfl
    | ok six =>
      have h6 := a.shared
      have hv : (widerFillAtC I o' S O).shared Zp G = six := by
        show (nowSharedBy (I.weights Zp) Zp).toOption.getD [] = six
        rw [hs]
        rfl
      rw [hv] at h6
      rw [sharedWithUO_ok I hs, sharedWithU_ok I hs, strays_append, strays_append, h6]
      have hu : strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
          (halfU (I.weights Zp)
            (fun w => Bind.ForProver.encW Zp (I.weights Zp w)) Zp) = [] :=
        K10.strays_nil fun y hy => by
          rw [halfU_place _ _ Zp y hy]
          exact p2
      have ho : strays (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder
          (halfO (I.weights Zp) Zp) = [] :=
        K10.strays_nil fun y hy => by
          rw [halfO_place _ Zp y hy]
          exact p3
      rw [hu, ho]
      rfl
  · show strays _ (secondW I o' S O Zp G) = []
    refine K10.strays_nil fun y hy => ?_
    unfold secondW at hy
    split at hy
    · rw [halfW_place _ _ _ _ _ _ _ _ Zp G y hy]
      exact p4
    · cases hy

/-- **onlineProverFromPublicFiles returns at the filling, at any index type.** CONDITIONAL: h, hl. -/
theorem atPure_returns_fillW_at {W₀ : Type} (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (I : WiderIn W₀) (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (range : I.inRange I.dummy = true) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I o' S O) = .ok A ∧
      A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G := by
  obtain ⟨B, hB, -⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  exact atPure_returns_fill h hl ⟨B, hB⟩ _ (makerAsks_fillW_at h hl ⟨B, hB⟩ I o' S O range)

/-- **onlineProverFromPublicFiles returns at the filling at the matrices, read through the coins' map.** CONDITIONAL:
h, hl. -/
theorem atPure_returns_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (o' : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
        (OnlineProverParts.through id (tableCoins Z) matrixInput.dummy (onlineProverPartsInUse matrixInput o' S O)) = .ok A ∧
      A.Z = Zp ∧ A.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧ blankBy pureRoad.links Zp = some A.G := by
  obtain ⟨B, hB, -⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  exact atPure_returns_fill h hl ⟨B, hB⟩ _ fun G hG =>
    makerAsks_through id (tableCoins Z) matrixInput.dummy
      (makerAsks_fillW_at h hl ⟨B, hB⟩ matrixInput o' S O range_matrixInput G hG) range_matrixInput

/-- **The prover at that filling holds the last chain's pair.** CONDITIONAL: h, hl. -/
theorem second_ne_nil_term (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hl : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    ∃ A, onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL
        (OnlineProverParts.through id (tableCoins Z) matrixInput.dummy (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction S O)) = .ok A ∧
      A.H.second ≠ [] := by
  obtain ⟨A, hA, eZ, -, -⟩ := atPure_returns_term h hl OnBytes.secondHashFunction S O
  obtain ⟨Bs', base', Op⟩ := h.laid.opened
  obtain ⟨-, -, -, -, -, -, -, -, -, h2, -⟩ := atPure_ok hA
  refine ⟨A, hA, ?_⟩
  rw [h2, eZ]
  obtain ⟨J, -, hJ⟩ := second_made h Op matrixInput S O A.G
  show (secondW matrixInput OnBytes.secondHashFunction S O Zp A.G).map
    (Placed.thru (Local.thru id (tableCoins Z)) (Local.thru id (tableCoins Z))) ≠ []
  rw [hJ]
  exact List.cons_ne_nil _ _

end AtFullSide.K12

#print axioms AtFullSide.K12.makerAsks_fillW_at
#print axioms AtFullSide.K12.atPure_returns_fillW_at
#print axioms AtFullSide.K12.atPure_returns_term
#print axioms AtFullSide.K12.second_ne_nil_term
