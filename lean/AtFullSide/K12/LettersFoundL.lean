-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/LettersFoundL.lean: the side at the first chain's proximity test, at the prover that
onlineProverFromPublicFiles returns at the filling onlineProverPartsInUse, at any index type, under the library's head: the
search at the test's place finds the pair of jobL at the filling's own letters.

  lots_at_L   every lot of the filling has no half at the test's place, or the test's own list
  L_found     the search finds proverSideOfProximityTest of jobL, at the finish

By what. eleven_not_K12_plain (AtPureWiderK12Kinds.lean), closeLotAt_kinds, wLot_place, fitsL_head_L
(FitsAtHeadL.lean), proxLotAt_made, halves_lotAtDoor, atPure_first_find.

Limits.
- At the filling before it is read through.
- Nothing on what the pair plays. Nothing on completeness, soundness or hiding.
-/
import AtFullSide.K12.LettersAtHead
import Johnson.Desc.ProofFile.Honest.AtPureWiderK12Kinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open VerifiableInference.Desc (Chain KindName Place)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open ProofFile (Ground SecondHashFunctionArgument Pub)
open P5J (AtMgA TS)

variable {W₀ : Type}

/-- **Every lot of the filling has no half at the test's place, or the test's own list.** -/
theorem lots_at_L (I : WiderIn W₀) (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    (Z : Pub) (G : Ground) :
    ∀ M ∈ (onlineProverPartsInUse I o S O).lots,
      (∀ g ∈ M.halves Z G, g.place ≠ placeL) ∨
      M.halves Z G = (proxLotAt (X := Unit) I S).halves Z G := by
  intro M hM
  rw [widerFillAtCPUOWM_lots] at hM
  simp only [List.mem_append, List.mem_singleton] at hM
  rcases hM with ((h | rfl) | rfl) | rfl
  · refine .inl fun g hg e => ?_
    have h' : M ∈ (widerFillAtC I o S O).lots := List.mem_append_left _ h
    exact eleven_not_K12_plain I o S O Z G M h' g hg (congrArg (fun a : Place => a.kind) e)
  · refine .inl fun g hg e => ?_
    have hk := closeLotAt_kinds I S Z G g hg
    have hk' : KindName.K12 = KindName.K10 := (congrArg (fun a : Place => a.kind) e).symm.trans hk
    cases hk'
  · exact .inr rfl
  · refine .inl fun g hg e => ?_
    have hk := congrArg (fun a : Place => a.kind) ((wLot_place I o O Z G g hg).symm.trans e)
    have hk' : KindName.K1 = KindName.K12 := hk
    cases hk'

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The search at the test's place finds the pair of jobL, at the finish.** -/
theorem L_found (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ pl, finishAt Zp A.G = some pl ∧
      A.H.first.find? (fun g => g.place == placeL) =
        some (proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) (widerRows S Zp A.G)
                           (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
                           (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) pl)) := by
  have eZ := (atPure_at_laid h.laid hA).1
  have hG : ProofFile.blankBy ProofFile.pureRoad.links Zp = some A.G := by
    have k := (atPure_ok hA).2.1
    rwa [eZ] at k
  obtain ⟨pl, hf, hfit⟩ := fitsL_head_L h.toAtMg hG
  have e₁ := proxLotAt_made (X := Unit) I S A.G h.laid.chain
  have e₂ : (proxLotOf (X := Unit) I S).halves Zp A.G =
      [proverSideOfProximityTest (jobL (H2U.p12OfMade Zp.made) (doorAtL Zp) (widerRows S Zp A.G)
                         (fun w : Local W₀ IndexCommitterCoins ProofFile.Inst Cells => ⟨w.trace, I.weights Zp w.w₀, w.rc⟩)
                         (K2.lotClosingAt A.G.first.layout (K2.segmentsOf Zp A.G)) pl)] :=
    halves_lotAtDoor _ _ _ Zp A.G pl hf hfit
  refine ⟨pl, hf, atPure_first_find hA (L := proxLotAt (X := Unit) I S)
    (by rw [widerFillAtCPUOWM_lots]; simp) (lots_at_L I _ S O A.Z A.G) ?_⟩
  rw [eZ, e₁, e₂]
  exact List.find?_cons_of_pos (beq_iff_eq.2 (proxPlace Zp))

end AtFullSide.K12

#print axioms AtFullSide.K12.lots_at_L
#print axioms AtFullSide.K12.L_found
