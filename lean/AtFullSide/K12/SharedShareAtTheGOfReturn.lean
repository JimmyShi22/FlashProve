-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: K12's share of the shared chain at the G of T3's one theorem.
/-
AtFullSide/K12/SharedShareAtTheGOfReturn.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

What is here. K12's shares at the shared chain at G := theGOfReturn made h T K (E2E/TheG.lean), the G of
Johnson/T3/TheOneAtTheG.lean, in the prefix of `KindOnAtEveryRun` at every family of `ThreadsP`, and `KindBud`'s second clause.
From two premises on K alone; `castSides_of` along `atPure_at_laid`'s second clause. The relation is written out:
imageRel id (tableCoins files) (relAt … Ry instanceAsPlainRecord), at any Ry.

  `k12_hrows_at_theGOfReturn`, `k12_on₂_at_theGOfReturn`, `k12_bud₂_at_theGOfReturn`.

Limits. All of the files beneath: at the base filling; T3's law crosses. The row must stand in G with a side for the
share to say anything. No property is claimed.
-/
import AtFullSide.K12.SharedShareAtTheG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace AtFullSide.K12
open OnBytes (TableKey)
open VerifiableInference.Desc (KindName)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Light ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Sim2
open ProofFile.Honest.FirstThread (HeadAtReturn)
open ProofFile.Honest.Term (matrixInput tableCoins baseFilling baseMaker theGAtBase)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.TheSides AtPublicFiles.TheG AtPublicFiles.Bridge AtPublicFiles.Along
open FlashProve
open LPFD.Full (XF instanceAsPlainRecord)

attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

local instance (priority := high) padAtTheGOfReturn : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- CONDITIONAL on hK₁ and hK₂. **hrows at the G of the return.** -/
theorem k12_hrows_at_theGOfReturn (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK₁ : ∀ r ∈ K.shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G)
    (hK₂ : ∀ g ∈ (baseFilling files).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.shared, r.place = g.place) :
    ∀ L ∈ (theGOfReturn made h T K).shared, L.place.kind = KindName.K12 → K12RowAt A.Z A.G L :=
  castSides_of (atPure_at_laid h.head.laid made).2
    (Q := fun _ G => ∀ L ∈ G.shared, L.place.kind = KindName.K12 → K12RowAt A.Z A.G L)
    (k12_hrows_at_theG h T K hK₁ hK₂)

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **K12's SHARE OF on₂ AT THE G OF THE RETURN, AT EVERY VALUE OF `ThreadsP`.** -/
theorem k12_on₂_at_theGOfReturn (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK₁ : ∀ r ∈ K.shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G)
    (hK₂ : ∀ g ∈ (baseFilling files).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.shared, r.place = g.place)
    (Ry : FullSizeMatrix → XF → Prop) :
    ∀ w₀ rc x, (∃ w rc', ProofFile.Honest.relAt (ansAt (AZ files) PadZ (holdZ files)) Ry instanceAsPlainRecord w rc' x ∧
        id w = w₀ ∧ tableCoins files rc' = rc) →
      ∀ k R (_ : ready A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k = .ok R)
        (Tp : ThreadsP A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k R) (ρ : Draws)
        (r : RunC A.F), ρ.due A.F = true →
        runC A.F A.B ((theGOfReturn made h T K).prover A.H) w₀ rc x k ρ = .ok r →
        ∀ L ∈ (theGOfReturn made h T K).shared, L.place.kind = KindName.K12 →
          OnAtRun₂ (G := theGOfReturn made h T K) (H := A.H) Tp ρ r L :=
  k12_on₂_at_relation h.head OnBytes.HonestTrace.Sz.ref openHonest made A.F
    (atPure_at_laid h.head.laid made).2 (theGOfReturn_prover made h T K) A.G
    (k12_hrows_at_theGOfReturn made h T K hK₁ hK₂) Ry

/-- CONDITIONAL on hK₁ and hK₂. **K12's SHARE OF bud₂ AT THE G OF THE RETURN**: `KindBud`'s second clause. -/
theorem k12_bud₂_at_theGOfReturn (made : baseMaker files = .ok A) (h : HeadAtReturn files A)
    (T : ThreadParts A Wt) (K : KindRows (baseFilling files) A.Z A.G)
    (hK₁ : ∀ r ∈ K.shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G)
    (hK₂ : ∀ g ∈ (baseFilling files).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.shared, r.place = g.place) :
    ∀ L ∈ (theGOfReturn made h T K).shared, L.place.kind = KindName.K12 →
      Johnson.M1.BudOwed₂ A.F L :=
  castSides_of (atPure_at_laid h.head.laid made).2
    (Q := fun F₀ G => ∀ L ∈ G.shared, L.place.kind = KindName.K12 → Johnson.M1.BudOwed₂ F₀ L)
    (k12_bud₂_at_base h.head.toAtMg A.G (k12_hrows_at_theG h T K hK₁ hK₂))

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_hrows_at_theGOfReturn
#print axioms AtFullSide.K12.k12_on₂_at_theGOfReturn
#print axioms AtFullSide.K12.k12_bud₂_at_theGOfReturn
