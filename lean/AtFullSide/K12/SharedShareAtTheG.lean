-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: K12's share of the shared chain at the G of the base filling.
/-
AtFullSide/K12/SharedShareAtTheG.lean: CONDITIONAL: A CONDITIONAL WITH NO KNOWN MEMBER.

What is here. `k12_onAt₂_at_relation` (AtFullSide/K12/SharedShareAtRelation.lean) at G := theGAtBase h T K
(E2E/TheG.lean): hP is paid by `theGAtBase_prover`, and hrows from two premises on K alone.

  `k12_hrows_at_theG`   every list of the kind K12 in G.shared takes its four fields from a row of the lot at G_u or at
      G_omega, where K's shared rows of that kind are these (hK₁) and K holds a row at each half of that kind (hK₂).
  `k12_onAt₂_at_theG`   the statement.

The premises. hK₁, hK₂: on K. Index privacy's kOurs lays sharedOurs := baseRows ++ the lot's rows at G_u ++ rowsAtOmega,
by its letter: at that K they are its to pay. T, K: letters: `ThreadParts` and the K of record have no value here.

Limits. All of the files beneath. At the base, not T1's prover; T3's law crosses (Johnson/T3/OnlineThru.lean). No
property is claimed.
-/
import AtFullSide.K12.SharedShareAtRelation
import E2E.TheG

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
open ProofFile.Honest.Term (matrixInput tableCoins baseFilling baseMaker theGAtBase theGAtBase_prover)
open AtPublicFiles.AtFiles AtPublicFiles.Committed AtPublicFiles.TheSides AtPublicFiles.TheG AtPublicFiles.Bridge AtPublicFiles.Along
open FlashProve
open LPFD.Full (XF instanceAsPlainRecord)

attribute [local irreducible] theKeyData theProofData protocolDataWellFormed theDeadPlan theKeyGate
  theProofGate theLinkGate theProvers theNamed LPFD.Full.GF LPFD.Full.mOneAt PV.EncId.encF
  PV.MFull.cfgF OnBytes.K.Arm.Pub.pub8 FlashProve.thePlan FlashProve.theItem riDigits fieldRows

local instance (priority := high) padAtTheG : Nonempty PadZ :=
  pads_nonempty OnBytes.Slice.frS 402653181

variable {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- CONDITIONAL on hK₁ and hK₂. **hrows at G.** -/
theorem k12_hrows_at_theG (h : HeadAtReturn files A) (T : ThreadParts A Wt)
    (K : KindRows (baseFilling files) A.Z A.G)
    (hK₁ : ∀ r ∈ K.shared, r.place.kind = KindName.K12 →
      r ∈ (lotU Face.shared matrixInput.weights
          (fun Zq w => Bind.ForProver.encW Zq (matrixInput.weights Zq w))).rows A.Z A.G ∨
        r ∈ (lotAtOmega matrixInput.weights).rows A.Z A.G)
    (hK₂ : ∀ g ∈ (baseFilling files).shared A.Z A.G, g.place.kind = KindName.K12 →
      ∃ r ∈ K.shared, r.place = g.place) :
    ∀ L ∈ (theGAtBase h T K).shared, L.place.kind = KindName.K12 → K12RowAt A.Z A.G L := by
  intro L hL hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hL
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hr
  have hk' : (overlayRow K.shared g).place.kind = KindName.K12 := hk
  cases e : K.shared.find? (fun r => r.place == g.place) with
  | none =>
    exfalso
    have eb : overlayRow K.shared g = bareUnlettered g := by
      unfold overlayRow
      rw [e]
    rw [eb] at hk'
    obtain ⟨r₀, hr₀, ep⟩ := hK₂ g hg hk'
    have := List.find?_eq_none.1 e r₀ hr₀
    simp [ep] at this
  | some r₀ =>
    have er : overlayRow K.shared g = r₀ := by
      unfold overlayRow
      rw [e]
    rw [er] at hk' ⊢
    exact ⟨r₀, hK₁ r₀ (List.mem_of_find?_eq_some e) hk', rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- CONDITIONAL: see the head. **K12's SHARE OF on₂ AT G, IN THE SOCKET's OWN FORM.** -/
theorem k12_onAt₂_at_theG (h : HeadAtReturn files A) (made : baseMaker files = .ok A)
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
      ∀ k R (_ : ready h.description A.B A.H w₀ rc x k = .ok R)
        (Tp : ThreadsP h.description A.B A.H w₀ rc x k R) (ρ : Draws) (r : RunC h.description),
        ρ.due h.description = true → runC h.description A.B A.H w₀ rc x k ρ = .ok r →
        ∀ L ∈ (theGAtBase h T K).shared, L.place.kind = KindName.K12 →
          OnAtRunAt₂ (theGAtBase h T K) A.H w₀ rc x k Tp.I₂ ρ r L :=
  k12_onAt₂_at_relation h.head OnBytes.HonestTrace.Sz.ref openHonest made h.description rfl
    (theGAtBase_prover made h T K) A.G (k12_hrows_at_theG h T K hK₁ hK₂) Ry

end AtFullSide.K12

#print axioms AtFullSide.K12.k12_hrows_at_theG
#print axioms AtFullSide.K12.k12_onAt₂_at_theG
