-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K1/HeadAtReturn.lean: at a return of the maker onlineProverFromPublicFiles, where the public files are in
scope and the library's test on them says yes, the head of the counted statements stands at that
return's public part, and the return is the description that the public part makes.

  head_at_return         at the base filling onlineProverPartsInUse, any index type
  head_at_online_return  at T1's onlineMaker, with the online prover at that return
  headAtReturn_base, headAtReturn_online   the same as a value of HeadAtReturn

By what. The head: P5J.head_exists_at_name, P5J.owed_of_live. The return: IOP's
atPure_returns_fillW_at and atPure_returns_term, and that onlineProverFromPublicFiles is a function. The chain:
ToldDesc.pureChainAt_of_open. The places: LaidAt.places.

Limits.
- Nothing is said of what the returned prover plays.
- Nothing on completeness, soundness or hiding.
-/
import AtFullSide.Honest.HonestProverLaws
import Johnson.P5J.HeadExistsAtName
import Johnson.Goal.Skeleton.OwedOfLive
import Johnson.ToldDescR.PureChainOfOpen
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1
open P5J (AtMgA F0T TS)
open VerifiableInference.Desc (Chain)
open VerifierAndGoals (asDescriptionFiles InScope)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- Where the maker returns, the filling's named member is in range. -/
theorem range_of_atPure {W₀ Rc Tr X₀ X : Type} {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (h : onlineProverFromPublicFiles o pol lay KL P = .ok A) :
    P.inRange P.dummy = true := by
  unfold onlineProverFromPublicFiles at h
  obtain ⟨Z, -, h⟩ := bind_ok h
  obtain ⟨G, -, h⟩ := bind_ok h
  obtain ⟨F, -, h⟩ := bind_ok h
  obtain ⟨cs, -, h⟩ := bind_ok h
  split at h
  · obtain ⟨B, -, h⟩ := bind_ok h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i hr
        simpa using hr
  · cases h

/-- **THE HEAD AT A RETURN OF THE MAKER**, at the base filling, from the public files. -/
theorem head_at_return {W₀ : Type} (Z : VerifierAndGoals.PublicFiles) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
      (_ : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) A.Z Np cF x),
      A.F = F0T OnBytes.secondHashFunction A.Z Np cF ∧ ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G ∧
        H2U.placesOfMade A.Z.made = .ok Np ∧ ProofFile.onlineFirstChainAt A.Z = .ok cF := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  have range : I.inRange I.dummy = true := range_of_atPure hA
  obtain ⟨A', hA', eZ, eF, eG⟩ :=
    AtFullSide.K12.atPure_returns_fillW_at h live I OnBytes.secondHashFunction S O range
  obtain rfl : A' = A := by
    have e := hA'.symm.trans hA
    exact Except.ok.inj e
  subst eZ
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  exact ⟨Np, cF, x, h, eF, eG, h.laid.places, ToldDesc.pureChainAt_of_open Op⟩

/-- **HeadAtReturn at the base filling.** -/
theorem headAtReturn_base {W₀ : Type} (Z : VerifierAndGoals.PublicFiles) (I : WiderIn W₀)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S O) = .ok A) :
    ∃ H : ProofFile.Honest.FirstThread.HeadAtReturn Z A, A.F = H.description ∧
      ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G ∧
      H2U.placesOfMade A.Z.made = .ok H.places ∧ ProofFile.onlineFirstChainAt A.Z = .ok H.firstChain := by
  obtain ⟨Np, cF, x, h, eF, eG, hN, hc⟩ := head_at_return Z I S O scope live hA
  exact ⟨⟨⟨_, hA⟩, Np, cF, x, h⟩, eF, eG, hN, hc⟩

end ProofFile.Honest.K1

namespace AtPublicFiles.AtFiles.HonestTerm
open P5J (AtMgA F0T TS)
open VerifiableInference.Desc (Chain)
open ProofFile.Honest.Term (OnlineReturn onlineMaker)
open VerifierAndGoals (asDescriptionFiles InScope)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- **THE HEAD AT A RETURN OF T1's MAKER; THE ONLINE PROVER IS THE ONE AT THAT RETURN.** This gives
T1's ReturnIsTheDescription in scope. -/
theorem head_at_online_return (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    ∃ (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl) (x : VerifiableInference.Desc.First.Look.Place)
      (_ : AtMgA OnBytes.secondHashFunction Z (dpZ Z) (theProofRun (asDescriptionFiles Z)) A.Z Np cF x),
      A.F = AtPublicFiles.AtFiles.descZ A.Z Np cF ∧ ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G ∧
        H2U.placesOfMade A.Z.made = .ok Np ∧ ProofFile.onlineFirstChainAt A.Z = .ok cF ∧
        onlineProver Z = onlineProverAt A Np cF := by
  obtain ⟨pp, read⟩ := LPFPol.read_of_scope scope
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name Z scope read live (P5J.owed_of_live live)
  obtain ⟨A', hA', eZ, eF, eG⟩ :=
    AtFullSide.K12.atPure_returns_term h live OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
      ProofFile.Honest.openHonest
  obtain rfl : A' = A := by
    have e : (Except.ok A' : Except String (OnlineReturn Z)) = .ok A := hA'.symm.trans hA
    exact Except.ok.inj e
  subst eZ
  obtain ⟨Bs, base, Op⟩ := h.laid.opened
  have hN := h.laid.places
  have hc := ToldDesc.pureChainAt_of_open Op
  refine ⟨Np, cF, x, h, eF, eG, hN, hc, ?_⟩
  exact onlineProver_eq hA hN hc

/-- **HeadAtReturn at T1's maker.** -/
theorem headAtReturn_online (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {A : OnlineReturn Z} (hA : onlineMaker Z = .ok A) :
    ∃ H : ProofFile.Honest.FirstThread.HeadAtReturn Z A, A.F = H.description ∧
      ProofFile.blankBy ProofFile.pureRoad.links A.Z = some A.G ∧
      H2U.placesOfMade A.Z.made = .ok H.places ∧ ProofFile.onlineFirstChainAt A.Z = .ok H.firstChain ∧
      onlineProver Z = onlineProverAt A H.places H.firstChain := by
  obtain ⟨Np, cF, x, h, eF, eG, hN, hc, eP⟩ := head_at_online_return Z scope live hA
  exact ⟨⟨⟨_, hA⟩, Np, cF, x, h⟩, eF, eG, hN, hc, eP⟩

/-- **T1's proposition ReturnIsTheDescription, written out**, so that this file reads no issue of its
text. -/
theorem returnIsTheDescription_in_scope (Z : VerifierAndGoals.PublicFiles) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) :
    ∀ A : OnlineReturn Z, onlineMaker Z = .ok A →
      ∃ (Np : H2U.Places4) (cF : Chain TS ProofFile.Cl), H2U.placesOfMade A.Z.made = .ok Np ∧
        ProofFile.onlineFirstChainAt A.Z = .ok cF ∧ A.F = AtPublicFiles.AtFiles.descZ A.Z Np cF := by
  intro A hA
  obtain ⟨Np, cF, -, -, eF, -, hN, hc, -⟩ := head_at_online_return Z scope live hA
  exact ⟨Np, cF, hN, hc, eF⟩

end AtPublicFiles.AtFiles.HonestTerm

#print axioms ProofFile.Honest.K1.range_of_atPure
#print axioms ProofFile.Honest.K1.head_at_return
#print axioms ProofFile.Honest.K1.headAtReturn_base
#print axioms AtPublicFiles.AtFiles.HonestTerm.head_at_online_return
#print axioms AtPublicFiles.AtFiles.HonestTerm.headAtReturn_online
#print axioms AtPublicFiles.AtFiles.HonestTerm.returnIsTheDescription_in_scope
