-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our rows of the later chains in the K of record.
/-
AtFullSide/M1/KRecord.lean: `laterOurs`, a value of `LaterRows` (E2E/TheKOfRecord.lean) at our shared and
last rows, and the clauses at `theK E apart laterOurs` for any thirteen entries whose fields k1, w, k10 are
K1's own lot, W's and the closings'. No other field of E is read here. No property of the protocol is
claimed here.
-/
import AtFullSide.M1.KLarger
import E2E.TheKOfRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open Johnson.M1 (k1Lot wLot)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)

/-- **The later rows, ours.** -/
noncomputable def laterOurs {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit)
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀) : LaterRows baseFill A₀.Z A₀.G where
  shared := sharedOurs A₀.Z Np A₀.G
  shared_named := named_of_map (shared_fit h _)
  shared_apart := shared_apart h _
  shared_fit := fit_of_map (shared_fit h _) (shared_apart h _)
  second := secondOurs A₀.Z A₀.G
  second_named := named_of_map (second_fit _ _)
  second_apart := apart_of_short (rowsW_short _ _)
  second_fit := fit_of_map (second_fit _ _) (apart_of_short (rowsW_short _ _))

variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **The clauses at the K of record.** -/
theorem theK_pays (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (E : TheThirteen baseFill A₀.Z A₀.G)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (h₁ : E.k1.slot = k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id)
    (h₂ : E.w.slot = wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)
    (h₃ : E.k10.slot = closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head)))
        KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head)))
        KindName.K14 :=
  theG_pays_of_holds hd hS hL made T _
    (h₁ ▸ mem_theK (e := E.k1) (by simp [TheThirteen.entries]) apart _)
    (h₂ ▸ mem_theK (e := E.w) (by simp [TheThirteen.entries]) apart _)
    (h₃ ▸ mem_theK (e := E.k10) (by simp [TheThirteen.entries]) apart _)
    (fun _ hr => List.mem_append_left _ hr)

/-- **The same at the description that the return holds.** -/
theorem theK_pays_ofReturn (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (E : TheThirteen baseFill A₀.Z A₀.G)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (h₁ : E.k1.slot = k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id)
    (h₂ : E.w.slot = wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)
    (h₃ : E.k10.slot = closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K14 := by
  obtain ⟨a, b, c⟩ := theK_pays hd hS hL made T E apart h₁ h₂ h₃
  exact ⟨castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K1) _ a,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K10) _ b,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K14) _ c⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.laterOurs
#print axioms AtFullSide.M1.theK_pays
#print axioms AtFullSide.M1.theK_pays_ofReturn
