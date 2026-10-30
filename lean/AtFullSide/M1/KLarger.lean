-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our kinds' clauses at any K that holds our rows.
/-
AtFullSide/M1/KLarger.lean: at any value of `KindRows` at the base filling whose lots hold ours and whose
shared rows hold the six, `theG` pays at K1, K10, K14: so what `kOurs` shows carries to a larger K,
if it holds these lots and these six rows; no other premise on K. No property of the protocol is claimed here.
-/
import AtFullSide.M1.KOurs

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

variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- A row of the slots has the side that it stands for as its half. -/
theorem slot_row_half {V W Y Pb : Type} {hs : List (Placed V W Y)} {rs : List (Unlettered V W Y Pb)}
    (hm : ∀ h ∈ hs, ∀ r, (rs.find? fun r => r.place == h.place) = some r → r.half = h) :
    ∀ r ∈ hs.map (overlayRow rs), r.half ∈ hs := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  rw [overlayRow_half (hm x hx)]
  exact hx

/-- **A shared row of a kind other than K12 is one of the six**, at a K that holds the six. -/
theorem rows_of_K (hd : HeadAtReturn files A₀) (K : KindRows baseFill A₀.Z A₀.G)
    (hsix : ∀ r ∈ baseRows A₀.Z hd.places, r ∈ K.shared) (κ : KindName) (hκ : κ ≠ KindName.K12) :
    ∀ r ∈ K.slots.shared, r.place.kind = κ → r ∈ baseRows A₀.Z hd.places := by
  intro r hr hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  have hhalf : (overlayRow K.shared x).half = x := overlayRow_half (K.shared_fit x hx)
  have hp : x.place.kind = κ := (congrArg (fun y => y.place.kind) hhalf).symm.trans hk
  have hx' : x ∈ (sharedOurs A₀.Z hd.places A₀.G).map (·.half) := by
    rw [shared_fit hd.head]
    exact hx
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hx'
  rcases List.mem_append.1 hr₀ with h1 | h1
  · have hf : (K.shared.find? fun y => y.place == r₀.half.place) = some r₀ :=
      OnBytes.SendSim.Seat.find_of_nodup (fun y : Unlettered _ _ _ _ => y.place) K.shared
        K.shared_apart r₀ (hsix r₀ h1)
    have e : overlayRow K.shared r₀.half = r₀ := by
      unfold overlayRow
      rw [hf]
    rw [e]
    exact h1
  · exact absurd (hp.symm.trans (rest_k12 A₀.Z A₀.G r₀ h1)) hκ

/-- **A last row of any K is of the kind K12.** -/
theorem second_of_K (K : KindRows baseFill A₀.Z A₀.G) :
    ∀ r ∈ K.slots.second, r.place.kind = KindName.K12 := by
  intro r hr
  have h1 : r.half ∈ baseFill.second A₀.Z A₀.G := slot_row_half K.second_fit r hr
  have h2 : r.half ∈ (secondOurs A₀.Z A₀.G).map (·.half) := by
    rw [second_fit]
    exact h1
  obtain ⟨r₀, hr₀, e⟩ := List.mem_map.1 h2
  have h3 := second_k12 A₀.Z A₀.G r₀ hr₀
  have h4 : r₀.place = r.place := congrArg Placed.place e
  rw [← h4]
  exact h3

/-- **The clauses at any K that holds ours.** -/
theorem theG_pays_of_holds (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (h₁ : k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id ∈ K.lots)
    (h₂ : wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id ∈ K.lots)
    (h₃ : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
    (hsix : ∀ r ∈ baseRows A₀.Z hd.places, r ∈ K.shared) :
    VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K14 :=
  ⟨kindPays_K1_theG hd hS hL made T K
      (OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) K.lots K.apart _ h₁)
      (OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) K.lots K.apart _ h₂)
      (rows_of_K hd K hsix KindName.K1 (by decide)),
    kindPays_K10_theG hd hS hL made T K h₃,
    kindPays_K14_theG hd hS hL made T K (rows_of_K hd K hsix KindName.K14 (by decide))
      (fun r hr hk => by
        have h2 := second_of_K K r hr
        rw [hk] at h2
        cases h2)⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.theG_pays_of_holds
