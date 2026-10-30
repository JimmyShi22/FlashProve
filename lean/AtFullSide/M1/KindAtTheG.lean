-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our kinds' clauses at `theG`.
/-
AtFullSide/M1/KindAtTheG.lean: `theG` (E2E/TheG.lean) stands at the head's description, our clauses at the
return's: the two are equal, so the clauses cross, by substitution. What `K : KindRows` must hold is
named: our lots by name (`hf₁`, `hf₂`, `hc`), and on the shared and last chains that a row of the kind is
one of the six or none (`hsh`, `hse`). No property of the protocol is claimed here.
-/
import AtFullSide.M1.GOurs
import E2E.TheG

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

/-- A clause at every threads and falls, at a description. -/
def KindAtF {Bk : ProverCoinCounts} (R : Rows FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (κ : KindName)
    (F : FileDescription ProofFile.Inst) : Prop :=
  ∀ (T₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread Bk F.S₁ F.Cl
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (T₂ : Common FullSizeMatrix IndexCommitterCoins TableKey → Thread Bk F.S₂ F.Cl Empty
      (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (T₃ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread Bk F.S₃ F.Cl
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (S₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins Bk →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (S₂ : Common FullSizeMatrix IndexCommitterCoins TableKey → Nat → Coins Bk → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (S₃ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins Bk →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (f₁ : List (Fall F.S₁)) (f₂ : List (Fall F.S₂)) (f₃ : List (Fall F.S₃)),
    VerifiableInference.Compilation.KindPays (theSides F (Letters.ofThreads F T₁ T₂ T₃ S₁ S₂ S₃) R f₁ f₂ f₃) κ

/-- **The clause crosses to the equal description.** -/
theorem kindAtF_cross {Bk : ProverCoinCounts} {R : Rows FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit} {κ : KindName}
    {F F' : FileDescription ProofFile.Inst} (e : F = F') (h : KindAtF (Bk := Bk) R κ F) :
    KindAtF (Bk := Bk) R κ F' := e ▸ h

section
variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **`KindPays .K1` at `theG`.** -/
theorem kindPays_K1_theG (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (hf₁ : (K.lots.find? fun s => s.name ==
        (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id).name) =
      some (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id))
    (hf₂ : (K.lots.find? fun s => s.name ==
        (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id).name) =
      some (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id))
    (hsh : ∀ r ∈ K.slots.shared, r.place.kind = KindName.K1 → r ∈ baseRows A₀.Z hd.places) :
    VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K1 := by
  have e := (ProofFile.Honest.atPure_at_laid hd.head.laid made).2
  have H : KindAtF (Bk := A₀.B) K.slots.rows KindName.K1 A₀.F :=
    fun T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ =>
      kindPays_K1_sides hd.head hS hL made K.lots K.named K.apart K.lots_fit hf₁ hf₂ K.slots.shared
        K.slots.shared_fit K.slots.second K.slots.second_fit hsh T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃
  exact kindAtF_cross e H _ _ _ _ _ _ _ _ _

/-- **`KindPays .K10` at `theG`.** -/
theorem kindPays_K10_theG (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (hc : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots) :
    VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K10 := by
  have e := (ProofFile.Honest.atPure_at_laid hd.head.laid made).2
  have H : KindAtF (Bk := A₀.B) K.slots.rows KindName.K10 A₀.F :=
    fun T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ =>
      kindPays_K10_sides hd.head hS hL made K.lots K.named K.apart K.lots_fit hc K.slots.shared
        K.slots.shared_fit K.slots.second K.slots.second_fit T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃
  exact kindAtF_cross e H _ _ _ _ _ _ _ _ _

/-- **`KindPays .K14` at `theG`.** -/
theorem kindPays_K14_theG (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (hsh : ∀ r ∈ K.slots.shared, r.place.kind = KindName.K14 → r ∈ baseRows A₀.Z hd.places)
    (hse : ∀ r ∈ K.slots.second, r.place.kind = KindName.K14 → False) :
    VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K14 := by
  have e := (ProofFile.Honest.atPure_at_laid hd.head.laid made).2
  have H : KindAtF (Bk := A₀.B) K.slots.rows KindName.K14 A₀.F :=
    fun T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ =>
      kindPays_K14_sides hd.head hS hL made K.lots K.named K.apart K.lots_fit K.slots.shared
        K.slots.shared_fit K.slots.second K.slots.second_fit hsh hse T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃
  exact kindAtF_cross e H _ _ _ _ _ _ _ _ _

end

end AtFullSide.M1

#print axioms AtFullSide.M1.kindPays_K1_theG
#print axioms AtFullSide.M1.kindPays_K10_theG
#print axioms AtFullSide.M1.kindPays_K14_theG
