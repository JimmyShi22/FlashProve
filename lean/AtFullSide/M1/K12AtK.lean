-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- the kind K12's clause at any K that holds our rows, and at the K of record.
/-
AtFullSide/M1/K12AtK.lean: what K12Closed.lean shows at `gOurs`, at `theSides` over any `overlaySlots` that holds the test at L's lot and whose later rows of the kind are ours; so at `theG`, at the K of record and at the letters, beside the three of M1's files.

  `k12_rest_of_K`, `second_rows_of_K`   at a K that holds ours: a shared row of the kind is ours; a last row is
  `kindPays_K12_sides`, `kindPays_K12_theG`   the clause
  `theG_pays_four`, `theK_pays_four`, `theK_pays_four_ofReturn`, `letters_theK_four`   **the four kinds**

Limits. As K12Closed.lean's: `Good` at A := False; the base filling, not read through. No property of the protocol is claimed.
-/
import AtFullSide.M1.K12Closed
import AtFullSide.M1.KOursLetters

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open ProofFile.Honest.K12.Sim2
open Johnson.M1 (k1Lot wLot)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides AtPublicFiles.TheG
open ProofFile.Honest.FirstThread (HeadAtReturn)
open OnBytes (TableKey)

/-- **The later rows of the kind K12.** -/
noncomputable def restOurs (Zp : ProofFile.Pub) (G : ProofFile.Ground) :
    List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) :=
  (lotU .shared matrixInput.weights encOf).rows Zp G ++
    ProofFile.Honest.K12.AtProof.rowsAtOmega (matrixInput.weights Zp) Zp

variable {files : VerifierAndGoals.PublicFiles} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} {Wt : Type}

/-- **A shared row of the kind K12 is one of ours**, at a K that holds ours. -/
theorem k12_rest_of_K (hd : HeadAtReturn files A₀) (K : KindRows baseFill A₀.Z A₀.G)
    (hrest : ∀ r ∈ restOurs A₀.Z A₀.G, r ∈ K.shared) :
    ∀ r ∈ K.slots.shared, r.place.kind = KindName.K12 → r ∈ restOurs A₀.Z A₀.G := by
  intro r hr hk
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  have hhalf : (overlayRow K.shared x).half = x := overlayRow_half (K.shared_fit x hx)
  have hp : x.place.kind = KindName.K12 := (congrArg (fun y => y.place.kind) hhalf).symm.trans hk
  have hx' : x ∈ (sharedOurs A₀.Z hd.places A₀.G).map (·.half) := by
    rw [shared_fit hd.head]
    exact hx
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hx'
  rcases List.mem_append.1 hr₀ with h1 | h1
  · exact (six_not_k12 hd.head r₀ h1 hp).elim
  · have hf : (K.shared.find? fun y => y.place == r₀.half.place) = some r₀ :=
      OnBytes.SendSim.Seat.find_of_nodup (fun y : Unlettered _ _ _ _ => y.place) K.shared
        K.shared_apart r₀ (hrest r₀ h1)
    have e : overlayRow K.shared r₀.half = r₀ := by
      unfold overlayRow
      rw [hf]
    rw [e]
    exact h1

/-- **A last row is one of ours**, at a K that holds ours. -/
theorem second_rows_of_K (K : KindRows baseFill A₀.Z A₀.G)
    (hse : ∀ r ∈ secondOurs A₀.Z A₀.G, r ∈ K.second) :
    ∀ r ∈ K.slots.second, r ∈ secondOurs A₀.Z A₀.G := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hr
  have hx' : x ∈ (secondOurs A₀.Z A₀.G).map (·.half) := by
    rw [second_fit]
    exact hx
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hx'
  have hf : (K.second.find? fun y => y.place == r₀.half.place) = some r₀ :=
    OnBytes.SendSim.Seat.find_of_nodup (fun y : Unlettered _ _ _ _ => y.place) K.second
      K.second_apart r₀ (hse r₀ hr₀)
  have e : overlayRow K.second r₀.half = r₀ := by
    unfold overlayRow
    rw [hf]
  rw [e]
  exact hr₀

/-- **`KindPays .K12` at `theSides` over `overlaySlots`**, at any `mine` that holds the test at L's lot. -/
theorem kindPays_K12_sides {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (mine : Lots₀)
    (named : ∀ s ∈ mine, baseFill.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ baseFill.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A₀.Z A₀.G).map (·.half) = L.halves A₀.Z A₀.G)
    (hc : simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ mine)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey))
    (hs : shared.map (·.half) = baseFill.shared A₀.Z A₀.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)) (h₃ : second.map (·.half) = baseFill.second A₀.Z A₀.G)
    (hsh : ∀ r ∈ shared, r.place.kind = KindName.K12 → r ∈ restOurs A₀.Z A₀.G)
    (hse : ∀ r ∈ second, r ∈ secondOurs A₀.Z A₀.G)
    (T₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread A₀.B A₀.F.S₁ A₀.F.Cl
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (T₂ : Common FullSizeMatrix IndexCommitterCoins TableKey → Thread A₀.B A₀.F.S₂ A₀.F.Cl Empty
      (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (T₃ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread A₀.B A₀.F.S₃ A₀.F.Cl
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (S₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins A₀.B →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (S₂ : Common FullSizeMatrix IndexCommitterCoins TableKey → Nat → Coins A₀.B → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (S₃ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins A₀.B →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (f₁ : List (Fall A₀.F.S₁)) (f₂ : List (Fall A₀.F.S₂)) (f₃ : List (Fall A₀.F.S₃)) :
    VerifiableInference.Compilation.KindPays (theSides A₀.F (Letters.ofThreads A₀.F T₁ T₂ T₃ S₁ S₂ S₃)
      (overlaySlots baseFill A₀.Z A₀.G mine named apart hm shared hs second h₃).rows f₁ f₂ f₃)
      KindName.K12 := by
  have hB := ProofFile.Honest.K12.Sim2.noneSpent_at_maker h hA
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  have eF : A₀.F = P5J.F0T OnBytes.secondHashFunction A₀.Z Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  refine ⟨?_, ?_, ?_⟩
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hl
    have hh : r.half ∈ M.halves A₀.Z A₀.G := by
      rw [← overlay_half (hm M hM)]
      exact List.mem_map.2 ⟨r, hrl, rfl⟩
    have e := lots_k12 A₀.Z A₀.G M hM _ hh hk
    subst e
    have ef : (mine.find? fun s => s.name ==
        (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).name) =
        some (simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :=
      OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mine apart _ hc
    have eo : overlayLot mine (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) =
        simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref := by
      unfold overlayLot
      rw [ef]
    rw [eo] at hrl
    exact k12L_row h A₀.F eF A₀.B hB _ _ A₀.G T₁ S₁ f₁ r hrl σ hσ
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    rcases List.mem_append.1 (hsh r hr hk) with h2 | h2
    · exact k12U_row h A₀.F eF A₀.B hB _ _ A₀.G T₂ S₂ f₂ r h2 σ hσ
    · exact k12O_row h A₀.F eF A₀.B hB _ _ T₂ S₂ f₂ r h2 σ hσ
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    exact k12W_row h A₀.F eF A₀.B hB _ _ _ A₀.G T₃ S₃ f₃ r (hse r hr) σ hσ

/-- **`KindPays .K12` at `theG`.** -/
theorem kindPays_K12_theG (hd : HeadAtReturn files A₀)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (hc : simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
    (hrest : ∀ r ∈ restOurs A₀.Z A₀.G, r ∈ K.shared)
    (hse : ∀ r ∈ secondOurs A₀.Z A₀.G, r ∈ K.second) :
    VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K12 := by
  have e := (ProofFile.Honest.atPure_at_laid hd.head.laid made).2
  have H : KindAtF (Bk := A₀.B) K.slots.rows KindName.K12 A₀.F :=
    fun T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ =>
      kindPays_K12_sides hd.head made K.lots K.named K.apart K.lots_fit hc K.slots.shared
        K.slots.shared_fit K.slots.second K.slots.second_fit (k12_rest_of_K hd K hrest)
        (second_rows_of_K K hse) T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃
  exact kindAtF_cross e H _ _ _ _ _ _ _ _ _

/-- **The four kinds at any K that holds ours.** -/
theorem theG_pays_four (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (K : KindRows baseFill A₀.Z A₀.G)
    (h₁ : k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id ∈ K.lots)
    (h₂ : wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id ∈ K.lots)
    (h₃ : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
    (h₄ : simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ K.lots)
    (hsix : ∀ r ∈ baseRows A₀.Z hd.places, r ∈ K.shared)
    (hrest : ∀ r ∈ restOurs A₀.Z A₀.G, r ∈ K.shared)
    (hse : ∀ r ∈ secondOurs A₀.Z A₀.G, r ∈ K.second) :
    VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K14 ∧
      VerifiableInference.Compilation.KindPays (theG hd T K) KindName.K12 := by
  obtain ⟨a, b, c⟩ := theG_pays_of_holds hd hS hL made T K h₁ h₂ h₃ hsix
  exact ⟨a, b, c, kindPays_K12_theG hd made T K h₄ hrest hse⟩

/-- **The four kinds at the K of record.** -/
theorem theK_pays_four (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (E : TheThirteen baseFill A₀.Z A₀.G)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (h₁ : E.k1.slot = k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id)
    (h₂ : E.w.slot = wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)
    (h₃ : E.k10.slot = closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)
    (h₄ : E.k12.slot = simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head)))
        KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head)))
        KindName.K14 ∧
      VerifiableInference.Compilation.KindPays (theG hd T (theK E apart (laterOurs A₀ hd.head)))
        KindName.K12 := by
  obtain ⟨a, b, c⟩ := theK_pays hd hS hL made T E apart h₁ h₂ h₃
  exact ⟨a, b, c, kindPays_K12_theG hd made T _
    (h₄ ▸ mem_theK (e := E.k12) (by simp [TheThirteen.entries]) apart _)
    (fun _ hr => List.mem_append_right _ hr) (fun _ hr => hr)⟩

/-- **The same at the description that the return holds.** -/
theorem theK_pays_four_ofReturn (hd : HeadAtReturn files A₀) (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (T : ThreadParts A₀ Wt) (E : TheThirteen baseFill A₀.Z A₀.G)
    (apart : (E.entries.map (·.slot.name)).Nodup)
    (h₁ : E.k1.slot = k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id)
    (h₂ : E.w.slot = wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)
    (h₃ : E.k10.slot = closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)
    (h₄ : E.k12.slot = simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K14 ∧
      VerifiableInference.Compilation.KindPays
        (theGOfReturn made hd T (theK E apart (laterOurs A₀ hd.head))) KindName.K12 := by
  obtain ⟨a, b, c, d⟩ := theK_pays_four hd hS hL made T E apart h₁ h₂ h₃ h₄
  exact ⟨castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K1) _ a,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K10) _ b,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K14) _ c,
    castSides_of (Q := fun _ G => VerifiableInference.Compilation.KindPays G KindName.K12) _ d⟩


section
open AtFullSide.Honest.TheLetters (OpenShared OpenLast OpenG)
variable [Inhabited P5J.TS] [Inhabited Desc.K14.St]
variable {Z : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit} (h : HeadAtReturn Z A)
  {O : OpenShared A} (P : OpenLast h O)

/-- **The four kinds at the letters, at the K of record.** -/
theorem letters_theK_four (hS : VerifierAndGoals.InScope Z = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (made : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL baseFill = .ok A)
    (E : AtPublicFiles.TheSides.TheThirteen baseFill A.Z A.G) (apart : (E.entries.map (·.slot.name)).Nodup)
    (h₁ : E.k1.slot = k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id)
    (h₂ : E.w.slot = wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)
    (h₃ : E.k10.slot = closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)
    (h₄ : E.k12.slot = simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :
    VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K1 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K10 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K14 ∧
      VerifiableInference.Compilation.KindPays (AtFullSide.Honest.TheLetters.theG h P
        ⟨AtPublicFiles.TheSides.theK E apart (laterOurs A h.head)⟩) KindName.K12 :=
  theK_pays_four h hS hL made (AtFullSide.Honest.TheLetters.parts h P) E apart h₁ h₂ h₃ h₄

end

end AtFullSide.M1

#print axioms AtFullSide.M1.letters_theK_four
#print axioms AtFullSide.M1.k12_rest_of_K
#print axioms AtFullSide.M1.second_rows_of_K
#print axioms AtFullSide.M1.kindPays_K12_sides
#print axioms AtFullSide.M1.kindPays_K12_theG
#print axioms AtFullSide.M1.theG_pays_four
#print axioms AtFullSide.M1.theK_pays_four
#print axioms AtFullSide.M1.theK_pays_four_ofReturn
