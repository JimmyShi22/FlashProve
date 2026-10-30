-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K1 pays at the one G.
/-
AtFullSide/M1/KindAtSides.lean: `VerifiableInference.Compilation.KindPays G .K1` at `theSides` (E2E/TheSides.lean), at the base filling,
at the rows that `overlaySlots` lays, where the kinds' own lots hold K1's own and W's. `hG` holds by
definition, `hk` by `overlay_k1`, the book by `book_at_return`. Left as hypotheses: that the shared rows of
the kind K1 are the six (`hsh`), and what `overlaySlots` itself takes, one hypothesis a lot. No property
of the protocol is claimed here.
-/
import AtFullSide.M1.KindPaysDoor
import Johnson.M1.K1Only
import E2E.TheSides
import AtFullSide.K14.Sim.AtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput)
open Johnson.M1 (k1Lot wLot k1_only)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides
open OnBytes (TableKey)

/-- The base filling. -/
noncomputable abbrev baseFill :=
  onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest

/-- The rows of the first chain at the base, with their simulators. -/
abbrev Lots₀ :=
  List (SLot (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)

/-- **A row of the kind K1 among the lots laid over the filling is a row of our two lots.** -/
theorem overlay_k1 (Z : ProofFile.Pub) (G : ProofFile.Ground) (mine : Lots₀)
    (hm : ∀ L ∈ baseFill.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows Z G).map (·.half) = L.halves Z G)
    (hf₁ : (mine.find? fun s => s.name ==
        (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id).name) =
      some (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id))
    (hf₂ : (mine.find? fun s => s.name ==
        (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id).name) =
      some (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id)) :
    ∀ r ∈ rowsOfLots Z G (baseFill.lots.map (overlayLot mine)), r.place.kind = KindName.K1 →
      r ∈ (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id).rows
          Z G ∨
        r ∈ (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id).rows Z G := by
  intro r hr hk
  obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hl
  have hh : r.half ∈ L.halves Z G := by
    rw [← overlay_half (hm L hL)]
    exact List.mem_map.2 ⟨r, hrl, rfl⟩
  rcases k1_only matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G L hL r.half hh
    hk with e | e
  · subst e
    left
    have e1 : overlayLot mine (HLot.byPub matrixInput.weights (LongLots.plain (W₀ := FullSizeMatrix) (X := Unit)
        OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).k1) =
        k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id := by
      unfold overlayLot
      rw [show (mine.find? fun s => s.name == (HLot.byPub matrixInput.weights
        (LongLots.plain (W₀ := FullSizeMatrix) (X := Unit) OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
          openHonest).k1).name) = _ from hf₁]
    rw [e1] at hrl
    exact hrl
  · subst e
    right
    have e1 : overlayLot mine (wLotAt matrixInput OnBytes.secondHashFunction openHonest) =
        wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id := by
      unfold overlayLot
      rw [show (mine.find? fun s => s.name ==
        (wLotAt (X := Unit) matrixInput OnBytes.secondHashFunction openHonest).name) = _ from hf₂]
    rw [e1] at hrl
    exact hrl

/-- **The premise `hsh`**, at shared rows that are the six, then rows of the kind K12 (`base_shared`'s
rest, `rest_kind`). -/
theorem hsh_of_rest (Zp : ProofFile.Pub) (Np : H2U.Places4)
    (rest : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey))
    (hr : ∀ r ∈ rest, r.place.kind = KindName.K12) :
    ∀ r ∈ ProofFile.Honest.Term.baseRows Zp Np ++ rest, r.place.kind = KindName.K1 →
      r ∈ ProofFile.Honest.Term.baseRows Zp Np := by
  intro r hm hk
  rcases List.mem_append.1 hm with h | h
  · exact h
  · have h2 := hr r h
    rw [hk] at h2
    cases h2

/-- **`KindPays .K1` at the one G, at the base filling.** -/
theorem kindPays_K1_sides {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (mine : Lots₀)
    (named : ∀ s ∈ mine, baseFill.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ baseFill.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A₀.Z A₀.G).map (·.half) = L.halves A₀.Z A₀.G)
    (hf₁ : (mine.find? fun s => s.name ==
        (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id).name) =
      some (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id))
    (hf₂ : (mine.find? fun s => s.name ==
        (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id).name) =
      some (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id))
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey))
    (hs : shared.map (·.half) = baseFill.shared A₀.Z A₀.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)) (h₃ : second.map (·.half) = baseFill.second A₀.Z A₀.G)
    (hsh : ∀ r ∈ shared, r.place.kind = KindName.K1 →
      r ∈ (ProofFile.Honest.K14.simRows (ProofFile.Honest.K14.simData Zp Np) (ProofFile.Honest.K14.simPub Zp Np)
          (matrixInput.weights Zp) (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt Zp Np)) :
          List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)))
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
      KindName.K1 := by
  refine kindPays_K1_base h hS hL hA _ T₁ S₁
    (rowsOfLots A₀.Z A₀.G (baseFill.lots.map (overlayLot mine))) rfl
    (overlay_k1 A₀.Z A₀.G mine hm hf₁ hf₂) (book_at_return hS hL hA) ?_
  intro L hLm hk
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
  exact ⟨r, hsh r hr hk, rfl, rfl, rfl, rfl⟩

/-- **What the kind K1 pays at the one G at a base return**: at every value of what `overlaySlots` takes,
and of the threads and falls. -/
def SidesK1 (Zp : ProofFile.Pub) (Np : H2U.Places4) (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) : Prop :=
  ∀ (mine : Lots₀)
    (named : ∀ s ∈ mine, baseFill.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ baseFill.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A₀.Z A₀.G).map (·.half) = L.halves A₀.Z A₀.G)
    (hf₁ : (mine.find? fun s => s.name ==
        (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id).name) =
      some (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id))
    (hf₂ : (mine.find? fun s => s.name ==
        (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id).name) =
      some (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id))
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey))
    (hs : shared.map (·.half) = baseFill.shared A₀.Z A₀.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)) (h₃ : second.map (·.half) = baseFill.second A₀.Z A₀.G)
    (hsh : ∀ r ∈ shared, r.place.kind = KindName.K1 →
      r ∈ (ProofFile.Honest.K14.simRows (ProofFile.Honest.K14.simData Zp Np) (ProofFile.Honest.K14.simPub Zp Np)
          (matrixInput.weights Zp) (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt Zp Np)) :
          List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)))
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
    (f₁ : List (Fall A₀.F.S₁)) (f₂ : List (Fall A₀.F.S₂)) (f₃ : List (Fall A₀.F.S₃)),
    VerifiableInference.Compilation.KindPays (theSides A₀.F (Letters.ofThreads A₀.F T₁ T₂ T₃ S₁ S₂ S₃)
      (overlaySlots baseFill A₀.Z A₀.G mine named apart hm shared hs second h₃).rows f₁ f₂ f₃)
      KindName.K1

/-- **Where the gate accepts, under the head.** -/
theorem sidesK1_of_head {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀) :
    SidesK1 Zp Np A₀ :=
  fun mine named apart hm hf₁ hf₂ shared hs second h₃ hsh T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ =>
    kindPays_K1_sides h hS hL hA mine named apart hm hf₁ hf₂ shared hs second h₃ hsh T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃

/-- **K1 at the base, at three public files.** -/
def K1AtBase (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit),
    ProofFile.Honest.Term.baseMaker files = .ok A₀ ∧ A₀.Z = Zp ∧
      H2U.placesOfMade A₀.Z.made = .ok Np ∧ SidesK1 Zp Np A₀

/-- **At either named set**: no premise outside. `SidesK1` keeps inside it what `overlaySlots` takes, `hf₁`,
`hf₂` and `hsh`. -/
theorem k1_at_base_named (files : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles files) : K1AtBase files := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named files hZ
  have live := AtFullSide.K14.live_named files hZ
  have hS : VerifierAndGoals.InScope files = true := by
    rcases hZ with rfl | rfl
    · exact AtFullSide.Tie.premises_zFull.1
    · exact AtFullSide.Tie.premises_zGap.1
  obtain ⟨A, hA, -, -, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest ProofFile.Honest.Term.range_matrixInput
  obtain ⟨hZp, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZp.symm.trans h.laid.pub)
  exact ⟨Zp, Np, A, hA, eZ, by rw [eZ]; exact h.laid.places, sidesK1_of_head h hS live hA⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.k1_at_base_named
#print axioms AtFullSide.M1.overlay_k1
#print axioms AtFullSide.M1.hsh_of_rest
#print axioms AtFullSide.M1.kindPays_K1_sides
