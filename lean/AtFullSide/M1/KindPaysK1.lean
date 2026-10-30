-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K1 pays, whole.
/-
AtFullSide/M1/KindPaysK1.lean: `KindPays G .K1` (Johnson/T3/KindPaysCore.lean) at the maker's return at
the term's filling. First chain: `k1_first_pays`. Shared chain: K14's `kind_clause_at_term`. Last chain:
empty, `k1_last_empty`. Premises: the scope, the gate, the maker's return and the head `P5J.AtMgA`, which
K14's clause takes (the head names the public part, places and first chain of the run at these files;
`P5J.head_exists_at_name` makes one where the files are in scope and the gate says yes); the rows of G
at the kind K1 on the first chain are those of K1's own lot and W's; the public test on the book; the
rows of G at the shared chain's two places of the kind K1 are those of the six. No property of the
protocol is claimed here.
-/
import AtFullSide.K14.Sim.AtTerm
import Johnson.T3.KindPaysCore
import AtFullSide.K12.MakerReturnsAtLive
import Johnson.M1.K1Rows
import Johnson.Desc.ProofFile.Honest.Rule
import Johnson.Desc.ProofFile.Honest.Owed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput tableCoins onlineMaker OnlineReturn termRows)
open Johnson.M1 (k1Lot wLot)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes (TableKey)

/-- **What the kind K1 pays, at any return of the maker.** -/
theorem kindPays_K1_at {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {W₀ W₀' Rc' Tr Y₀ Ky X₀ : Type} {Fl : OnlineProverParts W₀' Rc' Tr Y₀ Unit} {R : OnlineProverWithDescription W₀' Rc' Tr Y₀ Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL Fl = .ok R)
    (I : WiderIn W₀) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (g : W₀' → W₀) (rd : Rc' → IndexCommitterCoins)
    (weights : W₀' → Weights) (rand : Rc' → TableRand)
    (G : Sides R.F R.B W₀' Rc' Ky Cells X₀ Unit)
    (T₁ : Local W₀' Rc' ProofFile.Inst Cells → Thread R.B R.F.S₁ R.F.Cl
      (Local W₀' Rc' ProofFile.Inst Cells) (Local W₀' Rc' ProofFile.Inst Cells) Unit ProofFile.Inst)
    (S₁ : Local W₀' Rc' ProofFile.Inst Cells → Nat → Coins R.B →
      Mid (Local W₀' Rc' ProofFile.Inst Cells) Unit → Prop)
    (r₁ : List (Unlettered (Local W₀' Rc' ProofFile.Inst Cells)
      (Local W₀' Rc' ProofFile.Inst Cells) Unit ProofFile.Inst))
    (hG : G.first = r₁.map fun r => r.lay T₁ S₁ R.F.first.blocksInOrder)
    (hk : ∀ r ∈ r₁, r.place.kind = KindName.K1 →
      r ∈ (k1Lot (Pb := ProofFile.Inst) I OnBytes.secondHashFunction S g rd).rows R.Z R.G ∨
        r ∈ (wLot (Pb := ProofFile.Inst) I OnBytes.secondHashFunction O g rd).rows R.Z R.G)
    (book : ∀ e ∈ R.B.ahead, e.once = true →
      OnBytes.SendSim.Seat.lotsMine R.Z R.G e.owner = true →
      OnBytes.SendSim.Seat.lotsOkB R.Z R.G R.B (orderOf R.F) e.owner = true)
    (rows : ∀ L ∈ G.shared, L.place.kind = KindName.K1 →
      ∃ r ∈ (ProofFile.Honest.K14.simRows (ProofFile.Honest.K14.simData Zp Np) (ProofFile.Honest.K14.simPub Zp Np)
          weights rand : List (Unlettered Empty (Common W₀' Rc' Ky) X₀ Ky)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    VerifiableInference.Compilation.KindPays G KindName.K1 := by
  refine ⟨?_, ProofFile.Honest.K14.kind_clause_at_return h hA weights rand G KindName.K1 rows, ?_⟩
  · intro L hLm
    rw [hG] at hLm
    exact Johnson.M1.k1_first_pays hS hL hA I S O g rd T₁ S₁ r₁ G.falls₁ hk book L hLm
  · intro L _ hk3 σ hσ
    exact (Johnson.M1.k1_last_empty hS hL hA hk3 hσ).elim

/-- **What the kind K1 pays at the base filling**, `onlineProverPartsInUse` at its own types. -/
theorem kindPays_K1_base {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL
      (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest) = .ok A₀)
    (G : Sides A₀.F A₀.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit)
    (T₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread A₀.B A₀.F.S₁ A₀.F.Cl
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (S₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins A₀.B →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
    (r₁ : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst))
    (hG : G.first = r₁.map fun r => r.lay T₁ S₁ A₀.F.first.blocksInOrder)
    (hk : ∀ r ∈ r₁, r.place.kind = KindName.K1 →
      r ∈ (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id).rows
          A₀.Z A₀.G ∨
        r ∈ (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id id).rows A₀.Z A₀.G)
    (book : ∀ e ∈ A₀.B.ahead, e.once = true →
      OnBytes.SendSim.Seat.lotsMine A₀.Z A₀.G e.owner = true →
      OnBytes.SendSim.Seat.lotsOkB A₀.Z A₀.G A₀.B (orderOf A₀.F) e.owner = true)
    (rows : ∀ L ∈ G.shared, L.place.kind = KindName.K1 →
      ∃ r ∈ (ProofFile.Honest.K14.simRows (ProofFile.Honest.K14.simData Zp Np) (ProofFile.Honest.K14.simPub Zp Np)
          (matrixInput.weights Zp) (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt Zp Np)) :
          List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)),
        L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    VerifiableInference.Compilation.KindPays G KindName.K1 :=
  kindPays_K1_at h hS hL hA matrixInput OnBytes.HonestTrace.Sz.ref openHonest id id
    (matrixInput.weights Zp) (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt Zp Np)) G T₁ S₁ r₁ hG hk book
    rows

/-- **What the kind K1 pays at the term.** -/
theorem kindPays_K1 {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    {returned : OnlineReturn files} (hA : onlineMaker files = .ok returned)
    (G : Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Cells Unit Unit)
    (T₁ : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Thread returned.B returned.F.S₁ returned.F.Cl
      (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit ProofFile.Inst)
    (S₁ : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Nat → Coins returned.B →
      Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit → Prop)
    (r₁ : List (Unlettered (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells)
      (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit ProofFile.Inst))
    (hG : G.first = r₁.map fun r => r.lay T₁ S₁ returned.F.first.blocksInOrder)
    (hk : ∀ r ∈ r₁, r.place.kind = KindName.K1 →
      r ∈ (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id
          (tableCoins files)).rows returned.Z returned.G ∨
        r ∈ (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id
          (tableCoins files)).rows returned.Z returned.G)
    (book : ∀ e ∈ returned.B.ahead, e.once = true →
      OnBytes.SendSim.Seat.lotsMine returned.Z returned.G e.owner = true →
      OnBytes.SendSim.Seat.lotsOkB returned.Z returned.G returned.B (orderOf returned.F) e.owner =
        true)
    (rows : ∀ L ∈ G.shared, L.place.kind = KindName.K1 → ∃ r ∈ termRows files Zp Np,
      L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) :
    VerifiableInference.Compilation.KindPays G KindName.K1 :=
  kindPays_K1_at h hS hL hA matrixInput OnBytes.HonestTrace.Sz.ref openHonest id (tableCoins files)
    (matrixInput.weights Zp) (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt Zp Np) ∘ tableCoins files) G
    T₁ S₁ r₁ hG hk book rows

/-- **What the kind K1 pays at three public files**, the head and the return paid. Left: `hG`, `hk`,
`book`, `rows`. -/
def K1PaysAtFiles (files : VerifierAndGoals.PublicFiles) : Prop :=
    ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (returned : OnlineReturn files),
      onlineMaker files = .ok returned ∧ returned.Z = Zp ∧ H2U.placesOfMade returned.Z.made = .ok Np ∧
      ∀ (G : Sides returned.F returned.B FullSizeMatrix (protocolAtFiles files).EncodingRandomness TableKey Cells Unit Unit)
        (T₁ : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Thread returned.B returned.F.S₁ returned.F.Cl
          (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit
          ProofFile.Inst)
        (S₁ : Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells → Nat → Coins returned.B →
          Mid (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit → Prop)
        (r₁ : List (Unlettered (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells)
          (Local FullSizeMatrix (protocolAtFiles files).EncodingRandomness ProofFile.Inst Cells) Unit ProofFile.Inst)),
        (G.first = r₁.map fun r => r.lay T₁ S₁ returned.F.first.blocksInOrder) →
        (∀ r ∈ r₁, r.place.kind = KindName.K1 →
          r ∈ (k1Lot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id
              (tableCoins files)).rows returned.Z returned.G ∨
            r ∈ (wLot (Pb := ProofFile.Inst) matrixInput OnBytes.secondHashFunction openHonest id
              (tableCoins files)).rows returned.Z returned.G) →
        (∀ e ∈ returned.B.ahead, e.once = true →
          OnBytes.SendSim.Seat.lotsMine returned.Z returned.G e.owner = true →
          OnBytes.SendSim.Seat.lotsOkB returned.Z returned.G returned.B (orderOf returned.F)
            e.owner = true) →
        (∀ L ∈ G.shared, L.place.kind = KindName.K1 → ∃ r ∈ termRows files Zp Np,
          L.place = r.place ∧ L.row = r.row ∧ L.On = r.On ∧ L.bud = r.bud) →
        VerifiableInference.Compilation.KindPays G KindName.K1

/-- **Where the gate accepts.** -/
theorem kindPays_K1_live (files : VerifierAndGoals.PublicFiles) {pp : Inst.Model.ScalesAndPolicy}
    (hS : VerifierAndGoals.InScope files = true) (read : VerifierAndGoals.readFiles files = .ok pp)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true) : K1PaysAtFiles files := by
  obtain ⟨Zp, Np, cF, x, h⟩ := P5J.head_exists_at_name files hS read hL (P5J.owed_of_live hL)
  obtain ⟨A, hA⟩ := AtFullSide.K12.maker_returns files hS read hL
  obtain ⟨hZp, -⟩ := atPure_ok hA
  have eZ : A.Z = Zp := Except.ok.inj (hZp.symm.trans h.laid.pub)
  exact ⟨Zp, Np, A, hA, eZ, by rw [eZ]; exact h.laid.places, fun G T₁ S₁ r₁ hG hk book rows =>
    kindPays_K1 h hS hL hA G T₁ S₁ r₁ hG hk book rows⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.kindPays_K1_at
#print axioms AtFullSide.M1.kindPays_K1_base
#print axioms AtFullSide.M1.kindPays_K1
#print axioms AtFullSide.M1.kindPays_K1_live
