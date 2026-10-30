-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K12 pays (pays alone: one field of three of KindShare) at a G of ours, with no hypothesis on the tests on G_omega and W.
/-
AtFullSide/M1/K12Closed.lean: `gOurs_K12_of` (AtFullSide/M1/K12AtG.lean) with its two hypotheses paid: at the test on G_omega by `omega_good` (SimO/Top.lean), at the request's own test by `good_at_lot_W` (Sim2/ListWAtLot.lean); `noneSpent` by `noneSpent_at_maker`.

  `k12O_row`, `k12W_row`   a row of each test has `Good` at its side
  `gOurs_K12`   **`KindPays .K12` at `gOurs`, from the head and the maker's return alone**

Limits. `Good` at A := False: `plays` and `acc` are met for nothing, and `exact` is conditional on On. At the base filling, not read through. No property of the protocol is claimed.
-/
import AtFullSide.M1.K12AtG
import AtFullSide.K12.Sim.OmegaAtBase
import Johnson.Desc.ProofFile.Honest.K12.Sim2.ListWAtLot

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput)
open ProofFile.Honest.K12.Sim2
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides
open OnBytes (TableKey)

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **A row of the test on G_omega has `Good` at its side.** -/
theorem k12O_row (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (F : FileDescription ProofFile.Inst)
    (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF) (Bk : ProverCoinCounts)
    (hB : ∀ o : Addr, o.place.kind = .K12 → ProofFile.Honest.Small.noneSpent Bk o = true) (ord : List Place)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound))
    (T : Common FullSizeMatrix IndexCommitterCoins TableKey → Thread Bk F.S₂ F.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (Sd : Common FullSizeMatrix IndexCommitterCoins TableKey → Nat → Coins Bk → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fs : List (Fall F.S₂)) (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hr : r ∈ ProofFile.Honest.K12.AtProof.rowsAtOmega (matrixInput.weights Zp) Zp) :
    ∀ σ, (r.lay T Sd F.shared.blocksInOrder).side F.shared.blocksInOrder fs = some σ →
      ∃ A' B', Good pre .shared σ Bk ord 1 0 A' B' (r.lay T Sd F.shared.blocksInOrder).On
        (r.lay T Sd F.shared.blocksInOrder).bud := by
  subst eF
  intro σ hσ
  have hm := h.toAtMg
  have hkr : r.place.kind = .K12 := ProofFile.Honest.K12.AtProof.rowsAtOmega_kind _ _ r hr
  obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head hm
  obtain ⟨bs, hbs⟩ := ProofFile.Honest.K12.Light.blocks_head hm
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.Sh.blocks_eight_of hbs
  have hσp : σ.block.place = r.place := side_place hσ
  rw [ProofFile.Honest.Term.rowsAtOmega_at_head hm hO b1 b2 b3 b4 b5 b6 b7 b8 hbs, List.mem_singleton] at hr
  subst hr
  exact ⟨_, fun _ _ _ _ => False, ProofFile.Honest.K12.Light.omega_good hm hO _ _ _ none (ProofFile.Honest.K12.AtProof.simulatorJobAtOmega Zp.p.chains (ProofFile.Honest.K14.qAt Zp Np) (ProofFile.Honest.K12.AtProof.fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl fs σ hσ pre Face.shared 1 0 rfl Bk ord
    (fun _ _ _ _ => False) fun u _ => hB _ (by
      show σ.block.place.kind = _
      rw [hσp]
      exact hkr)⟩

/-- **A row of the request's own test has `Good` at its side.** -/
theorem k12W_row (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (F : FileDescription ProofFile.Inst)
    (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF) (Bk : ProverCoinCounts)
    (hB : ∀ o : Addr, o.place.kind = .K12 → ProofFile.Honest.Small.noneSpent Bk o = true) (ord : List Place)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (firstTree : Nat) (G : ProofFile.Ground)
    (T : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread Bk F.S₃ F.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (Sd : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins Bk →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) (fs : List (Fall F.S₃))
    (r : Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hr : r ∈ secondOurs Zp G) :
    ∀ σ, (r.lay T Sd F.second.blocksInOrder).side F.second.blocksInOrder fs = some σ →
      ∃ A' B', Good pre .own σ Bk ord 2 firstTree A' B' (r.lay T Sd F.second.blocksInOrder).On
        (r.lay T Sd F.second.blocksInOrder).bud := by
  subst eF
  intro σ hσ
  have hm := h.toAtMg
  have hkr : r.place.kind = .K12 := second_k12 Zp G r hr
  have hσp : σ.block.place = r.place := side_place hσ
  obtain ⟨M, hM, rfl⟩ := row_of_lotW hm .own matrixInput OnBytes.HonestTrace.Sz.ref openHonest G r hr
  exact ⟨_, fun _ _ _ _ => False, good_at_lot_W hm matrixInput OnBytes.HonestTrace.Sz.ref openHonest G M hM _ rfl fs σ hσ pre ord
    firstTree (fun _ _ _ _ => False) fun u _ => hB _ (by
      show σ.block.place.kind = _
      rw [hσp]
      exact hkr)⟩

section
variable {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
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
  (f₁ : List (Fall A₀.F.S₁)) (f₂ : List (Fall A₀.F.S₂)) (f₃ : List (Fall A₀.F.S₃))

/-- **`KindPays .K12` at `gOurs`, from the head and the maker's return alone.** -/
theorem gOurs_K12 (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀) :
    VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K12 := by
  have hB := ProofFile.Honest.K12.Sim2.noneSpent_at_maker h hA
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  have eF : A₀.F = P5J.F0T OnBytes.secondHashFunction A₀.Z Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  exact gOurs_K12_of T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h hA
    (fun r hr σ hσ => k12O_row h A₀.F eF A₀.B hB _ _ T₂ S₂ f₂ r hr σ hσ)
    (fun r hr σ hσ => k12W_row h A₀.F eF A₀.B hB _ _ _ A₀.G T₃ S₃ f₃ r hr σ hσ)

end

end AtFullSide.M1

#print axioms AtFullSide.M1.k12O_row
#print axioms AtFullSide.M1.k12W_row
#print axioms AtFullSide.M1.gOurs_K12
