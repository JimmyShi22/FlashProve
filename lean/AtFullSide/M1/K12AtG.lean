-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- what the kind K12 pays at a G of ours.
/-
AtFullSide/M1/K12AtG.lean: wrappers from a row of a G of ours to `Good` at its seated side: at the first
chain's last test (`row_good`), at the test on G_u (`good_testOnU`), and the six's rows at places of the
kind K12 if any. The tests on G_omega and the request's own test enter `gOurs_K12_of` as hypotheses, each
by name: they are premises here. No property of the protocol is claimed here.
-/
import AtFullSide.M1.GOurs
import Johnson.Desc.ProofFile.Honest.K12.Sim2.KeystoneL
import Johnson.Desc.ProofFile.Honest.K12.Sim2.BookAtWritten
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotU
import Johnson.M1.SlotsSeat

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open ProofFile.Honest.K12.Sim2
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides
open OnBytes (TableKey)

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **A row of the first chain's last test has `Good` at its side.** -/
theorem k12L_row (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (F : FileDescription ProofFile.Inst)
    (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF) (Bk : ProverCoinCounts)
    (hB : ∀ o : Addr, o.place.kind = .K12 → ProofFile.Honest.Small.noneSpent Bk o = true) (ord : List Place)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (G : ProofFile.Ground)
    (T : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread Bk F.S₁ F.Cl (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells)
      (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (Sd : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins Bk →
      Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop) (fs : List (Fall F.S₁))
    (r : Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
    (hr : r ∈ rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref Zp G) :
    ∀ σ, (r.lay T Sd F.first.blocksInOrder).side F.first.blocksInOrder fs = some σ →
      ∃ A' B', Good pre .own σ Bk ord 0 0 A' B' (r.lay T Sd F.first.blocksInOrder).On
        (r.lay T Sd F.first.blocksInOrder).bud := by
  subst eF
  intro σ hσ
  obtain ⟨pl, -, -, rfl⟩ := mem_rowsOfLot matrixInput OnBytes.HonestTrace.Sz.ref Zp G r hr
  exact ⟨_, _, row_good h.toAtMg matrixInput OnBytes.HonestTrace.Sz.ref G pl Bk T Sd _ fs σ hσ ord hB 0
    (fun _ _ _ _ => False) pre⟩

/-- **A row of the test on G_u has `Good` at its side.** -/
theorem k12U_row (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (F : FileDescription ProofFile.Inst)
    (eF : F = P5J.F0T OnBytes.secondHashFunction Zp Np cF) (Bk : ProverCoinCounts)
    (hB : ∀ o : Addr, o.place.kind = .K12 → ProofFile.Honest.Small.noneSpent Bk o = true) (ord : List Place)
    (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (G : ProofFile.Ground)
    (T : Common FullSizeMatrix IndexCommitterCoins TableKey → Thread Bk F.S₂ F.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (Sd : Common FullSizeMatrix IndexCommitterCoins TableKey → Nat → Coins Bk → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
    (fs : List (Fall F.S₂)) (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hr : r ∈ (lotU .shared matrixInput.weights encOf).rows Zp G) :
    ∀ σ, (r.lay T Sd F.shared.blocksInOrder).side F.shared.blocksInOrder fs = some σ →
      ∃ A' B', Good pre .shared σ Bk ord 1 0 A' B' (r.lay T Sd F.shared.blocksInOrder).On
        (r.lay T Sd F.shared.blocksInOrder).bud := by
  subst eF
  intro σ hσ
  have hkr := rest_k12 Zp G r (List.mem_append_left _ hr)
  obtain ⟨J, hJ, rfl⟩ := List.mem_map.1 hr
  have hJ' : ProofFile.Honest.K12.AtProof.realU (matrixInput.weights Zp) (encOf Zp) Zp = some J := by
    cases e : ProofFile.Honest.K12.AtProof.realU (matrixInput.weights Zp) (encOf Zp) Zp with
    | none => rw [e] at hJ; cases hJ
    | some J' =>
      rw [e] at hJ
      exact congrArg some (List.mem_singleton.1 hJ).symm
  obtain ⟨hp, hf⟩ := realU_ties h.toAtMg _ _ hJ'
  obtain ⟨hs, ho, hop⟩ := simAtU_head h.toAtMg
  have g := good_testOnU h.toAtMg J (simAtU Zp) 1 hp hf hs ho hop .shared 0 fs σ hσ Bk ord
    (fun u _ => hB _ (by
      have e : σ.block.place = J.p.place := side_place hσ
      show σ.block.place.kind = _
      rw [e]
      exact hkr))
    (fun _ _ _ _ => False) pre
  rw [← hp] at g
  exact ⟨_, _, g⟩

/-- **No lot but the test at L lays a half of the kind K12 on the first chain.** -/
theorem lots_k12 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ baseFill.lots, ∀ g ∈ M.halves Z G, g.place.kind = KindName.K12 →
      M = proxLotAt matrixInput OnBytes.HonestTrace.Sz.ref := by
  intro M hM g hg e
  have hM' : M ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
    openHonest).lots := hM
  rw [widerFillAtCPUOWM_lots] at hM'
  simp only [List.mem_append, List.mem_singleton] at hM'
  rcases hM' with ((h | rfl) | rfl) | rfl
  · rw [widerFillAt_lots] at h
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 h
    have hk := (FirstFill.widerKinds matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest
      Z G).all q hq g hg
    rw [e] at hk
    have hno : KindName.K12 ∉ (widerPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
        openHonest).map (·.2) := by
      simp [widerPairs]
    exact (hno (List.mem_map.2 ⟨q, hq, hk.symm⟩)).elim
  · have hk := closeLotAt_kinds matrixInput OnBytes.HonestTrace.Sz.ref Z G g hg
    rw [e] at hk
    cases hk
  · rfl
  · have hk := AtFullSide.K12.wHalf_place matrixInput OnBytes.secondHashFunction openHonest Z G g hg
    rw [hk] at e
    cases e

/-- **The six have no row of the kind K12.** -/
theorem six_not_k12 (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) :
    ∀ r ∈ baseRows Zp Np, r.place.kind ≠ KindName.K12 := by
  intro r hr hk
  have e := ProofFile.Honest.K14.simRows_places (Ky := TableKey) (X := Unit) h (matrixInput.weights Zp)
    (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt Zp Np))
  have e' : (baseRows Zp Np).map (·.place) = _ := e
  have hm : r.place ∈ (baseRows Zp Np).map (·.place) := List.mem_map.2 ⟨r, hr, rfl⟩
  rw [e'] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with e1 | e1 | e1 | e1 | e1 | e1 <;> (rw [e1] at hk; cases hk)

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

/-- **`KindPays .K12` at `gOurs`, from the tests on G_omega and the request's own.** These two enter as
hypotheses, row by row: `hO`, `hW`: premises here. -/
theorem gOurs_K12_of (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (hO : ∀ r ∈ ProofFile.Honest.K12.AtProof.rowsAtOmega (matrixInput.weights A₀.Z) A₀.Z, ∀ σ,
      (r.lay T₂ S₂ A₀.F.shared.blocksInOrder).side A₀.F.shared.blocksInOrder f₂ = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf A₀.F 1) A₀.F.shared.blocksInOrder r.place) .shared σ A₀.B (orderOf A₀.F)
        1 0 A' B' r.On r.bud)
    (hW : ∀ r ∈ secondOurs A₀.Z A₀.G, ∀ σ,
      (r.lay T₃ S₃ A₀.F.second.blocksInOrder).side A₀.F.second.blocksInOrder f₃ = some σ →
      ∃ A' B', Good (preOf 2 A₀.F.lastChainFirstTreeNumber (earlierOf A₀.F 2) A₀.F.second.blocksInOrder r.place) .own σ A₀.B
        (orderOf A₀.F) 2 A₀.F.lastChainFirstTreeNumber A' B' r.On r.bud) :
    VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K12 := by
  have hB := ProofFile.Honest.K12.Sim2.noneSpent_at_maker h hA
  obtain ⟨hZ, -, hF, -⟩ := atPure_ok hA
  have eF : A₀.F = P5J.F0T OnBytes.secondHashFunction A₀.Z Np cF := Except.ok.inj (hF.symm.trans h.laid.value)
  refine ⟨?_, ?_, ?_⟩
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hl
    have hh : r.half ∈ M.halves A₀.Z A₀.G := by
      rw [← overlay_half (mine_hm A₀.Z A₀.G M hM)]
      exact List.mem_map.2 ⟨r, hrl, rfl⟩
    have e := lots_k12 A₀.Z A₀.G M hM _ hh hk
    subst e
    have ef : (mineOurs.find? fun s => s.name ==
        (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).name) =
        some (simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :=
      OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mineOurs mine_apart _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
    have eo : overlayLot mineOurs (proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) =
        simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref := by
      unfold overlayLot
      rw [ef]
    rw [eo] at hrl
    exact k12L_row h A₀.F eF A₀.B hB _ _ A₀.G T₁ S₁ f₁ r hrl σ hσ
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    rcases List.mem_append.1 hr with h1 | h1
    · exact (six_not_k12 h r h1 hk).elim
    · rcases List.mem_append.1 h1 with h2 | h2
      · exact k12U_row h A₀.F eF A₀.B hB _ _ A₀.G T₂ S₂ f₂ r h2 σ hσ
      · exact hO r h2 σ hσ
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    exact hW r hr σ hσ

end

end AtFullSide.M1

#print axioms AtFullSide.M1.k12L_row
#print axioms AtFullSide.M1.k12U_row
#print axioms AtFullSide.M1.gOurs_K12_of
