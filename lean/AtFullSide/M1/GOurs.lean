-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- our kinds' rows, assembled.
/-
AtFullSide/M1/GOurs.lean: A G WHOSE HALVES ARE THE BASE MAKER'S OWN AT EVERY PLACE, IN ORDER, WITH OUR FOUR
LOTS AND ALL SHARED AND LAST ROWS BESIDE THEIR SIMULATORS AND NINE LOTS STILL BARE: NOT THE G OF THE
ZERO-KNOWLEDGE THEOREM: at a bare row whose part sends anything `exact` is false, so `∀ κ, KindPays` fails
here. The clauses for K1, K10, K14 are stated general in `mine` (`kindPays_K1_sides`, `kindPays_K10_sides`,
`kindPays_K14_sides`); those at this G are their corollaries. No property of the protocol is claimed here.
-/
import AtFullSide.M1.KindAtSides
import Johnson.Desc.ProofFile.Honest.K10.Slot.AtFill
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotValueL
import Johnson.Desc.ProofFile.Honest.K12.SimO.SlotO
import Johnson.M1.SlotsUW
import Johnson.M1.K1Socket
import AtFullSide.K12.SidesSocket
import AtFullSide.K14.Sim.RestKinds
import AtFullSide.K12.ReturnsAtFillW
import Johnson.Desc.ProofFile.Honest.K10.Slot.AtTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.M1
open ProofFile.Honest ProofFile.Honest.K1 OnBytes VerifiableInference.Desc
open ProofFile.Honest.Term (matrixInput baseRows)
open ProofFile.Honest.K12.Sim2 (simulatorLot simulatorLot_toHLot lotU lotU_halves rowsW lotW lotW_halves)
open ProofFile.Honest.K12.AtProof (rowsAtOmega rowsAtOmega_half)
open Johnson.M1 (k1Lot wLot k1_socket w_socket)
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open AtPublicFiles.TheSides
open OnBytes (TableKey)

/-- **Our lots of the first chain.** -/
noncomputable def mineOurs : Lots₀ :=
  [k1Lot matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref id id,
   closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref,
   simulatorLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref,
   wLot matrixInput OnBytes.secondHashFunction openHonest id id]

set_option maxRecDepth 1000000 in
/-- The filling's lots have names apart. -/
theorem lots_names : (baseFill.lots.map (·.name)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Our lots have names apart. -/
theorem mine_apart : (mineOurs.map (·.name)).Nodup := by decide +kernel

set_option maxRecDepth 1000000 in
/-- Each of our lots has the name of a lot of the filling. -/
theorem mine_named : ∀ s ∈ mineOurs, baseFill.lots.any (fun L => L.name == s.name) = true := by
  decide +kernel

theorem k1_mem : HLot.byPub matrixInput.weights (LongLots.plain (W₀ := FullSizeMatrix) (X := Unit) OnBytes.secondHashFunction
    OnBytes.HonestTrace.Sz.ref openHonest).k1 ∈ baseFill.lots := by
  show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_cons_self ..)))

theorem close_mem : closeLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ baseFill.lots := by
  show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ (.head _)))

theorem prox_mem : proxLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ baseFill.lots := by
  show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_left _ (List.mem_append_right _ (.head _))

theorem w_mem : wLotAt (X := Unit) matrixInput OnBytes.secondHashFunction openHonest ∈ baseFill.lots := by
  show _ ∈ (onlineProverPartsInUse matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest).lots
  rw [widerFillAtCPUOWM_lots]
  exact List.mem_append_right _ (.head _)

/-- **The one hypothesis a lot, at our four.** -/
theorem mine_hm (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ L ∈ baseFill.lots, ∀ s, (mineOurs.find? fun s => s.name == L.name) = some s →
      (s.rows Z G).map (·.half) = L.halves Z G := by
  intro L hL s hs
  have hmem := List.mem_of_find?_eq_some hs
  have hname : s.name = L.name :=
    beq_iff_eq.1 (List.find?_some (p := fun s : SLot _ _ _ _ => s.name == L.name) hs)
  have key : ∀ P ∈ baseFill.lots, P.name = s.name → L = P := fun P hP e =>
    List.inj_on_of_nodup_map lots_names hL hP (hname.symm.trans e.symm)
  simp only [mineOurs, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl
  · rw [key _ k1_mem rfl]
    exact k1_socket matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G
  · rw [key _ close_mem rfl]
    exact congrFun (congrFun (congrArg HLot.halves
      (closingsSLotAt_toHLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)) Z) G
  · rw [key _ prox_mem rfl]
    exact congrFun (congrFun (congrArg HLot.halves
      (simulatorLot_toHLot (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref)) Z) G
  · rw [key _ w_mem rfl]
    exact w_socket matrixInput OnBytes.secondHashFunction openHonest Z G

/-- The reader of the encoded table, as the test on G_u takes it. -/
noncomputable abbrev encOf : ProofFile.Pub → FullSizeMatrix → IndexCommitterCoins → Nat → Nat → Option (List Cb.Gl.F) :=
  fun Z w => Bind.ForProver.encW Z (matrixInput.weights Z w)

/-- **The shared chain's rows**: the six, the test on G_u, the test on G_omega. -/
noncomputable def sharedOurs (Zp : ProofFile.Pub) (Np : H2U.Places4) (G : ProofFile.Ground) :
    List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey) :=
  baseRows Zp Np ++ ((lotU .shared matrixInput.weights encOf).rows Zp G ++
    rowsAtOmega (matrixInput.weights Zp) Zp)

/-- **The last chain's rows.** -/
noncomputable def secondOurs (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst) :=
  rowsW .own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G

/-- **The shared chain's rows are the filling's**, under the head. -/
theorem shared_fit {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ Zp Np cF x₀) (G : ProofFile.Ground) :
    (sharedOurs Zp Np G).map (·.half) = baseFill.shared Zp G := by
  have hs := ProofFile.Honest.K14.simRows_now (Pb := TableKey) h (matrixInput.weights Zp)
  show _ = ProofFile.Honest.K12.AtProof.sharedWithUO matrixInput Zp
  unfold ProofFile.Honest.K12.AtProof.sharedWithUO sharedOurs
  have eU : ((lotU .shared matrixInput.weights encOf).rows Zp G).map (·.half) =
      ProofFile.Honest.K12.AtProof.halfU (matrixInput.weights Zp) (encOf Zp) Zp :=
    lotU_halves .shared matrixInput.weights encOf Zp G
  rw [hs, List.map_append, List.map_append, rowsAtOmega_half, eU]
  exact (List.append_assoc _ _ _).symm

/-- **The last chain's rows are the filling's.** -/
theorem second_fit (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    (secondOurs Z G).map (·.half) = baseFill.second Z G :=
  lotW_halves (X := Unit) .own matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G

/-- A row of the tests behind the six is of the kind K12. -/
theorem rest_k12 (Zp : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ r ∈ (lotU .shared matrixInput.weights encOf).rows Zp G ++
        rowsAtOmega (matrixInput.weights Zp) Zp, r.place.kind = KindName.K12 := by
  intro r hr
  have eU : ((lotU .shared matrixInput.weights encOf).rows Zp G).map (·.half) =
      ProofFile.Honest.K12.AtProof.halfU (matrixInput.weights Zp) (encOf Zp) Zp :=
    lotU_halves .shared matrixInput.weights encOf Zp G
  have hh : r.half ∈ ProofFile.Honest.K12.AtProof.halfU (matrixInput.weights Zp) (encOf Zp) Zp ++
      ProofFile.Honest.K12.AtProof.halfO (matrixInput.weights Zp) Zp := by
    rw [← eU, ← rowsAtOmega_half, ← List.map_append]
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  exact ProofFile.Honest.K12.AtProof.rest_kind _ _ _ _ hh

/-- **The socket of the shared chain**: a row of another kind than K12 is one of the six. -/
theorem rows_of_shared (Zp : ProofFile.Pub) (Np : H2U.Places4) (G : ProofFile.Ground) (κ : KindName)
    (hκ : κ ≠ KindName.K12) :
    ∀ r ∈ sharedOurs Zp Np G, r.place.kind = κ → r ∈ baseRows Zp Np := by
  intro r hm hk
  rcases List.mem_append.1 hm with h | h
  · exact h
  · exact absurd ((hk.symm.trans (rest_k12 Zp G r h))) hκ

/-- No side stands at a kind that the chain has not. -/
theorem no_side {S Cl V W Y Pb : Type} {Bk : ProverCoinCounts} {bs : List (Block S Cl)} {κ : KindName}
    (hno : ∀ b ∈ bs, b.place.kind ≠ κ) {L : Lettered Bk S Cl V W Y Pb} (hk : L.place.kind = κ)
    {f : List (Fall S)} {σ : Side S Cl V W Y Pb} (hσ : L.side bs f = some σ) : False := by
  have hf := OnBytes.SendSim.Seat.find_of_seated hσ
  have hm := List.mem_of_find?_eq_some hf
  have hp := List.find?_some (p := fun b : Block S Cl => b.place == L.place) hf
  have e : σ.block.place = L.place := beq_iff_eq.1 hp
  exact hno _ hm (e ▸ hk)

set_option maxRecDepth 1000000 in
/-- The kinds that the written chains have not. -/
theorem cuts_kinds :
    (VerifiableInference.PlanWritten.cutFirstFull.all fun r => r.2.1.kind != KindName.K14) = true ∧
    (VerifiableInference.PlanWritten.cutSharedFull.all fun r => r.2.1.kind != KindName.K10) = true ∧
    (VerifiableInference.PlanWritten.cutSecondFull.all fun r => r.2.1.kind != KindName.K10) = true := by
  decide +kernel

/-- The cuts of the description at a return. -/
theorem cuts_at_return {W₀ Rc Tr Y₀ X' : Type} {P : VerifierAndGoals.PublicFiles} {Fl : OnlineProverParts W₀ Rc Tr Y₀ X'}
    {R : OnlineProverWithDescription W₀ Rc Tr Y₀ X'} (hS : VerifierAndGoals.InScope P = true)
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    (h : onlineProverFromPublicFiles OnBytes.secondHashFunction P.pol P.lay P.KL Fl = .ok R) :
    VerifiableInference.PlanWritten.cutOf R.F.first.blocksInOrder = VerifiableInference.PlanWritten.cutFirstFull ∧
      VerifiableInference.PlanWritten.cutOf R.F.shared.blocksInOrder = VerifiableInference.PlanWritten.cutSharedFull ∧
      VerifiableInference.PlanWritten.cutOf R.F.second.blocksInOrder = VerifiableInference.PlanWritten.cutSecondFull := by
  obtain ⟨Bs, base, c, A, B, O, -⟩ := Johnson.M1.open_of_return h
  obtain ⟨-, h4⟩ := OnBytes.SendSim.Seat.plan_of_live hL O
  have hk := VerifiableInference.PlanWritten.key_in_scope_pure hS O.pub
  obtain ⟨-, hc⟩ := LPFD.asks_pins h4 O.pub (decide_eq_true hk)
  exact VerifiableInference.PlanWritten.cutIs_eq hc

/-- A written chain's kind test, read at its blocks. -/
theorem no_kind_of_cut {S Cl : Type} {bs : List (Block S Cl)} {κ : KindName}
    {C : List (String × Place × Nat × Nat × List (Nat × List VerifiableInference.Desc.Oracle) ×
      List (Nat × Nat))}
    (hc : VerifiableInference.PlanWritten.cutOf bs = C) (hall : (C.all fun r => r.2.1.kind != κ) = true) :
    ∀ b ∈ bs, b.place.kind ≠ κ := by
  intro b hb hk
  have hm : (b.name, b.place, b.rounds.length, b.oracles.length,
      VerifiableInference.PlanWritten.toldRounds b, b.before) ∈ C := by
    rw [← hc]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  have h1 := List.all_eq_true.1 hall _ hm
  simp only [bne_iff_ne, ne_eq] at h1
  exact h1 hk

/-- **The socket of the last chain**: every row of ours there is of the kind K12. The chain's other
sub-protocol of a kind, «K14, second part», has no round and no row. -/
theorem second_k12 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ r ∈ secondOurs Z G, r.place.kind = KindName.K12 := by
  intro r hr
  have hh : r.half ∈ ProofFile.Honest.secondW matrixInput OnBytes.secondHashFunction
      OnBytes.HonestTrace.Sz.ref openHonest Z G := by
    have e := second_fit Z G
    have e' : (secondOurs Z G).map (·.half) = ProofFile.Honest.secondW matrixInput
        OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest Z G := e
    rw [← e']
    exact List.mem_map.2 ⟨r, hr, rfl⟩
  unfold ProofFile.Honest.secondW at hh
  split at hh
  · have e : r.place = _ := AtFullSide.K12.halfW_place _ _ _ _ _ _ _ _ Z G _ hh
    rw [e]
    rfl
  · cases hh

/-- **No lot but the closings' lays a half of the kind K10.** -/
theorem lots_k10 (Z : ProofFile.Pub) (G : ProofFile.Ground) :
    ∀ M ∈ baseFill.lots, ∀ g ∈ M.halves Z G, g.place.kind = KindName.K10 →
      M = closeLotAt matrixInput OnBytes.HonestTrace.Sz.ref := by
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
    have hno : KindName.K10 ∉ (widerPairs matrixInput OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref
        openHonest).map (·.2) := by
      simp [widerPairs]
    exact (hno (List.mem_map.2 ⟨q, hq, hk.symm⟩)).elim
  · rfl
  · have hk := proxLotAt_kinds matrixInput OnBytes.HonestTrace.Sz.ref Z G g hg
    rw [e] at hk
    cases hk
  · have hk := AtFullSide.K12.wHalf_place matrixInput OnBytes.secondHashFunction openHonest Z G g hg
    rw [hk] at e
    cases e

/-- **`KindPays .K10` at `theSides` over `overlaySlots`**, at any `mine` that holds the closings' lot. -/
theorem kindPays_K10_sides {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (mine : Lots₀)
    (named : ∀ s ∈ mine, baseFill.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ baseFill.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A₀.Z A₀.G).map (·.half) = L.halves A₀.Z A₀.G)
    (hc : closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref ∈ mine)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey))
    (hs : shared.map (·.half) = baseFill.shared A₀.Z A₀.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)) (h₃ : second.map (·.half) = baseFill.second A₀.Z A₀.G)
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
      KindName.K10 := by
  obtain ⟨-, c₂, c₃⟩ := cuts_at_return hS hL hA
  refine ⟨?_, ?_, ?_⟩
  · intro L hLm hk σ hσ
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    obtain ⟨l, hl, hrl⟩ := List.mem_flatMap.1 hr
    obtain ⟨M, hM, rfl⟩ := List.mem_map.1 hl
    have hh : r.half ∈ M.halves A₀.Z A₀.G := by
      rw [← overlay_half (hm M hM)]
      exact List.mem_map.2 ⟨r, hrl, rfl⟩
    have e := lots_k10 A₀.Z A₀.G M hM _ hh hk
    subst e
    have ef : (mine.find? fun s => s.name ==
        (closeLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).name) =
        some (closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) :=
      OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mine apart _ hc
    have eo : overlayLot mine (closeLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref) =
        closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref := by
      unfold overlayLot
      rw [ef]
    rw [eo] at hrl
    cases hc' : ProofFile.onlineFirstChainAt A₀.Z with
    | error e =>
      have hnil : (closingsSLotAt (X := Unit) matrixInput OnBytes.HonestTrace.Sz.ref).rows A₀.Z A₀.G =
          [] := by
        show (match ProofFile.onlineFirstChainAt A₀.Z with
          | .ok _ => _
          | .error _ => []) = []
        rw [hc']
      rw [hnil] at hrl
      cases hrl
    | ok c =>
      rw [closingsSLotAt_ok matrixInput OnBytes.HonestTrace.Sz.ref A₀.G hc'] at hrl
      obtain ⟨Q, hQ, rfl⟩ := List.mem_map.1 hrl
      exact ProofFile.Honest.K10.Slot.closing_hand_at_return h hA _ .own _ 0 0 _ _ _ _ A₀.G Q hQ T₁ S₁ σ hσ
  · intro L _ hk σ hσ
    exact (no_side (no_kind_of_cut c₂ cuts_kinds.2.1) hk hσ).elim
  · intro L _ hk σ hσ
    exact (no_side (no_kind_of_cut c₃ cuts_kinds.2.2) hk hσ).elim

/-- **`KindPays .K14` at `theSides` over `overlaySlots`**, at any `mine`, at shared rows of that kind that
are the six and last rows of no row of that kind. -/
theorem kindPays_K14_sides {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀)
    (mine : Lots₀)
    (named : ∀ s ∈ mine, baseFill.lots.any (fun L => L.name == s.name) = true)
    (apart : (mine.map (·.name)).Nodup)
    (hm : ∀ L ∈ baseFill.lots, ∀ s, (mine.find? fun s => s.name == L.name) = some s →
      (s.rows A₀.Z A₀.G).map (·.half) = L.halves A₀.Z A₀.G)
    (shared : List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey))
    (hs : shared.map (·.half) = baseFill.shared A₀.Z A₀.G)
    (second : List (Unlettered (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit
      ProofFile.Inst)) (h₃ : second.map (·.half) = baseFill.second A₀.Z A₀.G)
    (hsh : ∀ r ∈ shared, r.place.kind = KindName.K14 → r ∈ baseRows A₀.Z Np)
    (hse : ∀ r ∈ second, r.place.kind = KindName.K14 → False)
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
      KindName.K14 := by
  obtain ⟨c₁, -, -⟩ := cuts_at_return hS hL hA
  refine ⟨?_, ProofFile.Honest.K14.kind_clause_at_return h hA (matrixInput.weights A₀.Z)
    (ProofFile.Honest.K14.randNow (ProofFile.Honest.K14.qAt A₀.Z Np)) _ KindName.K14 ?_, ?_⟩
  · intro L _ hk σ hσ
    exact (no_side (no_kind_of_cut c₁ cuts_kinds.1) hk hσ).elim
  · intro L hLm hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    exact ⟨r, hsh r hr hk, rfl, rfl, rfl, rfl⟩
  · intro L hLm hk
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hLm
    exact (hse r hr hk).elim

/-- **Our rows at a base return.** -/
noncomputable def slotsOurs {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
    {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place} (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit)
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀) : RowSlots baseFill A₀.Z A₀.G :=
  overlaySlots baseFill A₀.Z A₀.G mineOurs mine_named mine_apart (mine_hm _ _)
    (sharedOurs A₀.Z Np A₀.G) (shared_fit h _) (secondOurs _ _) (second_fit _ _)

section
variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place} {A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit}
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

/-- **A G at our rows, nine lots bare: not the G of the zero-knowledge theorem.** The falls are letters
here: the road takes the lists. -/
noncomputable abbrev gOurs (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀) :
    Sides A₀.F A₀.B FullSizeMatrix IndexCommitterCoins TableKey Cells Unit Unit :=
  theSides A₀.F (Letters.ofThreads A₀.F T₁ T₂ T₃ S₁ S₂ S₃) (slotsOurs A₀ h).rows f₁ f₂ f₃

/-- **`KindPays .K1` at `gOurs`.** -/
theorem gOurs_K1 (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀) :
    VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K1 :=
  kindPays_K1_sides h hS hL hA mineOurs mine_named mine_apart (mine_hm _ _)
    (OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mineOurs mine_apart _
      (List.mem_cons_self ..))
    (OnBytes.SendSim.Seat.find_of_nodup (fun s : SLot _ _ _ _ => s.name) mineOurs mine_apart _
      (by simp [mineOurs]))
    (sharedOurs A₀.Z Np A₀.G) (shared_fit h _) (secondOurs _ _) (second_fit _ _)
    (rows_of_shared _ _ _ KindName.K1 (by decide)) T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃

/-- **`KindPays .K10` at `gOurs`.** -/
theorem gOurs_K10 (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀) :
    VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K10 :=
  kindPays_K10_sides h hS hL hA mineOurs mine_named mine_apart (mine_hm _ _)
    (List.mem_cons_of_mem _ (List.mem_cons_self ..)) _ (shared_fit h _) _ (second_fit _ _)
    T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃

/-- **`KindPays .K14` at `gOurs`.** -/
theorem gOurs_K14 (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀)
    (hS : VerifierAndGoals.InScope files = true) (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles files) = true)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction files.pol files.lay files.KL baseFill = .ok A₀) :
    VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K14 :=
  kindPays_K14_sides h hS hL hA mineOurs mine_named mine_apart (mine_hm _ _) _ (shared_fit h _) _
    (second_fit _ _) (rows_of_shared _ _ _ KindName.K14 (by decide))
    (fun r hr hk => by
      have h2 := second_k12 _ _ r hr
      rw [hk] at h2
      cases h2)
    T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃

end

/-- **At three public files**: the base returns, and at `gOurs` our kinds pay. -/
def GOursAt (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (D : OnBytes.Maker.WholeD) (r₀ : LPFD.Full.RunPF) (Np : H2U.Places4)
    (cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl)
    (x₀ : VerifiableInference.Desc.First.Look.Place) (A₀ : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit)
    (h : P5J.AtMgA OnBytes.secondHashFunction files D r₀ A₀.Z Np cF x₀),
    ProofFile.Honest.Term.baseMaker files = .ok A₀ ∧
    ∀ (T₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread A₀.B A₀.F.S₁ A₀.F.Cl
        (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
      (T₂ : Common FullSizeMatrix IndexCommitterCoins TableKey → Thread A₀.B A₀.F.S₂ A₀.F.Cl Empty
        (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
      (T₃ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Thread A₀.B A₀.F.S₃ A₀.F.Cl
        (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit ProofFile.Inst)
      (S₁ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins A₀.B →
        Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
      (S₂ : Common FullSizeMatrix IndexCommitterCoins TableKey → Nat → Coins A₀.B →
        Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Prop)
      (S₃ : Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells → Nat → Coins A₀.B →
        Mid (Local FullSizeMatrix IndexCommitterCoins ProofFile.Inst Cells) Unit → Prop)
      (f₁ : List (Fall A₀.F.S₁)) (f₂ : List (Fall A₀.F.S₂)) (f₃ : List (Fall A₀.F.S₃)),
      VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K1 ∧
        VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K14 ∧
        VerifiableInference.Compilation.KindPays (gOurs T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h) KindName.K10

/-- **At the named files, under no premise.** The threads, the letters and the falls are any: the road
takes the falls. No kind's clause here says anything of the other kinds' lots, which stand bare. -/
theorem gOurs_named (files : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles files) : GOursAt files := by
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
  subst eZ
  exact ⟨_, _, Np, cF, x₀, A, h, hA, fun T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ =>
    ⟨gOurs_K1 T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h hS live hA, gOurs_K14 T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h hS live hA,
      gOurs_K10 T₁ T₂ T₃ S₁ S₂ S₃ f₁ f₂ f₃ h hS live hA⟩⟩

end AtFullSide.M1

#print axioms AtFullSide.M1.gOurs_named
#print axioms AtFullSide.M1.gOurs_K1
#print axioms AtFullSide.M1.gOurs_K14
#print axioms AtFullSide.M1.gOurs_K10
#print axioms AtFullSide.M1.kindPays_K10_sides
#print axioms AtFullSide.M1.kindPays_K14_sides
#print axioms AtFullSide.M1.mine_hm
#print axioms AtFullSide.M1.shared_fit
#print axioms AtFullSide.M1.second_fit
