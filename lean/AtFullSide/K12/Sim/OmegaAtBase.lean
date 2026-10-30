-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the condition at the base filling.
/-
AtFullSide/K12/Sim/OmegaAtBase.lean: AT THE RETURN OF `baseMaker` (E2E/BaseMaker.lean), the filling that `onlineFilling` reads through, at a run of its own prover: `onOmega_at_side` (SimO/OnAtSide.lean) with the prover's halves, its key and its book paid.

  `find_of_twice`     where no two halves stand at one place the search finds a half at its own place
  `twice_of_ready`    `ready` says that
  `OmegaOnAtBase`     what is said, as one proposition
  `omega_on_at_base`  under the head at the files' own data, where the verifier's test on the files accepts
  `omega_on_at_base_named`, `omega_on_at_base_zFull`   **at either named set; at the stored files, under no premise**
  `rowsAtOmega_at_head`, `omega_row_good`   the list's one row under the head; `Good` at a row of the list
  `OmegaGoodAtBase`, `omega_good_at_base`, `omega_good_at_base_named`, `omega_good_at_base_zFull`   `Good` at the seated side, at A := False, under `noneSpent` at the two addresses: a premise, for `noneSpent_at_maker`

What is left at a run: the clause `asks`: `ShapeAsksO` and `DataAsks`. `ready`, `runC`, that the part is called and that the challenges fit are the run's.

Limits. A conditional on `asks`, at the base filling, not read through: the crossing to `onlineFilling` is not here. `Good` is at A := False: `plays` and `acc` are met for nothing, `exact` is conditional on `OnOmega`, and no member of `OnOmega` is shown. `noneSpent` is a premise there. No property of the protocol is claimed.
-/
import E2E.BaseMaker
import AtFullSide.K14.Sim.AtBase
import Johnson.Desc.K14.Law.SharedConstTests
import Johnson.Desc.ProofFile.Honest.K12.SimO.OnAtSide

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open OnBytes (TableKey)
open VerifiableInference.Desc (Chain Block)
open Desc.K14 (St blocks)
open ProofFile.Honest.K14
open ProofFile.Honest.K12 ProofFile.Honest.K12.Light
open ProofFile.Honest.K12.AtProof (halfU halfO sharedWithUO fourOf simulatorJobAtOmega jobOmegaReal)
open VerifierAndGoals (asDescriptionFiles)
open FlashProve (protocolDataWellFormed theProofRun)
open VerifierAndGoals.AtTheName (dpZ)

/-- **The search at a place where no two halves stand.** -/
theorem find_of_twice {V W X : Type} (hs : List (Placed V W X)) (h : twice hs = []) (g : Placed V W X)
    (hg : g ∈ hs) : hs.find? (fun x => x.place == g.place) = some g := by
  have hone : (hs.filter fun x => x.place == g.place).length ≤ 1 := by
    by_contra hn
    have hm : g.place ∈ (hs.map (·.place)).filter fun a => 1 < (hs.filter fun x => x.place == a).length :=
      List.mem_filter.2 ⟨List.mem_map_of_mem hg, by simpa using Nat.lt_of_not_le hn⟩
    unfold twice at h
    have := List.mem_eraseDups.2 hm
    rw [h] at this
    cases this
  have hsome : (hs.find? fun x => x.place == g.place).isSome = true :=
    List.find?_isSome.2 ⟨g, hg, beq_self_eq_true _⟩
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hsome
  have hy1 : y ∈ hs := List.mem_of_find?_eq_some hy
  have hy2 : (y.place == g.place) = true := by
    have := List.find?_some hy
    simpa using this
  have m1 : y ∈ hs.filter fun x => x.place == g.place := List.mem_filter.2 ⟨hy1, hy2⟩
  have m2 : g ∈ hs.filter fun x => x.place == g.place := List.mem_filter.2 ⟨hg, beq_self_eq_true _⟩
  cases hl : hs.filter (fun x => x.place == g.place) with
  | nil =>
    rw [hl] at m1
    cases m1
  | cons a l =>
    rw [hl] at hone m1 m2
    have hl0 : l = [] := by
      cases l with
      | nil => rfl
      | cons b l' => simp at hone
    subst hl0
    obtain rfl := List.mem_singleton.1 m1
    obtain rfl := List.mem_singleton.1 m2
    exact hy

/-- `ready` says that no two halves stand at one place of the shared chain. -/
theorem twice_of_ready {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : VerifiableInference.Desc.FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hR : ready F Bk P w₀ rc x k = .ok R) : twice P.shared = [] := by
  have h := (ready_ok hR).1
  unfold readyTests at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i h2
      have h3 : (twice P.first ++ twice P.shared ++ twice P.second).isEmpty = true := by
        cases hx : (twice P.first ++ twice P.shared ++ twice P.second).isEmpty with
        | true => rfl
        | false =>
          rw [hx] at h2
          exact absurd rfl h2
      have h4 := List.isEmpty_iff.1 h3
      rw [List.append_eq_nil_iff, List.append_eq_nil_iff] at h4
      exact h4.1.2

variable {files : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **The condition at the test on G_omega at the base's return, at every run.** -/
def OmegaOnAtBase (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
    (returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (pO : VerifiableInference.Desc.K12.P12)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit),
    baseMaker files = .ok returned ∧ returned.Z = Zp ∧ returned.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧
    (fourOf Np).O = some pO ∧ blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
    ∀ (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey),
      Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder pO.place (omegaRow (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])) fs = some σ →
    ∀ (w₀ : FullSizeMatrix) (rc : IndexCommitterCoins) (x : ProofFile.Inst) (k : Coins returned.B) (ρ : Draws)
      (R : Ready FullSizeMatrix IndexCommitterCoins ProofFile.Inst TableKey Cells Unit Unit) (r : RunC (P5J.F0T OnBytes.secondHashFunction Zp Np cF)),
      ready (P5J.F0T OnBytes.secondHashFunction Zp Np cF) returned.B returned.H w₀ rc x k = .ok R →
      runC (P5J.F0T OnBytes.secondHashFunction Zp Np cF) returned.B returned.H w₀ rc x k ρ = .ok r →
      r.called ⟨σ.block.place, 1⟩ = true →
      drawsFit (P5J.F0T OnBytes.secondHashFunction Zp Np cF).roundsDeclaredByBlocks.2.1 ρ.shared = true →
    ∃ (c : RowCoins
        [(firstPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) : Part Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit).needsField,
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) : Part Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit).needsField])
      (m : Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit),
      midSharedAtW (P5J.F0T OnBytes.secondHashFunction Zp Np cF) returned.B returned.H w₀ rc x k ρ ⟨σ.block.place, 1⟩ =
        .ok (some m) ∧
      ProofFile.Honest.carriedAt returned.B k 1 ⟨σ.block.place, 1⟩
        (restPart (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) : ProofFile.Honest.Part Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit).needsField = .ok c.2.1.2.2 ∧
      m.st.input = ⟨w₀, rc, returned.H.key x⟩ ∧
      drawsFit (((H2K.JointK.laidOf (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO).p).take (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO).p.nums.stages)).map (·.1))
        (m.st.lately (firstLen (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO).p.nums.stages)) = true ∧
      ((∃ (Dp : H2K.First.Plain) (cc : ℕ → ℕ → List UInt64) (Rw : ProofFile.Honest.K12.PlainRows),
          Dp.ts.length = firstListAtOmega.length ∧
          ProofFile.Honest.K12.Own.ShapeAsksO (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) m.st.input (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) m)
            (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) m) H2K.Member.codesFull Dp ∧
          DataAsks (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) m.st.input (restFront (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) m)
            (carriedCoins (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (ProofFile.Honest.K12.stretches _ c.2.1.2.2)) (heardIn (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) m) Dp cc Rw) →
        OnOmega Face.shared (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) 1 firstListAtOmega
          (restMember (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) : Member Empty _ _ _).guarded c.2.1.2.2 m
          (r.run.beforeAt (storedShown (returned.H.storedWords w₀ rc) r.run.storedAsked) ⟨σ.block.place, 1⟩))

/-- **Under the head at the files' own data, where the verifier's test accepts.** -/
theorem omega_on_at_base
    (h : P5J.AtMgA OnBytes.secondHashFunction files (dpZ files) (theProofRun (asDescriptionFiles files)) Zp Np cF x₀)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) : OmegaOnAtBase files := by
  obtain ⟨A, hA, -, -, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest range_matrixInput
  obtain ⟨eZ, eF, -, -⟩ := six_at_atPure h hA
  obtain ⟨-, -, -, -, -, -, hkey, -, hS, -⟩ := atPure_ok hA
  have hm := h.toAtMg
  obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head hm
  obtain ⟨bs, hbs⟩ := blocks_head hm
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.Sh.blocks_eight_of hbs
  refine ⟨Zp, Np, cF, A, pO, b1, b2, b3, b4, b5, b6, b7, b8, hA, eZ, eF, hO, hbs, ?_⟩
  intro fs σ hσ w₀ rc x k ρ R r hR hrun hc hdue
  have hB : bookWhole (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Johnson.G.proofSendsFull.1 Johnson.G.proofSendsFull.2.1
      Johnson.G.proofSendsFull.2.2 (mergesByName (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder) = .ok A.B := by
    have hb := ProofFile.Honest.K14.atPure_book_at_head h hA
    have hs := ProofFile.Honest.K14.made_sends_at_files h.scope h.laid
    rw [hs] at hb
    exact hb
  have hshared : A.H.shared = sharedWithUO matrixInput Zp := by
    rw [hS, eZ]
    rfl
  have h6 := simRows_now (Pb := TableKey) h (matrixInput.weights Zp)
  have hU : sharedWithUO matrixInput Zp =
      (simRows (simData Zp Np) (simPub Zp Np) (matrixInput.weights Zp) (randNow (qAt Zp Np)) :
        List (Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)).map (·.half) ++
        halfU (matrixInput.weights Zp) (fun w => Bind.ForProver.encW Zp (matrixInput.weights Zp w)) Zp ++
        halfO (matrixInput.weights Zp) Zp := by
    unfold sharedWithUO
    rw [h6]
  have ht := twice_of_ready hR
  have hO' := ProofFile.Honest.K12.AtProof.halfO_at_head hm b1 b2 b3 b4 b5 b6 b7 b8 hbs (matrixInput.weights Zp) hO
  have hmemO : (proverSideOfProximityTest (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) : Placed Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit).needsField ∈ A.H.shared := by
    rw [hshared, hU, hO']
    exact List.mem_append_right _ (List.mem_singleton.2 rfl)
  have hmemS : (⟨sendPlace 5, [(liftSend (askOf ⟨qAt Zp Np, 0⟩ (fun w : Common FullSizeMatrix IndexCommitterCoins TableKey => matrixInput.weights Zp w.w₀)
        (fun w => ProofFile.Honest.K12.AtProof.randAt (qAt Zp Np) w.rc)) (sendingPart (jobOmega ⟨qAt Zp Np, 0⟩)) :
        Part Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit)]⟩ : Placed Empty _ Unit) ∈ A.H.shared := by
    rw [hshared, hU, simRows_half]
    refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    rw [sendHalves_eq]
    exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl)
  have hpl : σ.block.place = pO.place := (side_omega hm hO _ _ _ none (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl fs σ hσ).2.2.2.2.1
  have hg := find_of_twice A.H.shared ht _ hmemO
  have hgO := find_of_twice A.H.shared ht _ hmemS
  refine onOmega_at_side hm hO b1 b2 b3 b4 b5 b6 b7 b8 hbs hB (fun x => ?_) (matrixInput.weights Zp) hR fs σ hσ hrun hc
    (by rw [hpl]; exact hg) hgO hdue
  rw [hkey]
  rfl

/-- **At either named set, under no premise.** -/
theorem omega_on_at_base_named (files : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles files) : OmegaOnAtBase files := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named files hZ
  exact omega_on_at_base h (AtFullSide.K14.live_named files hZ)

/-- **AT THE STORED FILES, UNDER NO PREMISE.** -/
theorem omega_on_at_base_zFull : OmegaOnAtBase VerifierAndGoals.storedPublicFiles := omega_on_at_base_named _ (Or.inl rfl)

/-- **The row of the list, under the head.** -/
theorem rowsAtOmega_at_head (h : P5J.AtMg OnBytes.secondHashFunction files D r₀ Zp Np cF) {pO : VerifiableInference.Desc.K12.P12}
    (hO : (fourOf Np).O = some pO) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) :
    ProofFile.Honest.K12.AtProof.rowsAtOmega (matrixInput.weights Zp) Zp =
      [ProofFile.Honest.K12.AtProof.rowAtOmega (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])] := by
  unfold ProofFile.Honest.K12.AtProof.rowsAtOmega
  rw [(ProofFile.Honest.K12.Light.stages_at_head h).1, ProofFile.Honest.K12.AtProof.sendPub_at_head h b1 b2 b3 b4 b5 b6 b7 b8 hb]
  simp only [Option.bind_some, hO, hb, Option.map_some, Option.toList_some]
  rfl

/-- **`Good` at a row of the list with simulators, at the base's return.** -/
theorem omega_row_good
    (h : P5J.AtMgA OnBytes.secondHashFunction files (dpZ files) (theProofRun (asDescriptionFiles files)) Zp Np cF x₀)
    (hB : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (ord : List VerifiableInference.Desc.Place)
    (r : Unlettered Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hr : r ∈ ProofFile.Honest.K12.AtProof.rowsAtOmega (matrixInput.weights Zp) Zp)
    (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey)
    (hσ : Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder r.place r.row fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (B : Coins hB.B → St → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Env → Prop)
    (hnone : ∀ u ∈ σ.members, ProofFile.Honest.Small.noneSpent hB.B ⟨σ.block.place, u.number⟩ = true) :
    Good pre Face.shared σ hB.B ord 1 0 (fun _ _ _ _ => False) B r.On r.bud := by
  have hm := h.toAtMg
  obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head hm
  obtain ⟨bs, hbs⟩ := blocks_head hm
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.Sh.blocks_eight_of hbs
  rw [rowsAtOmega_at_head hm hO b1 b2 b3 b4 b5 b6 b7 b8 hbs, List.mem_singleton] at hr
  subst hr
  exact omega_good hm hO _ _ _ none (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl fs σ hσ pre Face.shared 1 0 rfl hB.B ord B hnone

/-- **`Good` at the base's return, at the seated side of the row, at A := False.** -/
def OmegaGoodAtBase (files : VerifierAndGoals.PublicFiles) : Prop :=
  ∃ (Zp : ProofFile.Pub) (Np : H2U.Places4) (cF : Chain P5J.TS ProofFile.Cl)
    (returned : OnlineProverWithDescription FullSizeMatrix IndexCommitterCoins Cells Unit Unit) (pO : VerifiableInference.Desc.K12.P12)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit),
    baseMaker files = .ok returned ∧ returned.Z = Zp ∧ returned.F = P5J.F0T OnBytes.secondHashFunction Zp Np cF ∧
    (fourOf Np).O = some pO ∧ blocks (qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8] ∧
    ∀ (fs : List (Fall St)) (σ : Side St ProofFile.Cl Empty (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit TableKey),
      Side.seated (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder pO.place (omegaRow (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8])) fs = some σ →
    ∀ (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (B : Coins returned.B → St → Mid (Common FullSizeMatrix IndexCommitterCoins TableKey) Unit → Env → Prop),
      (∀ u ∈ σ.members, ProofFile.Honest.Small.noneSpent returned.B ⟨σ.block.place, u.number⟩ = true) →
      Good pre Face.shared σ returned.B (orderOf returned.F) 1 0 (fun _ _ _ _ => False) B
        (OnOmega Face.shared (jobOmegaReal Zp Np [b1, b2, b3, b4, b5, b6, b7, b8] (matrixInput.weights Zp) pO) (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) 1 firstListAtOmega) (budBoth (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]))

/-- **Under the head at the files' own data, where the verifier's test accepts.** -/
theorem omega_good_at_base
    (h : P5J.AtMgA OnBytes.secondHashFunction files (dpZ files) (theProofRun (asDescriptionFiles files)) Zp Np cF x₀)
    (live : protocolDataWellFormed (asDescriptionFiles files) = true) : OmegaGoodAtBase files := by
  obtain ⟨A, hA, -, -, -⟩ := AtFullSide.K12.atPure_returns_fillW_at h live matrixInput
    OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest range_matrixInput
  obtain ⟨eZ, eF, -, -⟩ := six_at_atPure h hA
  have hm := h.toAtMg
  obtain ⟨pO, hO⟩ := ProofFile.Honest.K12.AtProof.someO_at_head hm
  obtain ⟨bs, hbs⟩ := blocks_head hm
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := Desc.K14.Law.Sh.blocks_eight_of hbs
  refine ⟨Zp, Np, cF, A, pO, b1, b2, b3, b4, b5, b6, b7, b8, hA, eZ, eF, hO, hbs, ?_⟩
  intro fs σ hσ pre B hnone
  exact omega_good hm hO _ _ _ none (simulatorJobAtOmega Zp.p.chains (qAt Zp Np) (fourOf Np).U pO [b1, b2, b3, b4, b5, b6, b7, b8]) rfl rfl fs σ hσ pre Face.shared 1 0 rfl A.B (orderOf A.F) B hnone

/-- **At either named set, under no premise.** -/
theorem omega_good_at_base_named (files : VerifierAndGoals.PublicFiles) (hZ : VerifierAndGoals.NamedFiles files) : OmegaGoodAtBase files := by
  obtain ⟨Zp, Np, cF, x₀, h⟩ := AtFullSide.Top.headMember_named files hZ
  exact omega_good_at_base h (AtFullSide.K14.live_named files hZ)

/-- **AT THE STORED FILES, UNDER NO PREMISE.** -/
theorem omega_good_at_base_zFull : OmegaGoodAtBase VerifierAndGoals.storedPublicFiles := omega_good_at_base_named _ (Or.inl rfl)

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.rowsAtOmega_at_head
#print axioms ProofFile.Honest.Term.omega_row_good
#print axioms ProofFile.Honest.Term.omega_good_at_base_zFull
#print axioms ProofFile.Honest.Term.omega_on_at_base
#print axioms ProofFile.Honest.Term.omega_on_at_base_named
#print axioms ProofFile.Honest.Term.omega_on_at_base_zFull
#print axioms ProofFile.Honest.Term.find_of_twice
#print axioms ProofFile.Honest.Term.twice_of_ready
