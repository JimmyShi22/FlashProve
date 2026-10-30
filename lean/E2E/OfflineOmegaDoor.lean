-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaDoor.lean: THE ROW OF THE KEY FILE's TEST ON G_omega (⟨2, –, 10⟩): THE CLAUSE door AT A RUN IS PAID (`DoorAtRun`,
E2E/OfflineOmegaOwed.lean) at every simulators' job whose state on entry is `stateAtOmega`
(Johnson/Desc/ProofFile/Honest/K12/SimO/DoorOmega.lean) at the written parameters, over the sub-protocols that the description's own shared
list has in front of the test. So of what is owed at the row ONE named sentence stays: `SayAtRun`
(E2E/OfflineSayAtRun.lean).

  `front_is_takeWhile`   where places are apart, what stands in front of a member is the list up to that member's place
  `state_of_fold`        the simulators' state on entry where the fold over the sub-protocols in front returns
  `omega_door_at_run`    the clause door at a run: by `door_key_at_omega` (…/K12/SimO/KeyRun.lean) and
                         `stateFromViewOnSharedChain_at_stand` (…/K12/SimO/Door.lean): both sides are what the way in makes of the
                         state that the fold over the sub-protocols in front returns
  `omega_owed_of_say`    `owedAt` at the muted row, at the muted rows' prover, from `SayAtRun` alone

New premises: the prover's reader of the key returns the instance's key; the simulators' job's state on entry is that term.

Limits. Conditional on `SayAtRun`: no value is shown to meet it; it reads the input and the carried coins: no later law may
take it as a hypothesis on a run and then speak of the coins as drawn anew. That a run returns, or calls a part, is
not shown here. At the written sizes. Nothing on any property.
-/
import E2E.OfflineOmegaClosed

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Own
open ProofFile.Honest.K12.Light (plainMany budBoth OnOmegaKey eight_of askOf sentOf stateAtOmega fallOmega flat_ten_key
  start_key door_key_at_omega rounds_like)
open ProofFile.Honest.K14 (SendPub sendPlace jobOmega sendingPart liftSend)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block FileDescription)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open VerifiableInference.Desc.Key (Source LaterPlaces keyAsProof sharedPar beforeSharedPoint)
open _root_.Desc.K14 (St blocks first frontBlock)
open H2K.Member (piKOFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnOmega bsOf wtOf rdOf)
open AtPublicFiles.KeyValueHolds (place_p12At)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **Where places are apart, what stands in front of a member is the list up to that member's place.** -/
theorem front_is_takeWhile {S Cl : Type} : ∀ {pre t : List (Block S Cl)} {b : Block S Cl},
    ((pre ++ b :: t).map (·.place)).Nodup → (pre ++ b :: t).takeWhile (·.place != b.place) = pre
  | [], t, b, _ => by
    show (b :: t).takeWhile _ = []
    exact List.takeWhile_cons_of_neg (by simp)
  | a :: p, t, b, hn => by
    have hn' : (a.place :: (p ++ b :: t).map (·.place)).Nodup := hn
    have hne : a.place ≠ b.place := by
      intro e
      refine (List.nodup_cons.1 hn').1 ?_
      rw [e]
      exact List.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self)
    show (a :: (p ++ b :: t)).takeWhile _ = _
    rw [List.takeWhile_cons_of_pos (by simpa using hne), front_is_takeWhile (List.nodup_cons.1 hn').2]

/-- The simulators' state on entry, where the front lists the columns and the fold over the sub-protocols in front
returns. -/
theorem state_of_fold {S Cl Pb : Type} (pre : List (Block S Cl)) (start : Pb → S)
    (enter : S → Except String T12) (fall : T12) (pb : Pb) (f : Before)
    (cs : List VerifiableInference.Desc.OpenedColumn) (s : S)
    (hc : Sim2.columnsOfChain f 1 0 (pre.flatMap (·.rounds)) = some cs)
    (hf : VerifiableInference.Desc.foldBlocks 0 pre (start pb) (Sim2.roundsOfChain f 1) cs = .ok (s, [], [])) :
    Sim2.stateFromViewOnSharedChain pre start enter fall pb f = (enter s).toOption.getD fall := by
  unfold Sim2.stateFromViewOnSharedChain Sim2.doorFromViewOnSharedChain
  rw [hc]
  dsimp only
  rw [hf]
  rfl

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **THE CLAUSE door AT A RUN, at the called second part of the test on G_omega.** -/
theorem omega_door_at_run (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (hkey : ∀ x, H.key x = x.key)
    (Js : SimJob TableKey)
    (hJr : Js.rec₀ = stateAtOmega QK (sentOf QK.S) pU
      ((keyFileDescription Xs N Pl).shared.blocksInOrder.takeWhile (·.place != omegaTestPlace)))
    {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) :
    DoorAtRun (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨omegaTestPlace, 1⟩) := by
  subst hA
  obtain ⟨B, rfl⟩ := eight_of QK bs hb
  intro hc m hm
  have plan := hs.named.plan
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
  have hOp : K.onOmega.place = omegaTestPlace := by
    rw [hO, hpO]
    exact place_p12At _ _
  obtain ⟨L, hL, hp⟩ : ∃ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace :=
    ⟨_, List.mem_map.2 ⟨K.onOmega,
      List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self), rfl⟩, hOp⟩
  obtain ⟨b₀, hbm, hbp₀⟩ := (sharedTests_there hs scope).2
  obtain ⟨σ, hσ⟩ : ∃ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ := by
    have hsome : ((keyFileDescription Xs N Pl).shared.blocksInOrder.find? fun b => b.place == L.place).isSome = true :=
      List.find?_isSome.2 ⟨b₀, hbm, by rw [hbp₀, hp]; exact beq_self_eq_true _⟩
    obtain ⟨b', hb'⟩ := Option.isSome_iff_exists.1 hsome
    refine ⟨⟨b', L.row, fallOf [] L.place⟩, ?_⟩
    unfold Lettered.side Side.seated
    rw [hb']
    rfl
  obtain ⟨⟨-, -, hparts⟩, hlaid, s, next, rest, hst⟩ :=
    omega_row_form hs scope K hsp hU _ pU pO hpO _ weights rand hO S c L hL hp
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts h
  obtain ⟨s0, s1, hmem⟩ := guarded_row_members plan book hR hL hσ _ hparts (hlaid σ hσ) s next rest hst
  have hbp : σ.block.place = L.place := side_place hσ
  obtain ⟨-, hstand⟩ := shared_stands plan book hR L hL σ hσ
  obtain ⟨⟨pre, t, A⟩, -⟩ := hstand _ (by
    rw [hmem]
    exact List.mem_cons_of_mem _ (List.mem_singleton.2 rfl))
  have hrowσ : σ.row = L.row := OnBytes.SendSim.Seat.row_of_seated hσ
  obtain ⟨q0, q1, hrow⟩ := two_of_map hparts
  have hto : σ.roundsTo 1 = firstLen (jobKO (X := Unit) ⟨QK, 0⟩ pU pO
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] weights rand).toRun.toTest.p.nums.stages := by
    unfold Side.roundsTo
    rw [hrowσ, hrow]
    simp [needsField_length, Light.first_moves_len]
  have A' := StandsAt.of_same (u' := _) rfl rfl hto A
  have h10 := omega_front_ten hs scope A.cut (hbp.trans hp) hb rfl
  have e : sharedPar Xs.chains (beforeSharedPoint Pl) = QK := par_sourced hs scope
  have hPl : Pl = PF := later_sourced hs scope
  have eK : ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).key x = x.key := by
    rw [offlineRows_prover_at]
    exact hkey x
  have eS : ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).storedWords = H.storedWords := by
    rw [offlineRows_prover_at]
    rfl
  have hstart : (keyFileDescription Xs N Pl).start₂ ((keyFileDescription Xs N Pl).pub x) =
      first QK.codes (((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).key x) := by
    rw [eK, ← e]
    exact start_key Xs N Pl _ x
  obtain ⟨pre₀, tl, e0, hl, hLike⟩ := flat_ten_key (Cl := VerifiableInference.Desc.Key.Claim)
    (keyAsProof Xs.chains) QK Pl B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 hb
  have e' : (keyFileDescription Xs N Pl).shared.blocksInOrder = pre₀ ++ tl := by
    show ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
      (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder = _
    rw [VerifiableInference.Desc.Key.sharedChain_flat_eq_chainOf_flat, e]
    exact e0
  have hpp : pre = pre₀ := h10.trans ((congrArg (List.take 10) e').trans (List.take_left' hl))
  have hpU' : H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ Pl.U = pU := by
    rw [hpU, hPl]
    rfl
  rw [hpU', ← hpp] at hLike
  have hc' : r.called ⟨σ.block.place, 1⟩ = true := by
    rw [hbp, hp]
    exact hc
  obtain ⟨m₁, hm₁, hd⟩ := door_key_at_omega plan hR h σ _ pre t _ A' hc' (keyAsProof Xs.chains) QK
    (sentOf QK.S) [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] pU hLike hstart
    (jobKO (X := Unit) ⟨QK, 0⟩ pU pO [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] weights
      rand).toRun.toTest rfl
  obtain ⟨m₂, s₂, cols, hm₂, hin, -, -, hfold, hrd, hcl, hstate⟩ :=
    Sim2.stateFromViewOnSharedChain_at_stand plan hR h σ _ pre t _ A' hc' (first QK.codes)
      (VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) (fallOmega QK (sentOf QK.S) pU)
      (((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).key x) hstart.symm
  rw [hbp, hp] at hm₁ hm₂ hd hrd hcl hstate
  dsimp only at hm₁ hm₂ hd hrd hcl hstate
  obtain rfl : m₁ = m := Option.some.inj (Except.ok.inj (hm₁.symm.trans hm))
  obtain rfl : m₂ = m₁ := Option.some.inj (Except.ok.inj (hm₂.symm.trans hm))
  rw [hstart] at hfold
  have hLr := rounds_like hLike
  have hf' := _root_.Desc.K14.Honest.fold_like 0 _ _ hLike _ _ _ _ hfold
  have hB1 : stateAtOmega QK (sentOf QK.S) pU (frontBlock (keyAsProof Xs.chains) ::
      ([B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] ++
        [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)]))
      (((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).key x)
      ((r.run.beforeAt (storedShown (((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).storedWords w₀ rc)
        r.run.storedAsked) ⟨omegaTestPlace, 1⟩).cut (firstLen (jobKO (X := Unit) ⟨QK, 0⟩ pU pO
          [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] weights rand).toRun.toTest.p.nums.stages)) =
      ((VerifiableInference.Desc.K12.Seat.enter (·.gOmega) fun _ => none) s₂).toOption.getD
        (fallOmega QK (sentOf QK.S) pU) := by
    refine state_of_fold _ _ _ _ _ _ cols s₂ ?_ ?_
    · exact (congrArg (Sim2.columnsOfChain _ 1 0) hLr).trans hcl
    · exact (congrArg (fun Rs => VerifiableInference.Desc.foldBlocks 0 (frontBlock (keyAsProof Xs.chains) ::
        ([B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] ++
          [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)]))
        (first QK.codes (((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).key x)) Rs cols) hrd).trans hf'
  have hfront : (keyFileDescription Xs N Pl).shared.blocksInOrder.takeWhile (·.place != omegaTestPlace) = pre := by
    have hn : ((pre ++ σ.block :: t).map (·.place)).Nodup := by
      rw [← A.cut]
      subst hPl
      exact sharedPlaces_nodup hs scope
    rw [A.cut, ← hp, ← hbp]
    exact front_is_takeWhile hn
  have hpub : (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub m₂.st.input =
      ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).key x := by
    rw [hin]
    rfl
  have hJr' : Js.rec₀ = stateAtOmega QK (sentOf QK.S) pU pre :=
    hJr.trans (congrArg (stateAtOmega QK (sentOf QK.S) pU) hfront)
  rw [hJr', hpub, ← eS]
  exact hd.trans (hB1.trans hstate.symm)

/-- **`owedAt` AT THE MUTED ROW OF THE TEST ON G_omega, FROM `SayAtRun` ALONE**: the form of the field owed. -/
theorem omega_owed_of_say (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hA : K.send = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U))
    (hO : K.onOmega = proverSideOfTestOnOmega K.send pU pO (bsOf K) (wtOf K) (rdOf K)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (hkey : ∀ x, H.key x = x.key)
    (Js : SimJob TableKey)
    (hsim : S.testOnOmega = [firstSim Js, restSim Js]) (hJs : Js.p = piKOFull) (hown : Js.own = true)
    (hJr : Js.rec₀ = stateAtOmega QK (sentOf QK.S) pU
      ((keyFileDescription Xs N Pl).shared.blocksInOrder.takeWhile (·.place != omegaTestPlace)))
    (hOn : ∀ u ca m front,
      OnOmegaKey Face.shared (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest Js 1 u ca
        m front → (c.shared omegaTestPlace).atPart u ca m front)
    (hpos : ∀ n ds asks, budBoth Js n ds asks → (c.shared omegaTestPlace).positions n ds asks)
    {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ =
      .ok r)
    (say : SayAtRun Empty (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest
      (plainMany (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K))) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
        ρ)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, L.place = omegaTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  have hI : (blocks QK).isSome = true :=
    List.all_eq_true.1 ProofFile.Honest.K12.Light.KeyDoorUClosed.plan_U _ (by
            unfold ProofFile.Honest.K12.Light.KeyDoorUClosed.planU
            exact List.mem_cons_self)
  have hb : blocks QK = some (bsOf K) := by
    show blocks QK = some ((blocks K.send.P).getD [])
    rw [hA]
    exact some_getD hI _
  refine omega_owed_of_two hs scope live hK hB K hsp hU hA pU pO hpU hpO hO S c H Js hsim hJs hown hOn hpos due
    h say ?_
  rw [prover_mute] at h ⊢
  exact omega_door_at_run hs scope hK hB K hsp hU K.send hA pU pO hpU hpO (bsOf K) hb (wtOf K) (rdOf K) hO S c
    H hkey Js hJr h

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.front_is_takeWhile
#print axioms AtPublicFiles.OfflineRows.state_of_fold
#print axioms AtPublicFiles.OfflineRows.omega_door_at_run
#print axioms AtPublicFiles.OfflineRows.omega_owed_of_say
