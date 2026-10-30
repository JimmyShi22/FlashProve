-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaClosed.lean: THE ROW OF THE KEY FILE's TEST ON G_omega (⟨2, –, 10⟩): WHAT IS OWED AT A RUN, FROM TWO NAMED SENTENCES AT THAT
RUN: `SayAtRun` (E2E/OfflineSayAtRun.lean: hidden data) and `DoorAtRun` (E2E/OfflineOmegaOwed.lean: the job's state on entry is the
simulators' job's). The clause on the trees that the first round of positions opens, which E2E/OfflineOmegaBud.lean leaves as a
third premise, is paid by `onOmega_key_sourced` (Johnson/Desc/ProofFile/Honest/K12/SimO/KeyAt.lean), whose premises on the run's stand,
on the filling and on the book are paid here at the offline rows over parts that hold the senders' own letters.

  `cut_unique`            a list whose members are apart under a function is cut at a member in one way
  `omegaSending_found`    the prover's shared list finds the half that sends Omega, at the senders' own readers
  `omega_front_ten`       in scope, what stands in front of the test in the shared list is the list's first ten
  `omega_on_of_two_at`, `omega_on_of_two`   the condition at every member of the row, at a run's own values: columns are handed, and
                          `OnEntryOwn` at the written codes and the written list of trees (`OnOmegaKey`, …/K12/SimO/Key.lean)
  `omega_owed_of_two`     `owedAt` at the muted row, at the muted rows' prover: the form of the field owed

Premises beside the two: `KeySourced`, `InScope`, the public files' test, the written book; on the parts: K.send = ⟨QK, 0⟩, the
shape splits, the two tests' halves are the senders' own at the places' numbers; on the letters: as in
E2E/OfflineOmegaBud.lean. The stored words shown are the run's own.

Limits. Conditional on the two: no value is shown to meet them. Both read the input, the first the carried coins too: no
later law may take them as hypotheses on a run and then speak of the coins as drawn anew. That a run returns, or calls
a part, is not shown here. At the written sizes. Nothing on any property.
-/
import E2E.OfflineOmegaBud
import Johnson.Desc.ProofFile.Honest.K12.SimO.KeyAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Own
open ProofFile.Honest.K12.Light (plainMany budBoth firstListAtKey firstListAtKey_length AtKeyPlace OnOmegaKey
  onOmega_key_sourced eight_of askOf)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (cuts_O)
open ProofFile.Honest.K14 (SendPub sendPlace jobOmega sendingPart liftSend)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block FileDescription)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St blocks blocksOr)
open H2K.Member (piKUFull piKOFull codesKeyFull)
open H2K.JointK (keyGu keyOmega keySharedPre keyShared_cut_omega)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription flat₂)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced omega_full)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnOmega bsOf wtOf rdOf)
open AtPublicFiles.KeyNineClosed (place_full)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyValueHolds (place_p12At)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- **A list whose members are apart under a function is cut at a member in one way.** -/
theorem cut_unique {α β : Type} (f : α → β) : ∀ {pre pre' t t' : List α} {b : α},
    ((pre ++ b :: t).map f).Nodup → pre ++ b :: t = pre' ++ b :: t' → pre = pre'
  | [], [], _, _, _, _, _ => rfl
  | [], a :: p, t, t', b, hn, h => by
    have h' : b :: t = a :: (p ++ b :: t') := h
    obtain ⟨-, rfl⟩ := List.cons.inj h'
    have hn' : (f b :: (p ++ b :: t').map f).Nodup := hn
    exact absurd (List.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self))
      (List.nodup_cons.1 hn').1
  | a :: p, [], t, t', b, hn, h => by
    have h' : a :: (p ++ b :: t) = b :: t' := h
    obtain ⟨rfl, -⟩ := List.cons.inj h'
    have hn' : (f a :: (p ++ a :: t).map f).Nodup := hn
    exact absurd (List.mem_map_of_mem (List.mem_append_right _ List.mem_cons_self))
      (List.nodup_cons.1 hn').1
  | a :: p, a' :: p', t, t', b, hn, h => by
    have h' : a :: (p ++ b :: t) = a' :: (p' ++ b :: t') := h
    obtain ⟨rfl, h2⟩ := List.cons.inj h'
    have hn' : (f a :: (p ++ b :: t).map f).Nodup := hn
    rw [cut_unique f (List.nodup_cons.1 hn').2 h2]

/-- **The prover's shared list finds the half that sends Omega**, at the senders' own readers. -/
theorem omegaSending_found {W₀ Rc X₀ Y Wk : Type} (K : KeyParts W₀ Rc X₀ Y Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hO : K.onOmega.place = omegaTestPlace) :
    ((keyProver K).shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf K.send (wtOf K) (rdOf K)) (sendingPart (jobOmega K.send)) :
        Part Empty (Common W₀ Rc TableKey) X₀)]⟩ :=
  OnBytes.SendSim.Seat.find_of_nodup
    (fun g : Placed Empty (Common W₀ Rc TableKey) X₀ => g.place) _ (shared_nodup K hsp hU hO)
    (⟨sendPlace 5, [(liftSend (askOf K.send (wtOf K) (rdOf K)) (sendingPart (jobOmega K.send)) :
      Part Empty (Common W₀ Rc TableKey) X₀)]⟩ : Placed Empty (Common W₀ Rc TableKey) X₀)
    (List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ List.mem_cons_self))))

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **In scope, what stands in front of the test on G_omega in the shared list is the list's first ten.** -/
theorem omega_front_ten (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {pre t : List (Block St VerifiableInference.Desc.Key.Claim)}
    {b : Block St VerifiableInference.Desc.Key.Claim}
    (hcut : flat₂ Xs.chains Pl = pre ++ b :: t) (hp : b.place = omegaTestPlace)
    {bs : List (Block St Unit)} (hb : blocks QK = some bs) (h8 : bs.length = 8) :
    pre = (flat₂ Xs.chains Pl).take 10 := by
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  have e : parKey Xs PF = QK := par_sourced hs scope
  have hm : b ∈ flat₂ Xs.chains PF := by
    rw [hcut]
    exact List.mem_append_right _ List.mem_cons_self
  obtain rfl : b = keyOmega (PF.O.getD PF.U) := sharedBlock_omega hs scope b hm hp
  have h2 : flat₂ Xs.chains PF =
      (keySharedPre Xs.chains PF ++ [keyGu PF]) ++ keyOmega (PF.O.getD PF.U) ::
        [H2K.JointK.keySharedEnd Xs.chains PF] := keyShared_cut_omega Xs.chains PF _ omega_full
  have hn : ((pre ++ keyOmega (PF.O.getD PF.U) :: t).map (·.place)).Nodup := by
    rw [← hcut]
    exact sharedPlaces_nodup hs scope
  have e1 : pre = keySharedPre Xs.chains PF ++ [keyGu PF] :=
    cut_unique (·.place) hn (hcut.symm.trans h2)
  have hl : (keySharedPre Xs.chains PF ++ [keyGu PF]).length = 10 := by
    have eb : blocksOr (parKey Xs PF) = bs := by
      rw [e]
      unfold blocksOr
      rw [hb]
      rfl
    unfold keySharedPre
    rw [List.length_append, List.length_cons, List.length_map, eb, h8]
    rfl
  rw [e1, h2]
  exact (List.take_left' hl).symm

/-- **THE CONDITION AT EVERY MEMBER OF THE ROW, AT A RUN's OWN VALUES, FROM THE TWO NAMED SENTENCES**, at letters for the
senders' public part, the eight and the two readers. hgO: the prover's shared list holds the half that sends Omega,
at these letters. -/
theorem omega_on_of_two_at (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (hgO : ((keyProver K).shared.find? fun g => g.place == sendPlace 5) = some ⟨sendPlace 5,
      [(liftSend (askOf A weights rand) (sendingPart (jobOmega A)) :
        Part Empty (Common W₀ Rc TableKey) Unit)]⟩)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey) (hJs : Js.p = piKOFull)
    (hown : Js.own = true) {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws}
    {r : RunC (keyFileDescription Xs N Pl)} (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r)
    (say : SayAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest
      (plainMany (jobKO (X := Unit) A pU pO bs weights rand)) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ))
    (door : DoorAtRun (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      OnOmegaKey Face.shared (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js 1 u
        ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
          ⟨L.place, u.number⟩) := by
  subst hA
  obtain ⟨B, rfl⟩ := eight_of QK bs hb
  intro L hL hp σ hσ u hu hc ca m hca hm
  have plan := hs.named.plan
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
  refine ⟨opened_at_shared_row plan book h hL hσ hu hc hm, fun hn => ?_⟩
  have left := omega_left_at_run hs scope hK hB K hsp hU _ rfl pU pO hpU hpO _ hb weights rand
    hO S c H Js due h L hL hp σ hσ u hu hn hc ca m hca hm
  obtain ⟨⟨-, -, hparts⟩, hlaid, s, next, rest, hst⟩ :=
    omega_row_form hs scope K hsp hU _ pU pO hpO _ weights rand hO S c L hL hp
  obtain ⟨R, -, -, -, -, -, -, hR, -⟩ := runC_parts h
  obtain ⟨s0, s1, hmem⟩ := guarded_row_members plan book hR hL hσ _ hparts (hlaid σ hσ) s next rest hst
  have hbp : σ.block.place = L.place := side_place hσ
  obtain ⟨⟨hsum, hor⟩, hstand⟩ := shared_stands plan book hR L hL σ hσ
  obtain ⟨⟨pre, t, A⟩, -⟩ := hstand u hu
  have hrowσ : σ.row = L.row := OnBytes.SendSim.Seat.row_of_seated hσ
  obtain ⟨q0, q1, hrow⟩ := two_of_map hparts
  have hto : σ.roundsTo 1 = firstLen (jobKO (X := Unit) ⟨QK, 0⟩ pU pO
      [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] weights rand).toRun.toTest.p.nums.stages := by
    unfold Side.roundsTo
    rw [hrowσ, hrow]
    simp [needsField_length, Light.first_moves_len]
  rw [hmem] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl
  · exact absurd (show (0 : ℕ) = 1 from hn) (by decide)
  have h10 := omega_front_ten hs scope A.cut (hbp.trans hp) hb rfl
  have hOp : K.onOmega.place = omegaTestPlace := by
    rw [hO, hpO]
    exact place_p12At _ _
  have eP : ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).shared = (keyProver K).shared := by
    rw [offlineRows_prover_at]
  have eS : ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H).storedWords = H.storedWords := by
    rw [offlineRows_prover_at]
    rfl
  have e1 : pU = piKUFull := hpU.trans place_full
  have e2 : pO = piKOFull := hpO.trans omegaNumbers_written
  have hPl : Pl = PF := later_sourced hs scope
  have hd1 : drawsFit (keyFileDescription Xs N Pl).roundsDeclaredByBlocks.2.1 ρ.shared = true := by
    unfold Draws.due at due
    simp only [Bool.and_eq_true] at due
    exact due.1.1.2
  have hbk : Light.bookCutsOmega Bk ⟨QK, 0⟩ pO = true := by
    have h' := cuts_O
    unfold atFull at h'
    rw [hK] at h'
    rw [hB, e2]
    exact h'
  have hT : tiesOB Bk pO.place 2 = true := by
    have h' := OmegaAtKeyBook.ties_O
    unfold atFull at h'
    rw [hK] at h'
    rw [hB, e2]
    exact h'
  rw [hp] at hc hca hm ⊢
  have hm' := orRefused_ok hm
  have hca' := carriedAt_behindGuard k 1 ⟨omegaTestPlace, 1⟩
    (restPart (jobKO (X := Unit) ⟨QK, 0⟩ pU pO [B.b1, B.b2, B.b3, B.b4, B.b5, B.b6, B.b7, B.b8] weights
      rand).toRun.toTest) (ca := ca) hca
  obtain ⟨Dp, c3, Rw, h3, hS, hD⟩ := left (say hc m ca hm' hca')
  obtain ⟨cc, m₂, hm₂, hca₂, -, -, hon⟩ := onOmega_key_sourced hs scope hR h pU pO
    (hpU.trans (by rw [hPl]; rfl)) (by rw [e2]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) (by rw [e1])
    B.b1 B.b2 B.b3 B.b4 B.b5 B.b6 B.b7 B.b8 hb weights rand Js (hJs.trans e2.symm) hown σ
    ((hbp.trans hp).trans (by rw [hpO]; exact (place_p12At _ _).symm)) pre t
    (by refine StandsAt.of_same ?_ ?_ hto A <;> rfl) h10 (by rw [hbp, hp]; exact hc)
    (fun m₃ hm₃ => by
      rw [hbp, hp] at hm₃ ⊢
      rw [eS]
      exact door hc m₃ hm₃)
    (by
      rw [eP, hbp, hp, (shared_finds K hsp hU hOp).2, hO]
      rfl)
    (hlaid σ hσ) (le_of_eq hor.symm)
    (by rw [eP]; exact hgO)
    hbk hT hd1
  rw [hbp, hp] at hm₂ hca₂ hon
  rw [eS] at hon
  obtain rfl : m₂ = m := Option.some.inj (Except.ok.inj (hm₂.symm.trans hm'))
  obtain rfl : cc.2.1.2.2 = ca := Except.ok.inj (hca₂.symm.trans hca)
  exact (hon ⟨Dp, c3, Rw, h3.trans firstListAtKey_length.symm, hS, hD⟩).2 rfl

/-- **The same at the senders' own letters.** -/
theorem omega_on_of_two (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hA : K.send = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U))
    (hO : K.onOmega = proverSideOfTestOnOmega K.send pU pO (bsOf K) (wtOf K) (rdOf K)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey) (hJs : Js.p = piKOFull)
    (hown : Js.own = true) {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws}
    {r : RunC (keyFileDescription Xs N Pl)} (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r)
    (say : SayAtRun Empty (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest
      (plainMany (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K))) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ))
    (door : DoorAtRun (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members,
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      OnOmegaKey Face.shared (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest Js 1 u
        ca m (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked)
          ⟨L.place, u.number⟩) := by
  have hI : (blocks QK).isSome = true :=
    List.all_eq_true.1 ProofFile.Honest.K12.Light.KeyDoorUClosed.plan_U _ (by
            unfold ProofFile.Honest.K12.Light.KeyDoorUClosed.planU
            exact List.mem_cons_self)
  have hb : blocks QK = some (bsOf K) := by
    show blocks QK = some ((blocks K.send.P).getD [])
    rw [hA]
    exact some_getD hI _
  have hOp : K.onOmega.place = omegaTestPlace := by
    rw [hO, hpO]
    exact place_p12At _ _
  exact omega_on_of_two_at hs scope hK hB K hsp hU K.send hA pU pO hpU hpO (bsOf K) hb (wtOf K) (rdOf K) hO
    (omegaSending_found K hsp hU hOp) S c H Js hJs hown due h say door

/-- **`owedAt` AT THE MUTED ROW OF THE TEST ON G_omega, FROM THE TWO NAMED SENTENCES AT THE RUN**: the form of the field
owed. -/
theorem omega_owed_of_two (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace)
    (hA : K.send = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U))
    (hO : K.onOmega = proverSideOfTestOnOmega K.send pU pO (bsOf K) (wtOf K) (rdOf K)) (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey)
    (hsim : S.testOnOmega = [firstSim Js, restSim Js]) (hJs : Js.p = piKOFull) (hown : Js.own = true)
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
        ρ))
    (door : DoorAtRun (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
        ρ)
      (r.run.beforeAt (storedShown (H.storedWords w₀ rc) r.run.storedAsked) ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, L.place = omegaTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run
        (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called := by
  rw [prover_mute] at h say door ⊢
  intro L hL hp
  obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
  have hp₀ : L₀.place = omegaTestPlace := hp
  have plan := hs.named.plan
  have book : Bk.word (keyFileDescription Xs N Pl) = none := by
    rw [hB]
    exact AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK
  have e2 : pO = piKOFull := hpO.trans omegaNumbers_written
  obtain ⟨⟨eOn, eBud, -⟩, -, -⟩ :=
    omega_row_form hs scope K hsp hU K.send pU pO hpO (bsOf K) (wtOf K) (rdOf K) hO S c L₀ h₀ hp₀
  suffices key : L₀.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
      (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
        ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ a)) r.run
      (storedShown (H.storedWords w₀ rc) r.run.storedAsked) r.called from key
  refine owedAt_shared_at plan book h h₀ _ (fun σ hσ u hu hc ca m hca hm => ?_) fun σ hσ u hu => ?_
  · rw [eOn]
    exact hOn _ _ _ _ (omega_on_of_two hs scope hK hB K hsp hU hA pU pO hpU hpO hO S c H Js hJs hown due h say
      door L₀ h₀ hp₀ σ hσ u hu hc ca m hca hm)
  · obtain ⟨-, ⟨pre, t, hcut, e1, e3⟩, -⟩ := shared_part_at_run plan book h h₀ hσ hu
    rw [e1, e3]
    exact omega_bud_guarded scope live hs L₀
      (jobKO (X := Unit) K.send pU pO (bsOf K) (wtOf K) (rdOf K)).toRun.toTest Js
      (e2.trans ProofFile.Honest.K12.Light.KeyDoorUClosed.place_sim.symm)
      (hJs.trans ProofFile.Honest.K12.Light.KeyDoorUClosed.place_sim.symm) rfl hown
      (hp₀.trans (by rw [hpO]; exact (place_p12At _ _).symm))
      (omega_row_guarded K hsp hU K.send pU pO (by rw [hpO]; exact place_p12At _ _) (bsOf K) (wtOf K) (rdOf K)
        hO S Js hsim c L₀ h₀ hp₀)
      (fun n ds asks hb' => by rw [eBud]; exact hpos n ds asks hb') σ hσ u hu pre t _ hcut rfl ρ due

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.cut_unique
#print axioms AtPublicFiles.OfflineRows.omegaSending_found
#print axioms AtPublicFiles.OfflineRows.omega_front_ten
#print axioms AtPublicFiles.OfflineRows.omega_on_of_two_at
#print axioms AtPublicFiles.OfflineRows.omega_on_of_two
#print axioms AtPublicFiles.OfflineRows.omega_owed_of_two
