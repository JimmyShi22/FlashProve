-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaFive.lean: FIVE CLAUSES OF THE CONDITION AT THE ENTRY OF THE SECOND PART OF THE KEY FILE's TEST ON G_omega
(⟨2, –, 10⟩), AT A RUN's OWN VALUES: le, leS, heardFit, heard, fold (`FiveAtEntry`, E2E/OfflineTestFive.lean), at the offline
rows (`offlineRows`, E2E/OfflineSides.lean) over parts whose half at the place is `proverSideOfTestOnOmega` (E2E/KeyHalves.lean: the pair
behind the guard), at the written book, in the form in which `owedAt_shared_at` (E2E/OfflineOwedChains.lean) asks On: at
every carried block that the book gives the part and every state that the frame returns at its address.

  `omegaJob`             the job with another state on entry: `jobKO …` with rec₀ := r'
  `omega_public`         its public part (`TestPublic`), at every r'
  `omega_laid`           the sub-protocol at the place declares the job's rounds and oracle messages
  `omega_five_at_run`    the theorem, AT EVERY r' THAT AGREES WITH THE JOB's OWN STATE ON ENTRY BUT FOR TARGETS
                         (`Blind.Agree`, Johnson/Desc/ProofFile/Honest/K12/Blind/Wipe.lean): the clause fold reads the state on entry,
                         and a condition may ask the five at such a stand-in
  `omega_five_at_run_own`   at the job's own state on entry
  `omega_five_at_value`     at the offline prover's own senders (`valueAt`, E2E/KeyValueHolds.lean)

It pays none of the clauses door, trees, asks. At a state on entry that is a letter, not shown to be the verifier's.
That a run returns, or calls the part, is not shown here. At the written sizes, under `fullPub = some K₀`,
`KeySourced` and `InScope`. Nothing on any property.
-/
import E2E.OfflineTestFiveGuarded
import E2E.OfflineSharedTestsTies
import E2E.OfflineSides
import E2E.KeyBookThirdNamed
import Johnson.SendSim.Seat.AtKeyStands
import Johnson.Desc.ProofFile.Honest.K12.Blind.All

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.enter Seat.leave)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St)
open H2K.Pub (sgOf)
open H2K.Member (piKOFull)
open H2K.JointK (keyOmega)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF later_sourced par_sourced)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub atFull foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnOmega bsOf wtOf rdOf)
open AtPublicFiles.KeySharedThread (parKey)
open AtPublicFiles.KeyValues (WitK withSendingsAndLookups)
open AtPublicFiles.KeyValueHolds (valueAt place_p12At)
open AtPublicFiles.AtFiles.HonestTerm (withStoredColumnsAndPlan)
open OnBytes.Slice (GF)
open VerifierAndGoals (PublicFiles InScope)

section Public
variable {W₀ Rc X₀ : Type}

/-- **The job of the test on G_omega, with another state on entry.** -/
abbrev omegaJob (A : SendPub) (pU pO : P12) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (r' : Common W₀ Rc TableKey → Front X₀ → T12) : TestJob (Common W₀ Rc TableKey) X₀ :=
  { (jobKO (X := X₀) A pU pO bs weights rand).toRun.toTest with rec₀ := r' }

variable (A : SendPub) (pU : P12) (bs : List (Block St Unit))
  (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
  (r' : Common W₀ Rc TableKey → Front X₀ → T12)

/-- **The job's public part**, at every state on entry. -/
theorem omega_public :
    ∃ s next rest, TestPublic (omegaJob A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r')
        s next rest ∧
      (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) : Block T12 Unit).planOk = true := by
  have hp : (omegaJob A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r').p = piKOFull :=
    omegaNumbers_written
  obtain ⟨s, t, rest, hst⟩ := two_in_front (l := (omegaJob A pU
      (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r').p.nums.stages) (by
                        rw [hp]
                        exact omegaStages_two)
  have hk : s.k = (sgOf s).h + (sgOf s).g := by
    have h := omegaFirst_splits
    rw [← hp, hst] at h
    exact h
  have P := PlanAtKey.planPlays_KO _ hp rfl s (t :: rest) hst
  refine ⟨s, t, rest, ⟨hst, hk, ?_, P.sorts, P.tables, fun w fr mem mem' h => ?_⟩, P.plan⟩
  · rw [hp]
    exact omegaEnough_written
  · exact Light.rowsMu_many (jobKO (X := X₀) A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
      rand) s w fr mem mem' h

/-- **The sub-protocol at the test's place declares the job's rounds and oracle messages.** -/
theorem omega_laid {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} (hs : KeySourced Z Xs N PF)
    (scope : InScope Z = true) {b : Block (keyFileDescription Xs N PF).S₂ (keyFileDescription Xs N PF).Cl}
    (hb : b ∈ (keyFileDescription Xs N PF).shared.blocksInOrder) (hp : b.place = omegaTestPlace) :
    b.rounds.zip b.oracles =
      (omegaJob A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r').laid := by
  obtain ⟨-, -, -, -, hplan⟩ := omega_public A pU bs weights rand r'
  have e : b = keyOmega (PF.O.getD PF.U) := sharedBlock_omega hs scope b hb hp
  have S : SeatOf (keyOmega (PF.O.getD PF.U))
      (omegaJob A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r')
      (Seat.enter (·.gOmega) fun _ => none) Seat.leave := by
    have h := seatOf_inside (Cl := Unit)
      (omegaJob A pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r')
      (Seat.enter (·.gOmega) fun _ => none) Seat.leave
    exact ⟨h.place, h.rounds, h.oracles, h.decide⟩
  rw [e, S.rounds, S.oracles]
  exact zip_laid _ hplan

end Public

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **FIVE CLAUSES AT A RUN, at the second part of the test on G_omega**: at every carried block and every state
that the frame returns at the part's address, where the part is called, at the run's own front; at every
state on entry r' that agrees with the job's own but for targets. Js: any simulators' job: nothing is read of
it. -/
theorem omega_five_at_run (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U))
    (bs : List (Block St Unit)) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (r' : Common W₀ Rc TableKey → Front Unit → T12)
    (hr : ∀ w fr, Blind.Agree ((jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest.rec₀ w fr) (r' w fr))
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey) {w₀ : W₀} {rc : Rc}
    {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      FiveAtEntry (omegaJob A pU pO bs weights rand r') (stretches _ ca) m
        (r.run.beforeAt st ⟨L.place, u.number⟩) := by
  subst hB
  subst hpO
  subst hA
  have hPl : Pl = PF := later_sourced hs scope
  subst hPl
  obtain ⟨s, next, rest, P, -⟩ := omega_public (X₀ := Unit) ⟨QK, 0⟩ pU bs weights rand r'
  intro L hL hp σ hσ
  have hplace : (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand
      r').p.place = omegaTestPlace := place_p12At _ _
  have hOp : K.onOmega.place = omegaTestPlace := by
    rw [hO]
    exact place_p12At _ _
  have hhalf : (proverSideOfProximityTest (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs
                       weights rand r') : Placed Empty (Common W₀ Rc TableKey) Unit) =
      proverSideOfProximityTest (jobKO (X := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
                         rand).toRun.toTest := Blind.testHalf_one _ r' hr
  have hparts : L.row.map (·.1) =
      [(firstPart (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
        rand r')).needsField,
       (restPart (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
        rand r')).needsField] := by
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
    obtain rfl := half_at_omegaTest K hsp hU hOp hg hp
    show (partsBeside K.onOmega.parts _).map (·.1) = _
    rw [partsBeside_parts, hO]
    show (proverSideOfProximityTest (jobKO (X := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights
                       rand).toRun.toTest : Placed Empty (Common W₀ Rc TableKey) Unit).needsField.parts = _
    rw [← hhalf]
    rfl
  have hT : Own.tiesOB (keyBook K₀) (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU
      (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r').p.place
      (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand
        r').members.length = true := by
    have hm : (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand
        r').members = AtPublicFiles.KeyTest.jobOmega.members := omegaMembers_written
    have hpp : (omegaJob (X₀ := Unit) ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand
        r').p = piKOFull := omegaNumbers_written
    rw [hpp, hm, members_two_O]
    have h' := OmegaAtKeyBook.ties_O
    unfold atFull at h'
    rw [hK] at h'
    exact h'
  exact five_at_shared_guarded_row hs.named.plan (AtPublicFiles.KeyBook.book_passes scope hs.named K₀ hK) due h hL hσ
    (omegaJob ⟨QK, 0⟩ pU (H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) bs weights rand r') Js rfl
    (hp.trans hplace.symm) hparts
    (omega_laid ⟨QK, 0⟩ pU bs weights rand r' hs scope (OnBytes.SendSim.Seat.block_of_seated hσ)
      ((side_place hσ).trans hp)) hT s next rest P st

/-- **The same at the job's own state on entry.** -/
theorem omega_five_at_run_own (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U))
    (bs : List (Block St Unit)) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey) {w₀ : W₀} {rc : Rc}
    {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      FiveAtEntry (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest (stretches _ ca) m
        (r.run.beforeAt st ⟨L.place, u.number⟩) :=
  omega_five_at_run hs scope hK hB K hsp hU A hA pU pO hpO bs weights rand hO _ (fun _ _ => rfl) S c H Js
    due h st

end Run

section Value
variable {W₀ Rc : Type} (K' : KeyParts W₀ Rc Unit Unit WitK) (Xs : Source) (N : H2U.PlaceNums)
  (Pl : LaterPlaces) (f : W₀ → Weights) (g : Rc → Nat → TableRand) (inR : W₀ → Bool) (d : W₀)
  (ent : Local W₀ Rc KeyInst Unit → Nat → Nat → GF) (groups : List (List Nat)) (first : Nat)

/-- The senders beneath the four proximity tests of the offline prover's own value. -/
abbrev sendersAt : KeyParts W₀ Rc Unit Unit WitK :=
  withStoredColumnsAndPlan Xs Pl (withSendingsAndLookups K' Xs N f inR d) f g

/-- **The five at a run, at the offline prover's own senders** (`valueAt`, E2E/KeyValueHolds.lean), at its two places'
own numbers; at every state on entry that agrees with the job's own but for targets. -/
theorem omega_five_at_value {Z : PublicFiles} (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    {K₀ : KeyPub} (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀)
    (r' : Common W₀ Rc TableKey → Front Unit → T12)
    (hr : ∀ w fr, Blind.Agree ((jobKO (X := Unit) ⟨parKey Xs Pl, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
      (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) (bsOf (sendersAt K' Xs N Pl f g inR d))
      (wtOf (sendersAt K' Xs N Pl f g inR d)) (rdOf (sendersAt K' Xs N Pl f g inR d))).toRun.toTest.rec₀
      w fr) (r' w fr))
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey) {w₀ : W₀} {rc : Rc}
    {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                 (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
                   (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first) S c).prover H) w₀ rc x k ρ = .ok r)
    (st : List (ℕ × ℕ × List UInt64)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk
        (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
          (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first) S c).shared,
      L.place = omegaTestPlace →
      ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, u.number = 1 →
      r.called ⟨L.place, u.number⟩ = true → ∀ ca m,
      carriedAt Bk k 1 ⟨L.place, u.number⟩ u.part = .ok ca →
      orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk
                   (valueAt K' Xs N Pl f g inR d (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
                     (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) ent groups first) S c).prover H)
        w₀ rc x k ρ ⟨L.place, u.number⟩) = .ok m →
      FiveAtEntry (omegaJob ⟨parKey Xs Pl, 0⟩ (H2U.proximityTestParametersAt foldedTestPlace Pl.U)
          (H2U.proximityTestParametersAt omegaTestPlace (Pl.O.getD Pl.U)) (bsOf (sendersAt K' Xs N Pl f g inR d))
          (wtOf (sendersAt K' Xs N Pl f g inR d)) (rdOf (sendersAt K' Xs N Pl f g inR d)) r')
        (stretches _ ca) m (r.run.beforeAt st ⟨L.place, u.number⟩) := by
  have e : parKey Xs Pl = QK := par_sourced hs scope
  have hPl : Pl = PF := later_sourced hs scope
  exact omega_five_at_run hs scope hK hB _
    (by
      show (parKey Xs Pl).S.sharedSplitNeeded = true
      rw [e]
      exact writtenShape_splits)
    (place_p12At _ _) ⟨parKey Xs Pl, 0⟩ (by rw [e]) _ _ (by rw [hPl]) _ _ _ rfl r' hr S c H Js due h st

end Value

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.omega_public
#print axioms AtPublicFiles.OfflineRows.omega_laid
#print axioms AtPublicFiles.OfflineRows.omega_five_at_run
#print axioms AtPublicFiles.OfflineRows.omega_five_at_run_own
#print axioms AtPublicFiles.OfflineRows.omega_five_at_value
