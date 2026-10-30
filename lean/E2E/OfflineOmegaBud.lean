-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/OfflineOmegaBud.lean: THE ROW OF THE KEY FILE's TEST ON G_omega (⟨2, –, 10⟩): ITS LETTER ON POSITIONS IS PAID, so that of
E2E/OfflineOmegaOwed.lean's four named premises three stay.

  `take_behindGuard`        the numbers of moves of a row behind the guard are the row's
  `omega_bud_guarded`       the field `bud₂` of `BudDebts` (Johnson/Desc/ProofFile/Honest/Law/OwedRule.lean) at a list whose row is the
                            test's pair behind the guard (`guardRow`, …/K12/SimO/Guard.lean): from `budOwed₂_at_KO`
                            (Johnson/M1/KeyBudO.lean), which is at the bare pair: the bound reads of a member its number
                            and its rounds alone
  `omega_row_guarded`       where the simulators laid at the place are a job's two, the offline row there is that pair
                            behind the guard
  `omega_owed_of_three`     `owedAt` at the row from `SayAtRun`, `DoorAtRun`, `FirstTreesAtRun`
  `omega_owed_muted`        the same at the muted rows, at the muted rows' prover

Premises beside these three: the public files' test (`protocolDataWellFormed`: the count asks it), `KeySourced`, `InScope`, the written book;
on the letters: the simulators at the place are `firstSim Js`, `restSim Js`; Js stands at the written place and has its own table;
the row's letter on positions follows from `budBoth Js`, its condition at a part from «columns are handed» and
`OnEntryOwn`.

Limits. Those of E2E/OfflineOmegaOwed.lean. Nothing on any property.
-/
import E2E.OfflineOmegaOwed
import Johnson.M1.KeyBudO

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.Own
open ProofFile.Honest.K12.Light (plainMany pKO budBoth)
open ProofFile.Honest.K12.Light.KeyDoorUClosed (place_sim)
open ProofFile.Honest.K14 (SendPub)
open OnBytes (TableKey)
open VerifiableInference.Desc (Place Block FileDescription)
open VerifiableInference.Desc.K12 (P12 T12)
open VerifiableInference.Desc.Key (Source LaterPlaces)
open _root_.Desc.K14 (St blocks)
open H2K.Member (piKOFull codesKeyFull)
open AtPublicFiles.AtFiles (KeySourced keyFileDescription)
open AtPublicFiles.AtFiles.Full (QK PF)
open AtPublicFiles.KeyBook (KeyPub keyBook fullPub foldedTestPlace omegaTestPlace)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver)
open AtPublicFiles.KeyLay (jobKO proverSideOfTestOnOmega)
open AtPublicFiles.KeyValueHolds (place_p12At)
open VerifierAndGoals (PublicFiles InScope asDescriptionFiles)
open FlashProve (protocolDataWellFormed)

/-- The numbers of moves of a row behind the guard are the row's. -/
theorem take_behindGuard {V W Y Pb : Type} (row : List (Part V W Y × Sim Pb)) (j : ℕ) :
    (((guardRow row).take j).map fun x => x.1.moves.length) =
      (row.take j).map fun x => x.1.moves.length := by
  unfold guardRow
  rw [← List.map_take, List.map_map]
  exact List.map_congr_left fun x _ => needsField_length x.1

section Bud
variable {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **The field `bud₂` at a list whose row is the test's pair behind the guard.** -/
theorem omega_bud_guarded (scope : InScope Z = true) (live : protocolDataWellFormed (asDescriptionFiles Z) = true)
    (hS : KeySourced Z Xs N Pl) {V W Y Pb : Type} {Bk : ProverCoinCounts}
    (L : Lettered Bk (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W Y Pb) (J : TestJob W Y)
    (Js : SimJob Pb) (hp : J.p = pKO) (hJ : Js.p = pKO) (hfr : J.fresh.isNone = true)
    (ho : Js.own = true) (hpl : L.place = J.p.place) (hrow : L.row = guardRow (testPairs J Js))
    (hbud : ∀ n ds asks, budBoth Js n ds asks → L.bud n ds asks) :
    ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ → ∀ u ∈ σ.members, ∀ pre t n,
      (keyFileDescription Xs N Pl).shared.blocksInOrder = pre ++ σ.block :: t →
      n = (pre.flatMap (·.rounds)).length + σ.roundsTo u.number → ∀ ρ : Draws,
      ρ.due (keyFileDescription Xs N Pl) = true →
      L.bud u.number ((ρ.shared.drop n).take u.rounds.length)
        (asksFrom (treeAsks (keyFileDescription Xs N Pl) ρ 1) (u.rounds.map (·.2.length))
          (((rowsOfChain (keyFileDescription Xs N Pl).shared.blocksInOrder).take n).map (·.2.length)).sum) := by
  intro σ hσ u hu pre t n hcut hn ρ hρ
  let L₀ : Lettered Bk (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W Y Pb :=
    { L with row := testPairs J Js }
  have B := OnBytes.M1.KeyBud.budOwed₂_at_KO scope live hS L₀ J Js hp hJ hfr ho hpl rfl hbud
  have hσ' := hσ
  unfold Lettered.side Side.seated at hσ'
  obtain ⟨b, hb, e⟩ := Option.map_eq_some_iff.1 hσ'
  let σ₀ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W Y Pb :=
    ⟨b, testPairs J Js, fallOf [] L.place⟩
  have hσ₀ : L₀.side (keyFileDescription Xs N Pl).shared.blocksInOrder = some σ₀ := by
    unfold Lettered.side Side.seated
    show Option.map _ ((keyFileDescription Xs N Pl).shared.blocksInOrder.find? fun b => b.place == L.place) = _
    rw [hb]
    rfl
  have eb : σ.block = b := by rw [← e]
  have er : σ.row = guardRow (testPairs J Js) := by rw [← e]; exact hrow
  have hm : σ.members = σ₀.members.map Member.guarded := by
    show membersOf σ.row 0 _ = _
    rw [er, membersOf_guardRow, eb]
    rfl
  rw [hm] at hu
  obtain ⟨u₀, hu₀, rfl⟩ := List.mem_map.1 hu
  have hTo : σ.roundsTo u₀.guarded.number = σ₀.roundsTo u₀.number := by
    unfold Side.roundsTo
    rw [er]
    show (((guardRow (testPairs J Js)).take u₀.number).map fun x => x.1.moves.length).sum = _
    rw [take_behindGuard]
  exact B σ₀ hσ₀ u₀ hu₀ pre t n (by rw [hcut, eb]) (by rw [hn, hTo]) ρ hρ

end Bud

section Run
variable {W₀ Rc Wk : Type} {Z : PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces}

/-- **Where the simulators laid at the place are a job's two, the offline row there is the pair behind the
guard.** -/
theorem omega_row_guarded {Fx : FileDescription KeyInst} {Bk : ProverCoinCounts} (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (pU pO : P12) (hpl : pO.place = omegaTestPlace) (bs : List (Block St Unit))
    (weights : Common W₀ Rc TableKey → Weights) (rand : Common W₀ Rc TableKey → TableRand)
    (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand) (S : OfflineSimulators) (Js : SimJob TableKey)
    (hsim : S.testOnOmega = [firstSim Js, restSim Js])
    (c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit Unit Unit) :
    ∀ L ∈ (offlineRows Fx Bk K S c).shared, L.place = omegaTestPlace →
      L.row = guardRow (testPairs (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js) := by
  intro L hL hp
  have hOp : K.onOmega.place = omegaTestPlace := by
    rw [hO]
    exact hpl
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL
  obtain rfl := half_at_omegaTest K hsp hU hOp hg hp
  show partsBeside K.onOmega.parts (S.byChain.shared K.onOmega.place) = _
  rw [hOp]
  show partsBeside K.onOmega.parts S.testOnOmega = _
  rw [hsim, hO]
  rfl

/-- **`owedAt` AT THE ROW OF THE TEST ON G_omega, FROM THE THREE NAMED SENTENCES AT THE RUN.** -/
theorem omega_owed_of_three (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey)
    (hsim : S.testOnOmega = [firstSim Js, restSim Js]) (hJs : Js.p = piKOFull) (hown : Js.own = true)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os.length = 3)
    (hOn : ∀ u ca m front, ((∃ cs, m.opened = some cs) ∧
      OnEntryOwn Face.shared (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js codesKeyFull 1 os u ca
        m front) → (c.shared omegaTestPlace).atPart u ca m front)
    (hpos : ∀ n ds asks, budBoth Js n ds asks → (c.shared omegaTestPlace).positions n ds asks)
    {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64))
    (say : SayAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest
      (plainMany (jobKO (X := Unit) A pU pO bs weights rand)) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ))
    (door : DoorAtRun (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩))
    (trees : FirstTreesAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest os k 1
      omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).shared, L.place = omegaTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).prover H) w₀ rc x k ρ a)) r.run st r.called := by
  have e2 : pO = piKOFull := hpO.trans omegaNumbers_written
  refine omega_owed_at_rows hs scope hK hB K hsp hU A hA pU pO hpU hpO bs hb weights rand hO S c H Js os hos
    hOn (fun L hL hp => ?_) due h st say door trees
  obtain ⟨⟨-, eBud, -⟩, -, -⟩ := omega_row_form hs scope K hsp hU A pU pO hpO bs weights rand hO S c L hL hp
  exact omega_bud_guarded scope live hs L (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
    (e2.trans place_sim.symm) (hJs.trans place_sim.symm) rfl hown
    (hp.trans (by rw [hpO]; exact (place_p12At _ _).symm))
    (omega_row_guarded K hsp hU A pU pO (by rw [hpO]; exact place_p12At _ _) bs weights rand hO S Js hsim c L
      hL hp)
    (fun n ds asks hb' => by rw [eBud]; exact hpos n ds asks hb')

/-- **The same at the muted rows**, at the muted rows' prover: the form of the field owed. -/
theorem omega_owed_muted (hs : KeySourced Z Xs N Pl) (scope : InScope Z = true)
    (live : protocolDataWellFormed (asDescriptionFiles Z) = true) {K₀ : KeyPub}
    (hK : fullPub = some K₀) {Bk : ProverCoinCounts} (hB : Bk = keyBook K₀) (K : KeyParts W₀ Rc Unit Unit Wk)
    (hsp : K.lin.S.sharedSplitNeeded = true) (hU : K.onU.place = foldedTestPlace) (A : SendPub)
    (hA : A = ⟨QK, 0⟩) (pU pO : P12) (hpU : pU = H2U.proximityTestParametersAt foldedTestPlace PF.U)
    (hpO : pO = H2U.proximityTestParametersAt omegaTestPlace (PF.O.getD PF.U)) (bs : List (Block St Unit))
    (hb : blocks QK = some bs) (weights : Common W₀ Rc TableKey → Weights)
    (rand : Common W₀ Rc TableKey → TableRand) (hO : K.onOmega = proverSideOfTestOnOmega A pU pO bs weights rand)
    (S : OfflineSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit Unit Unit)
    (H : Prover W₀ Rc KeyInst TableKey Unit Unit Unit) (Js : SimJob TableKey)
    (hsim : S.testOnOmega = [firstSim Js, restSim Js]) (hJs : Js.p = piKOFull) (hown : Js.own = true)
    (os : List (Fmt.Shape × Fmt.TreeSource)) (hos : os.length = 3)
    (hOn : ∀ u ca m front, ((∃ cs, m.opened = some cs) ∧
      OnEntryOwn Face.shared (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js codesKeyFull 1 os u ca
        m front) → (c.shared omegaTestPlace).atPart u ca m front)
    (hpos : ∀ n ds asks, budBoth Js n ds asks → (c.shared omegaTestPlace).positions n ds asks)
    {w₀ : W₀} {rc : Rc} {x : KeyInst} {k : Coins Bk} {ρ : Draws} {r : RunC (keyFileDescription Xs N Pl)}
    (due : ρ.due (keyFileDescription Xs N Pl) = true)
    (h : runC (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ =
      .ok r) (st : List (ℕ × ℕ × List UInt64))
    (say : SayAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest
      (plainMany (jobKO (X := Unit) A pU pO bs weights rand)) k 1 omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
        ρ))
    (door : DoorAtRun (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest Js
      (Face.shared (W₀ := W₀) (Rc := Rc) (Ky := TableKey)).pub omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
        ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩))
    (trees : FirstTreesAtRun Empty (jobKO (X := Unit) A pU pO bs weights rand).toRun.toTest os k 1
      omegaTestPlace r.called
      (midSharedAtW (keyFileDescription Xs N Pl) Bk ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k
        ρ)
      (r.run.beforeAt st ⟨omegaTestPlace, 1⟩)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.shared, L.place = omegaTestPlace →
      L.owedAt (keyFileDescription Xs N Pl).shared.blocksInOrder k 1
        (fun a => orRefused (midSharedAtW (keyFileDescription Xs N Pl) Bk
          ((offlineRows (keyFileDescription Xs N Pl) Bk K S c).mute.prover H) w₀ rc x k ρ a)) r.run st r.called := by
  rw [prover_mute] at h say door trees ⊢
  intro L hL hp
  obtain ⟨L₀, h₀, rfl⟩ := List.mem_map.1 hL
  exact omega_owed_of_three hs scope live hK hB K hsp hU A hA pU pO hpU hpO bs hb weights rand hO S c H Js hsim
    hJs hown os hos hOn hpos due h st say door trees L₀ h₀ hp

end Run

end AtPublicFiles.OfflineRows

#print axioms AtPublicFiles.OfflineRows.take_behindGuard
#print axioms AtPublicFiles.OfflineRows.omega_bud_guarded
#print axioms AtPublicFiles.OfflineRows.omega_row_guarded
#print axioms AtPublicFiles.OfflineRows.omega_owed_of_three
#print axioms AtPublicFiles.OfflineRows.omega_owed_muted
