-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowTies.lean: ALL FOUR ROWS ARE CONDITIONAL ON THEIR On AT A RUN, OF WHICH NOTHING IS PAID HERE.
K12's FOUR OFFLINE ROWS ARE THE OFFLINE PROVER's OWN HALVES. At the
senders with the four tests laid (withTests), the halves that keyProver holds are the halves of the jobs of which RowRanges,
RowFolded, RowOwnKey and SimO/Key speak; and a half with the two simulators beside it is the row that those files seat.

  beside_test, beside_guard   a half, bare or behind the guard, beside the job's two simulators
  first_rng, shared_tests, second_own   where keyProver holds the four halves
  omega_sourced, omega_there, find_omega, spent_omega_full   the test on G_omega, in scope
  simOmegaKey, stateAtOmegaKey, omega_row, omega_row_at_half   row 15: Good at the pair behind the guard, at the key's book

Stands on KeyProver.
NO PROPERTY IS CLAIMED.
-/
import E2E.OfflineRows
import E2E.TheHonestProver
import E2E.KeyProverSideOfOwnTest
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowFolded
import Johnson.Desc.ProofFile.Honest.K12.SimO.Guard
import Johnson.Desc.ProofFile.Honest.K12.SimO.Key
import Johnson.Desc.ProofFile.Honest.K12.SimO.DoorOmega
import E2E.KeyShapeSharedTies
import E2E.KeyShapeSharedFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open VerifiableInference.Desc.K12 (P12)
open AtPublicFiles.KeyFile (KeyParts keyProver randK14)
open AtPublicFiles.KeyLay (withTests withTestsOnUAndOmega bsOf stOf wtOf rdOf jobKU jobKO jobKWAt)
open AtPublicFiles.KeyThread (rangesTestJob)
open AtPublicFiles.OfflineRows (partsBeside rowOf RowConditions)
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (askOf)

section
variable {V W X Pb : Type}

/-- A half beside its job's two simulators is the job's pairs. -/
theorem beside_test (J : TestJob W X) (Js : SimJob Pb) :
    partsBeside (proverSideOfProximityTest J : Placed V W X).parts [firstSim Js, restSim Js] = testPairs J Js := rfl

/-- The same behind the guard. -/
theorem beside_guard (J : TestJob W X) (Js : SimJob Pb) :
    partsBeside (proverSideOfProximityTest J : Placed V W X).needsField.parts [firstSim Js, restSim Js] =
      ProofFile.Honest.guardRow (testPairs J Js) := rfl

end

section
variable {W₀ Rc X₀ X Wk : Type} (Sd : KeyParts W₀ Rc X₀ X Wk) (src : Source)
  (N : H2U.PlaceNums) (Pl : LaterPlaces) (pU pO : P12)
  (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF) (grp : List (List Nat)) (fst : Nat)

/-- **The test on the ranges is the first chain's fifth half.** -/
theorem first_rng :
    (keyProver (withTests Sd src N Pl pU pO ent grp fst)).first[4]? =
      some (proverSideOfProximityTest (rangesTestJob src N Pl ent grp fst)) := rfl

/-- **The tests on G_u and on G_omega are the shared chain's last two halves.** -/
theorem shared_tests :
    (keyProver (withTests Sd src N Pl pU pO ent grp fst)).shared =
      AtPublicFiles.KeyFile.sharedChainProverSidesInOrder (ProofFile.Honest.K14.proverSidesOfSharedRounds Sd.lin Sd.weights)
        (ProofFile.Honest.K14.proverSidesOfSharedSendings Sd.send Sd.weights fun c => randK14 (Sd.rand c)) ++
      [proverSideOfProximityTest (jobKU Sd.send pU (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest,
       (proverSideOfProximityTest (jobKO Sd.send pU pO (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest :
         Placed Empty (AtPublicFiles.KeyFile.In2 W₀ Rc) X₀).needsField] := rfl

/-- **The own test is the last chain's half.** -/
theorem second_own :
    (keyProver (withTests Sd src N Pl pU pO ent grp fst)).second =
      [(proverSideOfProximityTest (jobKWAt src N Pl Sd.idx Sd.w Sd.send id
                           (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest :
        Placed (AtPublicFiles.KeyFile.In1 W₀ Rc) (AtPublicFiles.KeyFile.In1 W₀ Rc) X).needsField] := rfl

end

/-! ## Row 15 -/

section Key
open H2K.Member (piKOFull codesKeyFull)
open H2K.JointK (keyOmega keySharedPre keyGu keySharedEnd)
open AtPublicFiles.AtFiles (KeyNamed keyFileDescription KeySourced)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub omegaTestPlace)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc.K12 (proximityTestKind guardedProximityTestParts T12)
open ProofFile.Honest.Small (noneSpent)
open ProofFile.Honest.K12.Light (AtKeyPlace firstListAtKey OnOmegaKey key_omega_fields budBoth)
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {V W X Pb : Type}

/-- The test's numbers at the key file's plan: T1's offlineTestOnOmega. -/
abbrev pKOv (Pl : LaterPlaces) : P12 := H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ (Pl.O.getD Pl.U)

/-- In scope the seated numbers are the written ones. -/
theorem omega_sourced (hS : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) : pKOv Pl = piKOFull := by
  rw [AtPublicFiles.AtFiles.Full.later_sourced hS scope]
  rfl

/-- In scope the plan has a test on G_omega. -/
theorem omega_there (hS : KeySourced Z Xs N Pl) (scope : VerifierAndGoals.InScope Z = true) :
    Pl.O = some (Pl.O.getD Pl.U) := by
  rw [AtPublicFiles.AtFiles.Full.later_sourced hS scope]
  exact AtPublicFiles.AtFiles.Full.omega_full

/-- **The search at the test's place, in the key file's shared chain.** -/
theorem find_omega (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) :
    ∃ b, ((keyFileDescription Xs N Pl).shared.blocksInOrder.find? fun b => b.place == (pKOv Pl).place) = some b ∧
      b.place = (pKOv Pl).place ∧
      b.rounds = (proximityTestKind guardedProximityTestParts (pKOv Pl) : Block T12 Unit).rounds ∧
      b.oracles = (proximityTestKind guardedProximityTestParts (pKOv Pl) : Block T12 Unit).oracles := by
  have r := (AtPublicFiles.KeyBook.places_named scope hS.named).2.1
  have hO := omega_there hS scope
  have hcut := H2K.JointK.keyShared_cut_omega Xs.chains Pl _ hO
  have hnd : (((keyFileDescription Xs N Pl).shared.blocksInOrder).map (·.place)).Nodup := by
    have e : ((keyFileDescription Xs N Pl).shared.blocksInOrder).map (·.place) = AtPublicFiles.KeyBook.fullShared.map (·.1) := by
      rw [← r]
      show _ = (((keyFileDescription Xs N Pl).shared.blocksInOrder).map fun b => (b.place, b.rounds.length)).map (·.1)
      rw [List.map_map]
      rfl
    rw [e]
    decide +kernel
  have hpl : (keyOmega (Pl.O.getD Pl.U)).place = (pKOv Pl).place :=
    H2K.JointK.k12_place guardedProximityTestParts (pKOv Pl)
  refine ⟨keyOmega (Pl.O.getD Pl.U), ?_, hpl, ?_, ?_⟩
  · have key := find_after_nodup (fun b : Block Desc.K14.St VerifiableInference.Desc.Key.Claim => b.place)
      (keySharedPre Xs.chains Pl ++ [keyGu Pl]) (keyOmega (Pl.O.getD Pl.U))
      [keySharedEnd Xs.chains Pl] (by rw [← hcut]; exact hnd) (pKOv Pl).place hpl
    show List.find? _ ((VerifiableInference.Desc.Key.sharedChain Xs.chains Pl).retype
      (Cl' := VerifiableInference.Desc.Key.Claim)).blocksInOrder = _
    rw [hcut]
    exact key
  · exact (H2K.JointK.omegaEntry_sits _ (Pl.O.getD Pl.U)).rounds
  · rfl

theorem spent_omega_full : (fullPub.map fun K => noneSpent (keyBook K) ⟨omegaTestPlace, 0⟩ &&
    noneSpent (keyBook K) ⟨omegaTestPlace, 1⟩) = some true := by decide +kernel

theorem place_KO : piKOFull.place = omegaTestPlace := by decide +kernel

/-- A control: the folded row's test stands at another place. -/
theorem place_KO_bite : piKOFull.place ≠ AtPublicFiles.KeyBook.foldedTestPlace := by decide +kernel

/-- The simulators' job at the test on G_omega, at a state on entry r. -/
def simOmegaKey (r : Pb → Before → T12) : SimJob Pb :=
  ⟨piKOFull, true, r, firstListAtKey.map fun x =>
    ((ProofFile.Honest.srcOf 1 x.2).1, (ProofFile.Honest.srcOf 1 x.2).2, x.1.a)⟩

/-- **Row 15**: Good at a job at the place whose fresh table is its own, at the simulators' job, at the key's book, at every A
that never holds. -/
theorem omega_row (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {K : KeyPub}
    (hK : fullPub = some K) (J : TestJob W X) (hJ : J.p = pKOv Pl) (hfr : J.fresh = none)
    (r : Pb → Before → T12) (φ : Face V W Pb) (firstTree : ℕ)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₂))
    (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W X Pb)
    (hσ : Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder J.p.place
      (ProofFile.Honest.guardRow (testPairs J (simOmegaKey r))) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₂ → ProofFile.Honest.Mid W X → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord 1 firstTree A B (OnOmegaKey φ J (simOmegaKey r) 1)
      (budBoth (simOmegaKey r)) := by
  have hp := omega_sourced hS scope
  have hJ' : J.p = piKOFull := hJ.trans hp
  have hsp := spent_omega_full
  rw [hK] at hsp
  have hsp' : (noneSpent (keyBook K) ⟨omegaTestPlace, 0⟩ && noneSpent (keyBook K) ⟨omegaTestPlace, 1⟩) =
      true := Option.some.inj hsp
  simp only [Bool.and_eq_true] at hsp'
  obtain ⟨b, hf, hpl, hr, hor⟩ := find_omega scope hS
  rw [hp] at hf hpl hr hor
  have hσ' : Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder piKOFull.place
      (ProofFile.Honest.guardRow (testPairs J (simOmegaKey r))) fs = some σ := by
    rw [← hJ']
    exact hσ
  obtain ⟨b', hb', rfl⟩ := Option.map_eq_some_iff.1 hσ'
  obtain rfl : b = b' := Option.some.inj (hf.symm.trans hb')
  have hB : ∀ u ∈ (⟨b, ProofFile.Honest.guardRow (testPairs J (simOmegaKey r)), fallOf fs piKOFull.place⟩ :
      Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl V W X Pb).members,
      noneSpent (keyBook K) ⟨b.place, u.number⟩ = true := by
    intro u hu
    rw [hpl, place_KO]
    have hu' : u ∈ membersOf (ProofFile.Honest.guardRow (testPairs J (simOmegaKey r))) 0 _ := hu
    simp only [ProofFile.Honest.guardRow, testPairs, List.map_cons, List.map_nil, membersOf, List.mem_cons,
      List.not_mem_nil, or_false] at hu'
    rcases hu' with rfl | rfl
    · exact hsp'.1
    · exact hsp'.2
  obtain ⟨h1, h2, h3⟩ := key_omega_fields (p := piKOFull) ⟨rfl, rfl, rfl, rfl, rfl⟩ J hJ' hfr (simOmegaKey r) rfl rfl
    H2K.Pub.piKOFull_planOk fs (keyFileDescription Xs N Pl).shared.blocksInOrder _ hσ' hr hor φ 1 firstTree rfl (keyBook K) ord hB
  exact { fits := h1
          plays := fun _ _ _ _ _ h => (hA _ _ _ _ h).elim
          acc := fun _ _ _ _ _ h => (hA _ _ _ _ h).elim
          exact := fun u hu => ProofFile.Honest.Small.exactAt_of_exact pre (h2 u hu)
          fresh := h3 }

/-- **The simulators' state on entry at the key's test on G_omega**: stateAtOmega at the blocks of the shared chain in front of it. -/
def stateAtOmegaKey (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces) (Ap : ProofFile.Honest.K14.SendPub) (pU : P12) :
    OnBytes.TableKey → Before → T12 :=
  ProofFile.Honest.K12.Light.stateAtOmega Ap.P (ProofFile.Honest.K12.Light.sentOf Ap.P.S) pU
    ((keyFileDescription Xs N Pl).shared.blocksInOrder.takeWhile (·.place != omegaTestPlace))

/-- **The same at the job that proverSideOfTestOnOmega lays.** -/
theorem omega_row_at_half {W₀ Rc X' : Type} (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl)
    {K : KeyPub} (hK : fullPub = some K) (Ap : ProofFile.Honest.K14.SendPub) (pU : P12)
    (bs : List (Block Desc.K14.St Unit))
    (wt : Common W₀ Rc OnBytes.TableKey → Weights) (rd : Common W₀ Rc OnBytes.TableKey → TableRand)
    (φ : Face Empty (Common W₀ Rc OnBytes.TableKey) OnBytes.TableKey) (firstTree : ℕ)
    (fs : List (Fall (keyFileDescription Xs N Pl).S₂))
    (σ : Side (keyFileDescription Xs N Pl).S₂ (keyFileDescription Xs N Pl).Cl Empty (Common W₀ Rc OnBytes.TableKey) X'
      OnBytes.TableKey)
    (hσ : Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder
      (jobKO (X := X') Ap pU (pKOv Pl) bs wt rd).toRun.toTest.p.place
      (ProofFile.Honest.guardRow (testPairs (jobKO (X := X') Ap pU (pKOv Pl) bs wt rd).toRun.toTest
              (simOmegaKey (stateAtOmegaKey Xs N Pl Ap pU)))) fs = some σ)
    (pre : List (ℕ × ℕ × List Fmt.DeclaredRound)) (ord : List Place)
    (A B : Coins (keyBook K) → (keyFileDescription Xs N Pl).S₂ →
      ProofFile.Honest.Mid (Common W₀ Rc OnBytes.TableKey) X' → Env → Prop)
    (hA : ∀ c s m e, ¬ A c s m e) :
    Good pre φ σ (keyBook K) ord 1 firstTree A B
      (OnOmegaKey φ (jobKO (X := X') Ap pU (pKOv Pl) bs wt rd).toRun.toTest
        (simOmegaKey (stateAtOmegaKey Xs N Pl Ap pU)) 1)
      (budBoth (simOmegaKey (stateAtOmegaKey Xs N Pl Ap pU))) :=
  omega_row scope hS hK _ rfl rfl _ φ firstTree fs σ hσ pre ord A B hA

end Key

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.beside_test
#print axioms ProofFile.Honest.K12.Sim2.beside_guard
#print axioms ProofFile.Honest.K12.Sim2.first_rng
#print axioms ProofFile.Honest.K12.Sim2.shared_tests
#print axioms ProofFile.Honest.K12.Sim2.second_own
#print axioms ProofFile.Honest.K12.Sim2.omega_sourced
#print axioms ProofFile.Honest.K12.Sim2.omega_there
#print axioms ProofFile.Honest.K12.Sim2.find_omega
#print axioms ProofFile.Honest.K12.Sim2.spent_omega_full
#print axioms ProofFile.Honest.K12.Sim2.omega_row
#print axioms ProofFile.Honest.K12.Sim2.place_KO_bite
#print axioms ProofFile.Honest.K12.Sim2.omega_row_at_half
