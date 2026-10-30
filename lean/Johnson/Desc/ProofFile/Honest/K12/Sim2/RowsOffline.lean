-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/RowsOffline.lean: ALL FOUR ROWS ARE CONDITIONAL ON THEIR On AT A RUN, OF WHICH NOTHING IS PAID HERE.
K12's FOUR ROWS IN THE OFFLINE ROWS' ONE FORM (offlineRows, laidSimulators: E2E/OfflineSides.lean). The twin of key_k1_pays_offline.

  onU_is, onOmega_is   T1's two places are the rows' numbers
  k12_first, k12_shared, k12_second   of the rows that offlineRows lays, those of the kind K12 are the four tests'
  K12Laid           what is laid at the four places
  k12Lists, k12Letters, k12_laid   a value of them, over any value of the other lists and letters
  key_k12_pays_offline   the three chains at their fixed letters: preOf, face, order, tree
  key_k12_first, key_k12_shared, key_k12_second   at the key's description, book and the four jobs: every side has Good, at
                    the letters that c lays at the four places: hc, hb bind c there: On is NOT True: whoever lays c takes on OnEntry and OnOmegaKey
                    at a run, unpaid here. pre, face, order and firstTree are free; each chain's instance is read off.

Stands on KeyProver. T1's two places read the same by their text, at another state of T1 than this ride's.
NO PROPERTY IS CLAIMED.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowTies
import Johnson.Desc.ProofFile.Honest.K12.Sim2.RowOwnKey
import E2E.OfflineSides

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Place FileDescription)
open VerifiableInference.Desc.Key (Xi Source LaterPlaces)
open VerifiableInference.Desc.K12 (P12 T12)
open OnBytes (TableKey)
open AtPublicFiles.KeyFile (KeyInst KeyParts keyProver keyProver_first In1 In2 randK14 sharedChainProverSidesInOrder)
open AtPublicFiles.KeyLay (withTests bsOf stOf wtOf rdOf jobKU jobKO jobKWAt)
open AtPublicFiles.KeyThread (rangesTestJob)
open AtPublicFiles.KeyBook (keyBook fullPub KeyPub rngPlace foldedTestPlace omegaTestPlace ownTestPlace)
open AtPublicFiles.AtFiles (keyFileDescription KeySourced)
open AtPublicFiles.OfflineRows
open ProofFile.Honest ProofFile.Honest.K12
open ProofFile.Honest.K12.Light (askOf simLocU sentOf budBoth OnOmegaKey)
open H2K.Member (piKRFull piKWFull codesKeyFull)

/-- T1's place of the test on G_u is the row's. -/
theorem onU_is (Pl : LaterPlaces) : AtPublicFiles.AtFiles.HonestTerm.offlineTestParametersOnU Pl = pKU Pl := rfl

/-- T1's place of the test on G_omega is the row's. -/
theorem onOmega_is (Pl : LaterPlaces) : AtPublicFiles.AtFiles.HonestTerm.offlineTestOnOmega Pl = pKOv Pl := rfl

section
variable {W₀ Rc X₀ X Wk : Type} (Fx : FileDescription KeyInst) (Bk : ProverCoinCounts) (K : KeyParts W₀ Rc X₀ X Wk)
  (hK : K.AtAll) (T : TheirSimulators) (c : ConditionsByChain Fx Bk W₀ Rc TableKey Unit X₀ X)
include hK

/-- **The first chain's row of the kind K12 is the test on the ranges.** -/
theorem k12_first :
    ∀ L ∈ (offlineRows Fx Bk K (laidSimulators K T) c).first, L.place.kind = .K12 →
      L.place = rngPlace ∧ L.row = partsBeside K.rng.parts T.rangesTest ∧
        L.On = (c.first rngPlace).atPart ∧ L.bud = (c.first rngPlace).positions := by
  intro L hL hk
  have hL' : L ∈ AtPublicFiles.OfflineRows.rowsAt (Cl := Fx.Cl) (laidSimulators K T).byChain.first c.first (keyProver K).first :=
    hL
  unfold AtPublicFiles.OfflineRows.rowsAt at hL'
  rw [keyProver_first] at hL'
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hL'
  have h := hK.first
  rcases hL' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have e : K.idx.P.place.kind = .K12 := hk
    rw [h.idx] at e
    cases e
  · have e : K.msg.P.place.kind = .K12 := hk
    rw [h.msg] at e
    cases e
  · have e : K.look0.place.kind = .K12 := hk
    rw [h.look0] at e
    cases e
  · have e : K.look1.place.kind = .K12 := hk
    rw [h.look1] at e
    cases e
  · refine ⟨h.rng, ?_, ?_, ?_⟩
    · show partsBeside K.rng.parts ((laidSimulators K T).byChain.first K.rng.place) = _
      rw [h.rng]
      rfl
    · show (c.first K.rng.place).atPart = _
      rw [h.rng]
      rfl
    · show (c.first K.rng.place).positions = _
      rw [h.rng]
      rfl
  · have e : (K13.k13Place K.batt).kind = .K12 := hk
    rw [h.batt] at e
    cases e
  · have e : K.w.P.place.kind = .K12 := hk
    rw [h.w] at e
    cases e

/-- **The shared chain's rows of the kind K12 are the tests on G_u and on G_omega.** -/
theorem k12_shared :
    ∀ L ∈ (offlineRows Fx Bk K (laidSimulators K T) c).shared, L.place.kind = .K12 →
      (L.place = foldedTestPlace ∧ L.row = partsBeside K.onU.parts T.testOnFoldedRow ∧
        L.On = (c.shared foldedTestPlace).atPart ∧ L.bud = (c.shared foldedTestPlace).positions) ∨
      (L.place = omegaTestPlace ∧ L.row = partsBeside K.onOmega.parts T.testOnOmega ∧
        L.On = (c.shared omegaTestPlace).atPart ∧ L.bud = (c.shared omegaTestPlace).positions) := by
  intro L hL hk
  have hL' : L ∈ AtPublicFiles.OfflineRows.rowsAt (Cl := Fx.Cl) (laidSimulators K T).byChain.shared c.shared (keyProver K).shared :=
    hL
  unfold AtPublicFiles.OfflineRows.rowsAt at hL'
  obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hL'
  have hgk : g.place.kind = .K12 := hk
  have hs : (keyProver K).shared =
      sharedChainProverSidesInOrder (ProofFile.Honest.K14.proverSidesOfSharedRounds K.lin K.weights)
        (ProofFile.Honest.K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c)) ++
      [K.onU, K.onOmega] := rfl
  rw [hs] at hg
  rcases List.mem_append.1 hg with hw | ht
  · exfalso
    have hp : g.place ∈ (sharedChainProverSidesInOrder (ProofFile.Honest.K14.proverSidesOfSharedRounds (W₀ := W₀) (Rc := Rc) (Ky := TableKey) (X := X₀) K.lin K.weights)
        (ProofFile.Honest.K14.proverSidesOfSharedSendings K.send K.weights fun c => randK14 (K.rand c))).map (·.place) :=
      List.mem_map.2 ⟨g, hw, rfl⟩
    simp [sharedChainProverSidesInOrder, ProofFile.Honest.K14.proverSidesOfSharedRounds, ProofFile.Honest.K14.proverSidesOfSharedSendings, hK.splits] at hp
    rcases hp with e | e | e | e | e | e <;> rw [e] at hgk <;> cases hgk
  · rcases List.mem_cons.1 ht with rfl | ht
    · refine Or.inl ⟨hK.onU, ?_, ?_, ?_⟩
      · show partsBeside K.onU.parts ((laidSimulators K T).byChain.shared K.onU.place) = _
        rw [hK.onU]
        rfl
      · show (c.shared K.onU.place).atPart = _
        rw [hK.onU]
      · show (c.shared K.onU.place).positions = _
        rw [hK.onU]
    · obtain rfl := List.mem_singleton.1 ht
      refine Or.inr ⟨hK.onOmega, ?_, ?_, ?_⟩
      · show partsBeside K.onOmega.parts ((laidSimulators K T).byChain.shared K.onOmega.place) = _
        rw [hK.onOmega]
        rfl
      · show (c.shared K.onOmega.place).atPart = _
        rw [hK.onOmega]
      · show (c.shared K.onOmega.place).positions = _
        rw [hK.onOmega]

/-- **The last chain's row is the own test.** -/
theorem k12_second :
    ∀ L ∈ (offlineRows Fx Bk K (laidSimulators K T) c).second,
      L.place = ownTestPlace ∧ L.row = partsBeside K.own.parts T.ownTest ∧
        L.On = (c.second ownTestPlace).atPart ∧ L.bud = (c.second ownTestPlace).positions := by
  intro L hL
  have hL' : L ∈ AtPublicFiles.OfflineRows.rowsAt (Cl := Fx.Cl) (laidSimulators K T).byChain.second c.second [K.own] := hL
  unfold AtPublicFiles.OfflineRows.rowsAt at hL'
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hL'
  subst hL'
  refine ⟨hK.own, ?_, ?_, ?_⟩
  · show partsBeside K.own.parts ((laidSimulators K T).byChain.second K.own.place) = _
    rw [hK.own]
    rfl
  · show (c.second K.own.place).atPart = _
    rw [hK.own]
  · show (c.second K.own.place).positions = _
    rw [hK.own]

end

/-- **What is laid at the four places**: the four lists of simulators, and at each place c's On and bud. It binds T and c there. On is NOT True: it is a clause on a run, and whoever lays c takes it on. -/
structure K12Laid {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ X Wk : Type} {Bk : ProverCoinCounts}
    (Sd : KeyParts W₀ Rc X₀ X Wk) (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF)
    (grp : List (List Nat)) (fst : Nat) (T : TheirSimulators)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X) : Prop where
  hT : T.rangesTest = [firstSim (simRanges Xs N Pl), restSim (simRanges Xs N Pl)]
  hc : (c.first rngPlace).atPart =
    OnEntry .own (rangesTestJob Xs N Pl ent grp fst) (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first
  hb : (c.first rngPlace).positions = budBoth (simRanges Xs N Pl)
  hTU : T.testOnFoldedRow =
    [firstSim (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1),
     restSim (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1)]
  hTO : T.testOnOmega =
    [firstSim (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))),
     restSim (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl)))]
  hcU : (c.shared foldedTestPlace).atPart =
    OnEntry .shared (jobKU (X := X₀) Sd.send (pKU Pl) (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
      (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1) codesKeyFull 1 (pKU Pl).nums.first
  hbU : (c.shared foldedTestPlace).positions =
    budBoth (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1)
  hcO : (c.shared omegaTestPlace).atPart =
    OnOmegaKey .shared (jobKO (X := X₀) Sd.send (pKU Pl) (pKOv Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
      (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))) 1
  hbO : (c.shared omegaTestPlace).positions =
    budBoth (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl)))
  hTW : T.ownTest = [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)]
  hcW : (c.second ownTestPlace).atPart =
    OnOwnTestEntry .own (jobKWAt Xs N Pl Sd.idx Sd.w Sd.send id
        (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest
      (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first
  hbW : (c.second ownTestPlace).positions = budBoth (simOwnKey Xs N Pl)


/-- **K12's four lists laid into any value of the others.** -/
def k12Lists {W₀ Rc X₀ X Wk : Type} (T₀ : TheirSimulators) (Xs : Source) (N : H2U.PlaceNums) (Pl : LaterPlaces)
    (Sd : KeyParts W₀ Rc X₀ X Wk) : TheirSimulators :=
  { T₀ with
    rangesTest := [firstSim (simRanges Xs N Pl), restSim (simRanges Xs N Pl)]
    testOnFoldedRow :=
      [firstSim (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1),
       restSim (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1)]
    testOnOmega :=
      [firstSim (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))),
       restSim (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl)))]
    ownTest := [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)] }

/-- **K12's letters laid into any value of the others**, at the four places. -/
def k12Letters {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ X Wk : Type} {Bk : ProverCoinCounts}
    (c₀ : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X)
    (Sd : KeyParts W₀ Rc X₀ X Wk) (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF)
    (grp : List (List Nat)) (fst : Nat) :
    ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X where
  first := fun p => if p == rngPlace then
      { c₀.first p with
        atPart := OnEntry .own (rangesTestJob Xs N Pl ent grp fst) (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first
        positions := budBoth (simRanges Xs N Pl) }
    else c₀.first p
  shared := fun p => if p == foldedTestPlace then
      { c₀.shared p with
        atPart := OnEntry .shared (jobKU (X := X₀) Sd.send (pKU Pl) (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
          (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1) codesKeyFull 1 (pKU Pl).nums.first
        positions := budBoth (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1) }
    else if p == omegaTestPlace then
      { c₀.shared p with
        atPart := OnOmegaKey .shared
          (jobKO (X := X₀) Sd.send (pKU Pl) (pKOv Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
          (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))) 1
        positions := budBoth (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))) }
    else c₀.shared p
  second := fun p => if p == ownTestPlace then
      { c₀.second p with
        atPart := OnOwnTestEntry .own (jobKWAt Xs N Pl Sd.idx Sd.w Sd.send id
            (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest
          (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first
        positions := budBoth (simOwnKey Xs N Pl) }
    else c₀.second p

/-- **K12Laid has a member**, over any value of the other lists and letters. -/
theorem k12_laid {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ X Wk : Type} {Bk : ProverCoinCounts}
    (T₀ : TheirSimulators) (c₀ : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X)
    (Sd : KeyParts W₀ Rc X₀ X Wk) (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF)
    (grp : List (List Nat)) (fst : Nat) :
    K12Laid Sd ent grp fst (k12Lists T₀ Xs N Pl Sd) (k12Letters c₀ Sd ent grp fst) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {Xs : Source} {N : H2U.PlaceNums} {Pl : LaterPlaces} {W₀ Rc X₀ X Wk : Type}
  (scope : VerifierAndGoals.InScope Z = true) (hS : KeySourced Z Xs N Pl) {Kp : KeyPub} (hKp : fullPub = some Kp)
  (Sd : KeyParts W₀ Rc X₀ X Wk) (ent : Local W₀ Rc Xi Unit → Nat → Nat → OnBytes.Slice.GF)
  (grp : List (List Nat)) (fst : Nat)
  (hK : (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst).AtAll) (T : TheirSimulators)
include scope hS hKp hK

/-- **At the key's description and book: row 5.** hT, hc, hb: what is laid at the place. -/
theorem key_k12_first
    (c : ConditionsByChain (keyFileDescription Xs N Pl) (keyBook Kp) W₀ Rc TableKey Unit X₀ X)
    (φ : Face (In1 W₀ Rc) (In1 W₀ Rc) (keyFileDescription Xs N Pl).XiPub)
    (hT : T.rangesTest = [firstSim (simRanges Xs N Pl), restSim (simRanges Xs N Pl)])
    (hc : (c.first rngPlace).atPart =
      OnEntry φ (rangesTestJob Xs N Pl ent grp fst) (simRanges Xs N Pl) codesKeyFull 0 piKRFull.nums.first)
    (hb : (c.first rngPlace).positions = budBoth (simRanges Xs N Pl)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) (keyBook Kp) (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).first,
      L.place.kind = .K12 → ∀ σ, L.side (keyFileDescription Xs N Pl).first.blocksInOrder [] = some σ →
      ∀ pre ord firstTree, ∃ A' B', Good pre φ σ (keyBook Kp) ord 0 firstTree A' B' L.On L.bud := by
  intro L hL hk σ hσ pre ord firstTree
  obtain ⟨c1, c2, c3, c4⟩ := k12_first _ _ _ hK T c L hL hk
  have hrow : L.row = testPairs (rangesTestJob Xs N Pl ent grp fst) (simRanges Xs N Pl) := by
    rw [c2, hT]
    exact beside_test _ _
  have hσ' : testSide (keyFileDescription Xs N Pl).first.blocksInOrder (rangesTestJob Xs N Pl ent grp fst) (simRanges Xs N Pl) [] =
      some σ := by
    unfold Lettered.side at hσ
    have hr : (rangesTestJob (X' := X) Xs N Pl ent grp fst).p.place = rngPlace := hK.first.rng
    rw [c1, hrow, ← hr] at hσ
    exact hσ
  refine ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
  rw [c3, c4, hc, hb]
  exact ranges_row scope hS hKp ent grp fst φ firstTree [] σ hσ' pre ord _ _ fun _ _ _ _ h => h

/-- **Rows 14 and 15.** -/
theorem key_k12_shared (c : ConditionsByChain (keyFileDescription Xs N Pl) (keyBook Kp) W₀ Rc TableKey Unit X₀ X)
    (φ : Face Empty (In2 W₀ Rc) TableKey)
    (hTU : T.testOnFoldedRow =
      [firstSim (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1),
       restSim (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1)])
    (hTO : T.testOnOmega =
      [firstSim (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))),
       restSim (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl)))])
    (hcU : (c.shared foldedTestPlace).atPart =
      OnEntry φ (jobKU (X := X₀) Sd.send (pKU Pl) (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
        (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1) codesKeyFull 1 (pKU Pl).nums.first)
    (hbU : (c.shared foldedTestPlace).positions =
      budBoth (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1))
    (hcO : (c.shared omegaTestPlace).atPart =
      OnOmegaKey φ (jobKO (X := X₀) Sd.send (pKU Pl) (pKOv Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
        (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))) 1)
    (hbO : (c.shared omegaTestPlace).positions =
      budBoth (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl)))) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) (keyBook Kp) (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).shared,
      L.place.kind = .K12 → ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder [] = some σ →
      ∀ pre ord firstTree, ∃ A' B', Good pre φ σ (keyBook Kp) ord 1 firstTree A' B' L.On L.bud := by
  intro L hL hk σ hσ pre ord firstTree
  rcases k12_shared _ _ _ hK T c L hL hk with ⟨c1, c2, c3, c4⟩ | ⟨c1, c2, c3, c4⟩
  · have hrow : L.row = testPairs
        (jobKU (X := X₀) Sd.send (pKU Pl) (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
        (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1) := by
      rw [c2, hTU]
      exact beside_test _ _
    have hσ' : testSide (keyFileDescription Xs N Pl).shared.blocksInOrder
        (jobKU (X := X₀) Sd.send (pKU Pl) (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
        (simLocU Sd.send.P (sentOf Sd.send.P.S) (bsOf Sd) (pKU Pl) 1) [] = some σ := by
      unfold Lettered.side at hσ
      rw [c1, hrow, ← hK.onU] at hσ
      exact hσ
    refine ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    rw [c3, c4, hcU, hbU]
    exact folded_row scope hS hKp Sd.send (bsOf Sd) (stOf Sd) (wtOf Sd) (rdOf Sd) φ firstTree [] σ hσ'
      pre ord _ _ fun _ _ _ _ h => h
  · have hrow : L.row = ProofFile.Honest.guardRow (testPairs
              (jobKO (X := X₀) Sd.send (pKU Pl) (pKOv Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
              (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl)))) := by
      rw [c2, hTO]
      exact beside_guard _ _
    have hσ' : Side.seated (keyFileDescription Xs N Pl).shared.blocksInOrder
        (jobKO (X := X₀) Sd.send (pKU Pl) (pKOv Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest.p.place
        (ProofFile.Honest.guardRow (testPairs
                (jobKO (X := X₀) Sd.send (pKU Pl) (pKOv Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd)).toRun.toTest
                (simOmegaKey (stateAtOmegaKey Xs N Pl Sd.send (pKU Pl))))) [] = some σ := by
      unfold Lettered.side at hσ
      rw [c1, hrow, ← hK.onOmega] at hσ
      exact hσ
    refine ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
    rw [c3, c4, hcO, hbO]
    exact omega_row_at_half scope hS hKp Sd.send (pKU Pl) (bsOf Sd) (wtOf Sd) (rdOf Sd) φ firstTree [] σ hσ'
      pre ord _ _ fun _ _ _ _ h => h

/-- **Row 16.** -/
theorem key_k12_second (c : ConditionsByChain (keyFileDescription Xs N Pl) (keyBook Kp) W₀ Rc TableKey Unit X₀ X)
    (φ : Face (In1 W₀ Rc) (In1 W₀ Rc) (keyFileDescription Xs N Pl).XiPub)
    (hT : T.ownTest = [firstSim (simOwnKey Xs N Pl), restSim (simOwnKey Xs N Pl)])
    (hc : (c.second ownTestPlace).atPart =
      OnOwnTestEntry φ (jobKWAt Xs N Pl Sd.idx Sd.w Sd.send id
          (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest
        (simOwnKey Xs N Pl) codesKeyFull 2 piKWFull.nums.first)
    (hb : (c.second ownTestPlace).positions = budBoth (simOwnKey Xs N Pl)) :
    ∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) (keyBook Kp) (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).second,
      L.place.kind = .K12 → ∀ σ, L.side (keyFileDescription Xs N Pl).second.blocksInOrder [] = some σ →
      ∀ pre ord firstTree, ∃ A' B', Good pre φ σ (keyBook Kp) ord 2 firstTree A' B' L.On L.bud := by
  intro L hL _ σ hσ pre ord firstTree
  obtain ⟨c1, c2, c3, c4⟩ := k12_second _ _ _ hK T c L hL
  have hrow : L.row = ProofFile.Honest.guardRow (testPairs
            (jobKWAt Xs N Pl Sd.idx Sd.w Sd.send id
              (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest
            (simOwnKey Xs N Pl)) := by
    rw [c2, hT]
    exact beside_guard _ _
  have hσ' : Side.seated (keyFileDescription Xs N Pl).second.blocksInOrder
      (jobKWAt Xs N Pl Sd.idx Sd.w Sd.send id
        (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest.p.place
      (ProofFile.Honest.guardRow (testPairs
              (jobKWAt Xs N Pl Sd.idx Sd.w Sd.send id
                (askOf Sd.send (fun w => Sd.weights w.w₀) fun w => randK14 (Sd.rand w.rc))).toRun.toTest
              (simOwnKey Xs N Pl))) [] = some σ := by
    unfold Lettered.side at hσ
    rw [c1, hrow, ← hK.own] at hσ
    exact hσ
  refine ⟨fun _ _ _ _ => False, fun _ _ _ _ => False, ?_⟩
  rw [c3, c4, hc, hb]
  exact own_key_row_at_half scope hS hKp Sd.idx Sd.w Sd.send id _ φ firstTree [] σ hσ' pre ord _ _
    fun _ _ _ _ h => h

/-- **KindPays .K12's three conjuncts at the key's description, at their fixed letters.** Bk: a book that is the key's. -/
theorem key_k12_pays_offline {Bk : ProverCoinCounts} (hBk : Bk = keyBook Kp)
    (c : ConditionsByChain (keyFileDescription Xs N Pl) Bk W₀ Rc TableKey Unit X₀ X)
    (hL : K12Laid Sd ent grp fst T c) :
    (∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).first,
      L.place.kind = .K12 → ∀ σ, L.side (keyFileDescription Xs N Pl).first.blocksInOrder [] = some σ →
      ∃ A' B', Good (preOf 0 0 (earlierOf (keyFileDescription Xs N Pl) 0) (keyFileDescription Xs N Pl).first.blocksInOrder L.place) .own σ Bk
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 0 0 A' B' L.On L.bud) ∧
    (∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).shared,
      L.place.kind = .K12 → ∀ σ, L.side (keyFileDescription Xs N Pl).shared.blocksInOrder [] = some σ →
      ∃ A' B', Good (preOf 1 0 (earlierOf (keyFileDescription Xs N Pl) 1) (keyFileDescription Xs N Pl).shared.blocksInOrder L.place) .shared σ Bk
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 1 0 A' B' L.On L.bud) ∧
    (∀ L ∈ (offlineRows (keyFileDescription Xs N Pl) Bk (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst)
        (laidSimulators (withTests Sd Xs N Pl (pKU Pl) (pKOv Pl) ent grp fst) T) c).second,
      L.place.kind = .K12 → ∀ σ, L.side (keyFileDescription Xs N Pl).second.blocksInOrder [] = some σ →
      ∃ A' B', Good (preOf 2 (keyFileDescription Xs N Pl).lastChainFirstTreeNumber (earlierOf (keyFileDescription Xs N Pl) 2)
          (keyFileDescription Xs N Pl).second.blocksInOrder L.place) .own σ Bk
        (ProofFile.Honest.orderOf (keyFileDescription Xs N Pl)) 2 (keyFileDescription Xs N Pl).lastChainFirstTreeNumber A' B' L.On L.bud) := by
  subst hBk
  exact ⟨fun L hm hk σ hσ => key_k12_first scope hS hKp Sd ent grp fst hK T c .own hL.hT hL.hc hL.hb L hm hk σ hσ _ _ _,
    fun L hm hk σ hσ => key_k12_shared scope hS hKp Sd ent grp fst hK T c .shared hL.hTU hL.hTO hL.hcU hL.hbU
      hL.hcO hL.hbO L hm hk σ hσ _ _ _,
    fun L hm hk σ hσ => key_k12_second scope hS hKp Sd ent grp fst hK T c .own hL.hTW hL.hcW hL.hbW L hm hk σ hσ _ _ _⟩

end

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.onU_is
#print axioms ProofFile.Honest.K12.Sim2.onOmega_is
#print axioms ProofFile.Honest.K12.Sim2.k12_first
#print axioms ProofFile.Honest.K12.Sim2.k12_shared
#print axioms ProofFile.Honest.K12.Sim2.k12_second
#print axioms ProofFile.Honest.K12.Sim2.key_k12_first
#print axioms ProofFile.Honest.K12.Sim2.key_k12_shared
#print axioms ProofFile.Honest.K12.Sim2.key_k12_second
#print axioms ProofFile.Honest.K12.Sim2.k12_laid
#print axioms ProofFile.Honest.K12.Sim2.key_k12_pays_offline
