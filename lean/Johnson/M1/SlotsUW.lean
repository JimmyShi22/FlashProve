-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's rows at G_u and at the request's own test as values of the frame's lot with simulators.
/-
Johnson/M1/SlotsUW.lean: as Sim2/SlotValueL.lean at the first chain's last test: values of SLot (Thread/Rows.lean) at the test on G_u and at the request's own
test: the parts that halfU and halfW lay, each with its simulator, the condition and the bound of slot_testOnU and slot_own_test. The first is at the face φ of
the chain, a letter. Definitions and two equations: what the rows lay is what the filling lays. Nothing here says that the values meet Good. No
property of the protocol is claimed.

  simAtU, rowAtU, lotU, lotU_halves    at G_u: the row: testPairs, onFreeT, budOpened; its list is halfU
  simAtW, rowAtW, rowsW, lotW, lotW_halves   at the own test: guardRow (testPairs J Js), OnOwnTestEntry, budBoth; its list is secondW
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.SlotOwnTest
import Johnson.Desc.ProofFile.Honest.K12.Sim2.DoorWAt
import Johnson.Desc.ProofFile.Honest.K12.AtProof.HalfWAtPure
import Johnson.Desc.ProofFile.Honest.K12.OnFreeTAtHeadU
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace ProofFile.Honest.K12.Sim2
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof ProofFile.Honest.K12.Light
open H2K.Member (codesFull)
open Johnson.G (codesFull2)
open VerifiableInference.Desc (Block Chain)
open OnBytes (TableKey)

variable {W₀ X : Type}

local notation "qAt'" => VerifiableInference.Desc.K1.qAt

/-- The simulators' job at G_u, at the public part: simHeadU at the planner's places and the plan's blocks; where the public part has none, an idle job. -/
def simAtU (Z : Pub) : SimJob TableKey :=
  match H2U.placesOfMade Z.made with
  | .ok N =>
    match Desc.K14.blocks (qAt' Z N) with
    | some bs => simHeadU Z N bs
    | none => ⟨H2U.noP12 placeU, false, fun _ _ => idleT12, []⟩
  | .error _ => ⟨H2U.noP12 placeU, false, fun _ _ => idleT12, []⟩

/-- **The row at G_u.** -/
def rowAtU (φ : Face Empty (Common W₀ IndexCommitterCoins TableKey) TableKey) (Z : Pub)
    (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) : Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey :=
  ⟨J.p.place, testPairs J (simAtU Z), onFreeT φ J (simAtU Z) codesFull2 1 J.p.nums.first,
    budOpened J.p.nums.stages⟩

/-- **The value at G_u.** -/
def lotU (φ : Face Empty (Common W₀ IndexCommitterCoins TableKey) TableKey) (wt : Pub → W₀ → Weights)
    (enc : Pub → W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) :
    SLot Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey :=
  ⟨"the test on G_u", fun Z _ => (realU (wt Z) (enc Z) Z).toList.map (rowAtU φ Z)⟩

/-- **Its list is what halfU lays.** -/
theorem lotU_halves (φ : Face Empty (Common W₀ IndexCommitterCoins TableKey) TableKey) (wt : Pub → W₀ → Weights)
    (enc : Pub → W₀ → IndexCommitterCoins → ℕ → ℕ → Option (List Cb.Gl.F)) (Z : Pub) (G : Ground) :
    (lotU φ wt enc).toHLot.halves Z G = halfU (wt Z) (enc Z) Z := by
  show ((realU (wt Z) (enc Z) Z).toList.map (rowAtU φ Z)).map (·.half) = (realU (wt Z) (enc Z) Z).toList.map proverSideOfProximityTest
  rw [List.map_map]
  rfl

/-- The simulators' job at the request's own test. -/
def simAtW (o : SecondHashFunctionArgument) (Z : Pub) (N : H2U.Places4) (c : Chain P5J.TS ProofFile.Cl) : SimJob Inst :=
  ⟨(fourOf N).W, false, stateAtOwnTest o Z N c,
    (fourOf N).W.nums.first.map fun x => ((srcOf 2 x.2).1, (srcOf 2 x.2).2, x.1.a)⟩

/-- **The row at the own test, behind the guard.** -/
def rowAtW (φ : Face (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Inst) (o : SecondHashFunctionArgument) (Z : Pub)
    (N : H2U.Places4) (c : Chain P5J.TS ProofFile.Cl) (J : TestJob (Local W₀ IndexCommitterCoins Inst Cells) X) :
    Unlettered (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst :=
  ⟨J.p.place, guardRow (testPairs J (simAtW o Z N c)),
    OnOwnTestEntry φ J (simAtW o Z N c) codesFull 2 J.p.nums.first, budBoth (simAtW o Z N c)⟩

/-- **The rows**, under secondW's own guards. -/
def rowsW (φ : Face (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Inst) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    List (Unlettered (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst) :=
  match nowSharedBy (I.weights Z) Z, H2U.placesOfMade Z.made, ProofFile.onlineFirstChainAt Z with
  | .ok _, .ok N, .ok c =>
    (realW S (P5J.F0T o Z N c) VerifiableInference.Desc.K12.Seat.enterOwn O.pile (K1.lotNo o Z)
      (fun w => ⟨w.trace, I.weights Z w.w₀, w.rc⟩) (fun w => I.weights Z w.w₀)
      (fun P w => randAt P w.rc) Z G).toList.map (rowAtW φ o Z N c)
  | _, _, _ => []

/-- **The value at the own test.** -/
def lotW (φ : Face (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Inst) (I : WiderIn W₀) (o : SecondHashFunctionArgument)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) :
    SLot (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) X Inst :=
  ⟨"the request's own test", rowsW φ I o S O⟩

/-- **Its list is what secondW lays.** -/
theorem lotW_halves (φ : Face (Local W₀ IndexCommitterCoins Inst Cells) (Local W₀ IndexCommitterCoins Inst Cells) Inst) (I : WiderIn W₀)
    (o : SecondHashFunctionArgument) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) (Z : Pub) (G : Ground) :
    (lotW (X := X) φ I o S O).toHLot.halves Z G = secondW I o S O Z G := by
  show (rowsW φ I o S O Z G).map (·.half) = secondW I o S O Z G
  unfold rowsW secondW
  cases nowSharedBy (I.weights Z) Z with
  | error e => rfl
  | ok s =>
    cases H2U.placesOfMade Z.made with
    | error e => rfl
    | ok N =>
      cases ProofFile.onlineFirstChainAt Z with
      | error e => rfl
      | ok c =>
        show List.map _ (List.map _ _) = halfW _ _ _ _ _ _ _ _ _ _
        unfold halfW
        rw [List.map_map]
        refine List.map_congr_left fun J _ => ?_
        rfl

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.lotU_halves
#print axioms ProofFile.Honest.K12.Sim2.lotW_halves
