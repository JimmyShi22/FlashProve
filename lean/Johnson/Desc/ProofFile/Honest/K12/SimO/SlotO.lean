-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator at the proximity test on G_omega: the rows with their simulators.
/-
Johnson/Desc/ProofFile/Honest/K12/SimO/SlotO.lean: THE VALUE AT THE TEST ON G_omega: the simulators' job, and the list that stands where `halfO` stands: the same parts, each with its simulator, the condition `OnOmega` and the bound `budBoth`.

  `simulatorJobAtOmega`   the job: the place, the flag, the letter `stateAtOmega` at the blocks in front, the openings of the written first list
  `rowAtOmega`            the row of a job at the place
  `rowsAtOmega`           the list at a public record, under `halfO`'s own guards
  `rowsAtOmega_half`      **its halves are `halfO`**

Definitions and one equation. Nothing here says that a value meets `Good`: `omega_good` (SimO/Top.lean) says that at a seated side. No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.SimO.AtTerm
import Johnson.Desc.ProofFile.Honest.K12.SimO.DoorOmega
import Johnson.Desc.ProofFile.Honest.Thread.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open OnBytes (OracleNotice TableKey)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14 St frontBlock)
open ProofFile.Honest.K12.Light (jobAtOmega doorOmegaF colsOpened sentOf stateAtOmega omegaRow OnOmega firstListAtOmega omegaRow_half budBoth)

variable {W₀ : Type}

/-- **The simulators' job at the test on G_omega.** -/
def simulatorJobAtOmega (c : OnBytes.Model.Verify.Chains) (Q : P14) (pU pO : P12)
    (bs : List (Block St Unit)) : SimJob TableKey :=
  ⟨pO, true,
    stateAtOmega Q (sentOf Q.S) pU
      (frontBlock c :: (bs ++ [VerifiableInference.Desc.K12.Seat.onGu (proximityTestKind guardedProximityTestParts pU)])),
    firstListAtOmega.map fun x => ((ProofFile.Honest.srcOf 1 x.2).1, (ProofFile.Honest.srcOf 1 x.2).2, x.1.a)⟩

/-- A place that `four` lays for the test on G_omega is of the kind K12. -/
theorem four_O_kind {Z : Pub} {F : Four} {pO : P12} (h1 : four Z = some F) (h2 : F.O = some pO) :
    pO.place.kind = .K12 := by
  unfold four at h1
  split at h1
  · obtain rfl := Option.some.inj h1
    rename_i N hN
    obtain ⟨nO, -, rfl⟩ := ProofFile.Honest.K12.Light.omega_of_four h2
    exact congrArg (·.kind) (H2K.JointK.place_of_p12At _ _)
  · cases h1

/-- **The row of a job at the place.** -/
def rowAtOmega (J : TestJob (Common W₀ IndexCommitterCoins TableKey) Unit) (Js : SimJob TableKey) :
    Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey :=
  ⟨J.p.place, omegaRow J Js, OnOmega Face.shared J Js 1 firstListAtOmega, budBoth Js⟩

/-- **The list**, under `halfO`'s own guards. -/
def rowsAtOmega (wt : W₀ → Weights) (Z : Pub) :
    List (Unlettered Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey) :=
  ((four Z).bind fun F => F.O.bind fun pO => (sendPub Z).bind fun A =>
    (Desc.K14.blocks A.P).map fun bs =>
      rowAtOmega (jobAtOmega A pO (doorOmegaF A.P (sentOf A.P.S) bs F.U (fun w => w.key) colsOpened)
          (fun w => wt w.w₀) (fun w => randAt A.P w.rc) none).toRun.toTest
        (simulatorJobAtOmega Z.p.chains A.P F.U pO bs)).toList

/-- **Its halves are `halfO`, the pair of the base filling.** That filling is not read through here: `onlineFilling` lays the pair through `OnlineProverParts.through`, and that crossing is not in this file. -/
theorem rowsAtOmega_half (wt : W₀ → Weights) (Z : Pub) :
    (rowsAtOmega wt Z).map (·.half) = halfO wt Z := by
  unfold rowsAtOmega halfO realO jobRealO
  cases h1 : four Z with
  | none => rfl
  | some F =>
    simp only [Option.bind_some]
    cases h2 : F.O with
    | none => rfl
    | some pO =>
      simp only [Option.bind_some]
      cases h3 : sendPub Z with
      | none => rfl
      | some A =>
        simp only [Option.bind_some]
        cases h4 : Desc.K14.blocks A.P with
        | none => rfl
        | some bs =>
          simp only [Option.map_some, Option.toList_some, List.map_cons, List.map_nil]
          exact congrArg (fun x => [x]) (omegaRow_half (V := Empty) _ _)

/-- **The value of the lot with simulators.** -/
def lotAtOmega (wt : Pub → W₀ → Weights) : SLot Empty (Common W₀ IndexCommitterCoins TableKey) Unit TableKey :=
  ⟨"the test on G_omega", fun Z _ => rowsAtOmega (wt Z) Z⟩

/-- **Its lot lays `halfO`, the base filling's pair.** Not read through. -/
theorem lotAtOmega_halves (wt : Pub → W₀ → Weights) (Z : Pub) (G : Ground) :
    (lotAtOmega wt).toHLot.halves Z G = halfO (wt Z) Z :=
  rowsAtOmega_half (wt Z) Z

/-- Its rows stand at a place of the kind K12, under the head's letters. -/
theorem rowsAtOmega_kind (wt : W₀ → Weights) (Z : Pub) :
    ∀ r ∈ rowsAtOmega wt Z, r.place.kind = .K12 := by
  intro r hr
  unfold rowsAtOmega at hr
  cases h1 : four Z with
  | none =>
    rw [h1] at hr
    cases hr
  | some F =>
    rw [h1] at hr
    simp only [Option.bind_some] at hr
    cases h2 : F.O with
    | none =>
      rw [h2] at hr
      cases hr
    | some pO =>
      rw [h2] at hr
      simp only [Option.bind_some] at hr
      cases h3 : sendPub Z with
      | none =>
        rw [h3] at hr
        cases hr
      | some A =>
        rw [h3] at hr
        simp only [Option.bind_some] at hr
        cases h4 : Desc.K14.blocks A.P with
        | none =>
          rw [h4] at hr
          cases hr
        | some bs =>
          rw [h4] at hr
          simp only [Option.map_some, Option.toList_some, List.mem_singleton] at hr
          subst hr
          exact four_O_kind h1 h2

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.lotAtOmega
#print axioms ProofFile.Honest.K12.AtProof.lotAtOmega_halves
#print axioms ProofFile.Honest.K12.AtProof.rowsAtOmega_kind
#print axioms ProofFile.Honest.K12.AtProof.simulatorJobAtOmega
#print axioms ProofFile.Honest.K12.AtProof.rowAtOmega
#print axioms ProofFile.Honest.K12.AtProof.rowsAtOmega
#print axioms ProofFile.Honest.K12.AtProof.rowsAtOmega_half
