-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptHeard.lean: the closing of a segment (K10): AT A CODE SWITCH's OWN MESSAGES THE BASE PROVER's DATA OF THE MAIN
ROWS READ NO CHALLENGE: at each place p of the code switch and each own message m of its sending but the last (the next fold's
fresh mask), the data `widerRows S A.Z A.G` say at the address `p.ownAddr m` that 0 challenges have been heard.

  `ownAllB`, `ownAllW`   a closed test, by Lean's kernel, at the written places and the written request: each such m is the rank of a
                        message of moment 0 of the segment into which the switch leads. `ownAll_can_fail`: at the written request
                        with its segments struck the test says no at the first written place
  `own_seat_first`      under the hypothesis: such an address has a seat among the switches' own messages
  **`heard_zero_first`**  THE STATEMENT

By: `switchSeat_own` (Johnson/Desc/ProofFile/Honest/K2/Law/OwnDataApart.lean); `places_at_head` (Honest/K2/Law/PlacesWritten.lean);
`shape_at_base` (AtFullSide/K1/OwnAtPlanNumbers.lean). The data are a join of two (`withSwitchData`, Honest/K2/OwnData.lean): at a
seat of a switch's own message the join reads the switches' own data, which say 0 everywhere.

Limits. A public number alone: nothing on what the data hold. The hypothesis and the maker's return are premises. A closed fact by
Lean's kernel. The full size and the older hash alone. No property is claimed.
-/
import AtFullSide.K1.OwnAtPlanNumbers
import Johnson.Desc.ProofFile.Honest.K2.Law.OwnDataApart
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open VerifiableInference.PlanWritten (proofSizedFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchSent switchSeat)
open ProofFile.Honest.K2.Law (placesW)

/-- Each own message of the sending but the last is the rank of a message of moment 0 of the segment into which the switch
leads. -/
def ownAllB (s : OnBytes.Params.ReqShape) (p : SwitchPlace) : Bool :=
  (List.range (switchSent p.sizes p.others).size).all fun m =>
    !decide (1 + p.sizes.kept.length + m + 1 < (switchSent p.sizes p.others).size) ||
      (msgNo s p.link 0 m).isSome

set_option maxRecDepth 1000000 in
/-- At the written places and the written request the test says yes. -/
theorem ownAllW : (placesW.all (ownAllB proofSizedFull.request)) = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- The test can fail: at the written request with its segments struck, at the first written place. -/
theorem ownAll_can_fail :
    ((placesW.take 1).all (ownAllB { proofSizedFull.request with link := [] })) = false := by decide +kernel

variable {W₀ : Type} {Z : VerifierAndGoals.PublicFiles} {I : WiderIn W₀} {S : OnBytes.HonestTrace.Sz} {Op : OnlineProverArguments}
  {A : OnlineProverWithDescription W₀ IndexCommitterCoins Cells Unit Unit} {D : WholeD} {r : LPFD.Full.RunPF} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- Such an address has a seat among the switches' own messages. -/
theorem own_seat_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) {m : Nat}
    (hm : 1 + p.sizes.kept.length + m + 1 < (switchSent p.sizes p.others).size) :
    (switchSeat A.Z A.G (p.ownAddr m)).isSome = true := by
  obtain ⟨Bs, base₀, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  have hP : p ∈ placesW := by
    rw [← K2.Law.places_at_head h.toAtMg O, ← eG]
    exact hp
  have t := List.all_eq_true.1 (List.all_eq_true.1 ownAllW p hP) m (List.mem_range.2 (by omega))
  rw [decide_eq_true hm] at t
  refine K2.Law.switchSeat_own A.Z A.G p hp m ?_
  rw [K1.shape_at_base h hA]
  exact t

/-- **AT A SWITCH's OWN MESSAGES THE DATA READ NO CHALLENGE.** -/
theorem heard_zero_first (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL (onlineProverPartsInUse I OnBytes.secondHashFunction S Op) = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (ξ : ProofFile.Inst) (m : Nat)
    (hm : 1 + p.sizes.kept.length + m + 1 < (switchSent p.sizes p.others).size) :
    (widerRows S A.Z A.G ξ).heardAt (p.ownAddr m) = 0 := by
  have hs := own_seat_first h hA hp hm
  show (if (switchSeat A.Z A.G (p.ownAddr m)).isSome = true then
    (K2.switchData S A.Z A.G).heardAt (p.ownAddr m) else (K1.lotData S A.Z A.G ξ).heardAt (p.ownAddr m)) = 0
  rw [if_pos hs]
  rfl

end AtFullSide.K10

#print axioms AtFullSide.K10.ownAllW
#print axioms AtFullSide.K10.ownAll_can_fail
#print axioms AtFullSide.K10.own_seat_first
#print axioms AtFullSide.K10.heard_zero_first
