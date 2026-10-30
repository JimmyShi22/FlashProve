-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/ScriptCopyBridges.lean: the closing of a segment (K10): THREE PUBLIC BRIDGES between the terms in which a law on the first
chain's script speaks of a code switch's messages (`switchNo`, Honest/K2/Law/SwitchNo.lean; `switchPar`, Honest/K2/SeatedL.lean; `seatAtMember`,
Honest/K1/Seated.lean) and the terms of this folder's record on the switch's sending (`fxAt`, Pay/XchSwitchPub.lean; `switchSent`; `seatSw`,
Pay/XchSeatsAt.lean). Public numbers and seats alone: no coin, input or run occurs.

  **`bridge_no`**, **`bridge_rounds`**   under the head, at every place p: the number where the written list of places first bears p's place is the
                    number where the chain's own list does; so the rounds in front of the one are `fxAt cF p`
  **`bridge_size`**   at every p, with no hypothesis: the switch's sending, as the shared sending's plan, has just the switch's messages
  `copySeatTest`, `copySeat_written`, `copySeat_bent`   a closed test, by Lean's kernel, at each written place of a link below 25, at each message
                    n: the written list of all seats has a seat q of "link l, moment 0" at the place n, and the seat at which the sending's
                    own laying into trees puts message n, behind the written count of trees in front, is (q.j, q.t + e), e = 0. THE TEST
                    CAN FAIL: at e = 1 it rejects at every such place
  **`bridge_seat_written`**   under the head, at a written place of a link below 25, at each message n: `seatAtMember cF.blocksInOrder (switchNo p)
                    (switchPar p) n = seatSw Zp p n`
  `mem_written`     under the head and the maker's return A: a place of the kind at A's own public part and ground is a written place
  **`bridge_seat`**   the same at such a place

Limits. The head and the maker's return are premises. THE THIRD BRIDGE IS SHOWN AT LINKS BELOW 25 ALONE: of a place of a link from 25 on nothing
is said. The full size and the older hash alone. This file proves no property of a prover or a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSeatsAt
import Johnson.Desc.ProofFile.Honest.K10.Pay.XchSwitchPub
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchNo
import Johnson.Desc.ProofFile.Honest.K2.Law.Counts
import Johnson.Desc.ProofFile.Honest.AtHeadGround

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (treesTold)
open VerifiableInference.Desc.First.K2Ties (toldFull)
open VerifiableInference.Desc.K1 (seatOfMsg)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open ProofFile.Honest
open ProofFile.Honest.K1 (seatAtMember)
open ProofFile.Honest.K2 (SwitchPlace switchPlaces switchSent switchSeatIn switchPar sendingPar_sent)
open ProofFile.Honest.K2.Law (placesW switchNo places_at_head treesTo_at_head)
open ProofFile.Honest.K10 (fxAt seatSw)

/-- **The switch's sending, as the shared sending's plan, has just the switch's messages.** -/
theorem bridge_size (p : SwitchPlace) : (switchPar p).sent.size = (switchSent p.sizes p.others).size := by
  show (ProofFile.Honest.K2.sendingPar p.sizes.codes (switchSent p.sizes p.others)).sent.size = _
  rw [sendingPar_sent]

/-- The test at one written place. e: a number added to the tenant that is asked for: 0 in the test. -/
def copySeatTest (e : Nat) (p : SwitchPlace) : Bool :=
  (List.range (switchSent p.sizes p.others).size).all fun n =>
    match switchSeatIn P5T.seatsAllFull p.link n with
    | some q => decide (seatOfMsg (switchPar p) (treesTold toldFull (switchNo p)) n = (q.j, q.t + e))
    | none => false

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- **At each written place of a link below 25 the sending's own seats are the plan's.** -/
theorem copySeat_written : (placesW.all fun p => decide (25 ≤ p.link) || copySeatTest 0 p) = true := by decide +kernel

set_option maxRecDepth 10000000 in
set_option maxHeartbeats 0 in
/-- The test can fail. -/
theorem copySeat_bent : (placesW.any fun p => decide (p.link < 25) && copySeatTest 1 p) = false := by decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The two numbers of a switch's border are one.** -/
theorem bridge_no (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p : SwitchPlace) : switchNo p = borderNo cF.blocksInOrder p.place :=
  (K1.borderNo_written h p.place).symm

/-- **So are the two counts of rounds in front.** -/
theorem bridge_rounds (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (p : SwitchPlace) :
    0 + roundsTo cF.blocksInOrder (switchNo p) = fxAt cF p := by
  unfold fxAt
  rw [K1.borderNo_written h]

/-- **The two seats of a switch's message are one**, at a written place of a link below 25. -/
theorem bridge_seat_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {p : SwitchPlace} (hp : p ∈ placesW)
    (hl : p.link < 25) {n : Nat} (hn : n < (switchSent p.sizes p.others).size) :
    seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n = seatSw Zp p n := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have t := List.all_eq_true.1 copySeat_written p hp
  rw [Bool.or_eq_true, decide_eq_true_eq] at t
  have t1 : copySeatTest 0 p = true := t.resolve_left (by omega)
  unfold copySeatTest at t1
  have t2 := List.all_eq_true.1 t1 n (List.mem_range.2 hn)
  have w2 : P5J.At.pseatsAll Zp = P5T.seatsAllFull := (P5J.AtMg.seats_written h.toAtMg).2.1
  show seatOfMsg (switchPar p) (treesTo cF.blocksInOrder (switchNo p)) n = _
  rw [treesTo_at_head h.toAtMg O]
  unfold seatSw
  rw [w2]
  cases hq : switchSeatIn P5T.seatsAllFull p.link n with
  | none =>
    rw [hq] at t2
    cases t2
  | some q =>
    rw [hq] at t2
    exact of_decide_eq_true t2

/-- A place of the kind at the maker's own public part and ground is a written place. -/
theorem mem_written {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) : p ∈ placesW := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨-, eG, -⟩ := atPure_at_laid_ground h.laid O.blank hA
  rw [eG, places_at_head h.toAtMg O] at hp
  exact hp

/-- **The two seats of a switch's message are one**, at a place of the kind at the maker's return, of a link below 25. -/
theorem bridge_seat {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : AtMgA OnBytes.secondHashFunction Z D r A.Z Np cF x) (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {p : SwitchPlace} (hp : p ∈ switchPlaces A.Z A.G) (hl : p.link < 25) {n : Nat}
    (hn : n < (switchSent p.sizes p.others).size) :
    seatAtMember cF.blocksInOrder (switchNo p) (switchPar p) n = seatSw A.Z p n :=
  bridge_seat_written h (mem_written h hA hp) hl hn

end AtFullSide.K10

#print axioms AtFullSide.K10.bridge_size
#print axioms AtFullSide.K10.copySeat_written
#print axioms AtFullSide.K10.copySeat_bent
#print axioms AtFullSide.K10.bridge_no
#print axioms AtFullSide.K10.bridge_rounds
#print axioms AtFullSide.K10.bridge_seat_written
#print axioms AtFullSide.K10.mem_written
#print axioms AtFullSide.K10.bridge_seat
