-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/TidyThrough.lean: **"TIDY IN FRONT, TIDY BEHIND" OVER A YES OF A PROXIMITY TEST, AT THE SHARED CHAIN's TWO SEATS.** Statements; each proof is calls of what lies. NO NEW MATHEMATICS.

What for. At the shared chain's borders 9, 10 and behind, three debts ask that the record's statement is in order (Means.InOrder: each open row has passed the tests of the adding at its group; each sample row lies on its own message): "a class
of rows reads the words of the test's members alone" (the ledger's hcong at blocks 9 | 10: cong_nine | cong_ten) · "three classes of rows ride back over the test on G_u" (HrowsNine.lean) · the first clause of the last chain's door.
The walk (Johnson/Desc/Tidy/Chains.lean: shared_steps) carries "tidy" along the shared chain's blocksInOrder list UNDER A NAMED PREMISE ON THE TWO TESTS. K12's files hold both halves of that premise: a yes of the test's block is a
run of the ground's plain calls (k12_calls, Johnson/Desc/K12/Law/Calls.lean: no premise) · such a run is a walk, and a walk keeps "tidy" (calls_walk | calls_tidy, Johnson/Desc/K12/Law/CallsWalkG.lean: where the codes' lengths are in order).
Here the two are joined and carried through the seats' doors.
  k12_walk · k12_tidy       at the kind's own record.
  seat_walk · seat_tidy     through Seat.enter g mask | Seat.leave, at whatever g and mask.
  **onGu_tidy | onGomega_tidy** · onGu_inOrder | onGomega_inOrder   at the two seats.
Premise: Codes.lengthsOk at the record's codes: a test with code on public data (the fold's road asks it of the plan: "the codes' lengths").
Limits. That any statement in front is tidy is not said. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Law.Calls
import Johnson.Desc.K12.Law.CallsWalkG
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open OnBytes.Means (Tidy Walk InOrder)
open _root_.Desc.K14 (St Lin)

section
variable {K : Type} [CommRing K] (ρ : OnBytes.Model.Reading K)

/-- **A yes of the test is a walk.** -/
theorem k12_walk (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hl : t0.st.codes.lengthsOk = true) :
    Walk ρ t0.st tE.st :=
  (calls_walk ρ (k12_calls p t0 tE rs gs h [] []) hl).1

/-- Through a seat's doors. -/
theorem seat_walk (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') (hl : d.st.codes.lengthsOk = true) : Walk ρ d.st d'.st := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl'⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl'
  exact k12_walk ρ p _ t' rs gs ht' hl

end

/-- **Tidy in front, tidy behind**, at the kind's own record. -/
theorem k12_tidy (p : P12) (t0 tE : T12) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (proximityTestKind guardedProximityTestParts p : Blk').decide t0 rs gs = .ok tE) (hl : t0.st.codes.lengthsOk = true)
    (hT : Tidy t0.st) : Tidy tE.st :=
  (k12_walk OnBytes.Model.Reading.gl p t0 tE rs gs h hl).tidy hT

theorem seat_tidy (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') (hl : d.st.codes.lengthsOk = true) (hT : Tidy d.st) : Tidy d'.st :=
  (seat_walk OnBytes.Model.Reading.gl g mask p d d' rs gs h hl).tidy hT

/-- **AT THE TEST ON G_u.** -/
theorem onGu_tidy (p : P12) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (hT : Tidy d.st) : Tidy d'.st :=
  seat_tidy _ _ p d d' rs gs h hl hT

/-- **AT THE TEST ON G_omega.** -/
theorem onGomega_tidy (p : P12) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (hT : Tidy d.st) : Tidy d'.st :=
  seat_tidy _ _ p d d' rs gs h hl hT

theorem onGu_inOrder (p : P12) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (hT : Tidy d.st) : InOrder d'.st :=
  (onGu_tidy p d d' rs gs h hl hT).inOrder

theorem onGomega_inOrder (p : P12) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d')
    (hl : d.st.codes.lengthsOk = true) (hT : Tidy d.st) : InOrder d'.st :=
  (onGomega_tidy p d d' rs gs h hl hT).inOrder

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_walk
#print axioms VerifiableInference.Desc.K12.Coin.k12_tidy
#print axioms VerifiableInference.Desc.K12.Coin.onGu_tidy
#print axioms VerifiableInference.Desc.K12.Coin.onGomega_tidy
#print axioms VerifiableInference.Desc.K12.Coin.onGu_inOrder
#print axioms VerifiableInference.Desc.K12.Coin.onGomega_inOrder
