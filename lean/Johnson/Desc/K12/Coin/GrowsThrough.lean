-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GrowsThrough.lean: **THE STATEMENT BEHIND A YES OF A PROXIMITY TEST HAS GROWN OUT OF THE ONE IN FRONT, AT THE SHARED CHAIN's TWO SEATS.** Statements; each proof is k12_grows (Johnson/Desc/K12/Law/GrowsTest.lean: no premise
but the yes) carried through the seat's two doors. NO NEW MATHEMATICS.
  seat_grows · onGu_grows · onGomega_grows.
A KIN, NOT AT THIS GROUND: Seat.tests_grow (TestsGrow.lean, a file of this project that is not in this library) says the like of the list Seat.tests N; as reported, not shown here, it has not been compiled over the base (N).
What for: the premise on a message's own sample's rows (SampleRides, Johnson/Desc/K14/Law/LedgerOne.lean) rides back "where the statement has grown": HrowsNine.lean's hG.
Limits. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.K12.Law.GrowsTest
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.SeatLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.JointK H2K.Sw H2K.Out
open _root_.Desc.K14 (St Lin)

theorem seat_grows (g : Lin → Nat) (mask : Lin → Option Nat) (p : P12) (d d' : St)
    (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Block.inside (Seat.enter g mask) (proximityTestKind guardedProximityTestParts p : Blk') Seat.leave).decide d rs gs =
      .ok d') : Grows d.st d'.st := by
  have h' : ((Seat.enter g mask d).bind fun t =>
      ((proximityTestKind guardedProximityTestParts p : Blk').decide t rs gs).bind (Seat.leave d)) = .ok d' := h
  obtain ⟨t, ht, h'⟩ := (Seat.ebind_ok _ _ _).1 h'
  obtain ⟨t', ht', hl'⟩ := (Seat.ebind_ok _ _ _).1 h'
  cases ht
  cases hl'
  exact k12_grows p _ t' rs gs ht'

/-- **AT THE TEST ON G_u.** -/
theorem onGu_grows (p : P12) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGu (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') : Grows d.st d'.st :=
  seat_grows _ _ p d d' rs gs h

/-- **AT THE TEST ON G_omega.** -/
theorem onGomega_grows (p : P12) (d d' : St) (rs : List Fmt.RoundView) (gs : Gs)
    (h : (Seat.onGomega (proximityTestKind guardedProximityTestParts p : Blk')).decide d rs gs = .ok d') : Grows d.st d'.st :=
  seat_grows _ _ p d d' rs gs h

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.onGu_grows
#print axioms VerifiableInference.Desc.K12.Coin.onGomega_grows
