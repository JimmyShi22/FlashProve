-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameSeats.lean: THE GAME OF THE PROXIMITY TEST AT THE NAMED SEATS OF THE
SHARED AND THE THIRD CHAIN. Statements; each proof is one call of GameSeat.lean: the seat IS
`Block.inside` at its two doors, by definition.

  `k12_game_onGu`: at `Seat.onGu`, first arm (the first fold's mask came earlier).
  `k12_game_onGomega`: at `Seat.onGomega`, second arm (the first fold sends its own mask).
  `k12_game_onOwn`, `k12_game_onOwnO`: at `Seat.onOwn`, either arm.
The first chain's finish (`atFinish`): `k12_gameF2Z`, GameZ.lean.
Limits: those of GameSeat.lean. NO SOUNDNESS IS CLAIMED. Which arm a place of the plan takes is not
said here: at the other arm's place `AtPlace` | `AtPlaceOwn` fails and the law is idle. The link's
own seat is not here.

-/
import Johnson.Desc.K12.Coin.GameSeat
import Johnson.Desc.K12.Seat
import Johnson.Desc.K12.Seat.Own

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K12.Coin
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker
open Iop Prob _root_.Run
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain
open H2K.Pin (NTuple)
open H2K.Pub (PayPub johOk batV0)
open H2K.First (batOneOk)

/-- The door into the test on G_u. -/
abbrev inGu : _root_.Desc.K14.St → Except String T12 := Seat.enter (·.gU) (·.firstMask)

/-- The door into the test on G_omega. -/
abbrev inGomega : _root_.Desc.K14.St → Except String T12 := Seat.enter (·.gOmega) fun _ => none

/-- **The test on G_u.** -/
theorem k12_game_onGu (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : _root_.Desc.K14.St × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    (pieceOf (C := ckP .two) (F := F) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => ∀ t, inGu a.1 = .ok t → FirstOpens π num no base t)
      (fun a b => ∃ t t', inGu a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      (e, εt) :=
  k12_gameSeat _ inGu Seat.leave F W π num no L mC mS mW rad rd base dB dt ext e
    εt r hA hr hj hb1 hle

/-- **The test on G_omega.** -/
theorem k12_game_onGomega (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : _root_.Desc.K14.St × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    (pieceOf (C := ckP .two) (F := F) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => ∀ t, inGomega a.1 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ∃ t t', inGomega a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      (e, εt) :=
  k12_gameSeatO _ inGomega Seat.leave F W π num no L mC mS mW rad rd base dB dt ext e
    v₀ εt hA hP h1 hlog hle

/-- **The request's own test, first arm.** -/
theorem k12_game_onOwn (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : Third.S₃ × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π num L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e) :
    (pieceOf (C := ckP .two) (F := F) (Seat.onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => ∀ t, Seat.enterOwn a.1 = .ok t → FirstOpens π num no base t)
      (fun a b => ∃ t t', Seat.enterOwn a.1 = .ok t ∧ Seat.leaveOwn a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      (e, εt) :=
  k12_gameSeat _ Seat.enterOwn Seat.leaveOwn F W π num no L mC mS mW rad rd base dB dt ext e
    εt r hA hr hj hb1 hle

/-- **The request's own test, second arm.** -/
theorem k12_game_onOwnO (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : Third.S₃ × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π num L mC mS mW rad base dB dt εt)
    (hP : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e) :
    (pieceOf (C := ckP .two) (F := F) (Seat.onOwn (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => ∀ t, Seat.enterOwn a.1 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ∃ t t', Seat.enterOwn a.1 = .ok t ∧ Seat.leaveOwn a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      (e, εt) :=
  k12_gameSeatO _ Seat.enterOwn Seat.leaveOwn F W π num no L mC mS mW rad rd base dB dt ext e
    v₀ εt hA hP h1 hlog hle

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_game_onGu
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_onGomega
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_onOwn
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_onOwnO
