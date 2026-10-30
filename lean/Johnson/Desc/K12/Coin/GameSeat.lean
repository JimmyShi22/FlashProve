-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameSeat.lean: **THE GAME OF THE PROXIMITY TEST AT EVERY SEAT**: at the block
set inside any chain's state by a door in and a door out (`Block.inside`). Statements and proofs,
over the block's parts with guard (c).

A description seats the proximity test's block on its chains' states by `Block.inside`:
`atFinish` (the first chain's finish), `Seat.onGu` and `Seat.onGomega` (the shared chain's two),
`Seat.onOwn` (the third chain's, with its own mask), and the link's. So one statement with letters
for the two doors serves them all.

  `K12GameSeat`, `k12_gameSeat`: the first arm: at the piece as the tiling makes it (`pieceOf`) of
    the seated block, any extractor, errors (e, εt): at every statement whose state the door in
    takes to a record with `FirstOpens`, the prover has lost towards: a yes came through both doors,
    and at the record behind the door in there is one tuple for all rows (`QN` at `NTuple`).
  `K12GameSeatO`, `k12_gameSeatO`: the second arm.
By `leads_seated` (Inside.lean) and GameZ.lean.
Limits: those of GameZ.lean. NO SOUNDNESS IS CLAIMED. Where the door in refuses, the piece refuses
and the law is idle. That a description's seat at a place is this term at these letters is shown
here of no seat: it is by definition for the four named above.

-/
import Johnson.Desc.K12.Coin.GameZ

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

/-- **THE GAME AT A SEAT, FIRST ARM.** -/
def K12GameSeat : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ),
    AtPlace F π num L mC mS mW rad base dB dt εt →
    (∀ s, rad s = r s.st) → johOk π r = true → batOneOk π = true →
    batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpens π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      (e, εt)

theorem k12_gameSeat : K12GameSeat := by
  intro S enter leave F W π num no L mC mS mW rad rd base dB dt ext e εt r hA hr hj hb1 hle a ha
  exact leads_seated (pieceT F W π base dB dt e εt) enter leave
    (fun x => FirstOpens π num no base x.1) (fun x _ => QN π (NTuple F π no rad rd) x)
    (k12_gameZ F W π num no L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r hA hr hj hb1
      hle) a ha

/-- **THE SECOND ARM.** -/
def K12GameSeatO : Prop :=
  ∀ (S : Type) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (F : Frame) (W : Type) (π : P12) (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : S × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt)),
    AtPlaceOwn F π num L mC mS mW rad base dB dt εt →
    PayPub π rad dB.entry.rows v₀ → Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0] →
    dB.entry.logN ≤ 64 → v₀ * (bsRound .two dB.entry dB.kind).w ≤ e →
    (pieceOf (C := ckP .two) (F := F) ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside enter leave) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => ∀ t, enter a.1 = .ok t → FirstOpensOwn π num no base t)
      (fun a b => ∃ t t', enter a.1 = .ok t ∧ leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π no rad rd) (t, a.2))
      (e, εt)

theorem k12_gameSeatO : K12GameSeatO := by
  intro S enter leave F W π num no L mC mS mW rad rd base dB dt ext e v₀ εt hA hP h1 hlog hle a
    ha
  exact leads_seated (pieceT F W π base dB dt e εt) enter leave
    (fun x => FirstOpensOwn π num no base x.1) (fun x _ => QN π (NTuple F π no rad rd) x)
    (k12_gameZO F W π num no L mC mS mW rad rd base dB dt (fun _ _ w => w) e v₀ εt hA hP h1 hlog
      hle) a ha

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_gameSeat
#print axioms VerifiableInference.Desc.K12.Coin.k12_gameSeatO
