-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameBook.lean: **THE GAME OF THE PROXIMITY TEST AT THE SHARED CHAIN's TWO SEATS, WITH A PROMISE THAT IS TWO TESTS WITH CODE ON THE CHAIN's OWN RECORD.**
Statements; each proof is one call of GameSeats.lean's law and one of FirstBook.lean's | FirstBookOwn.lean's rule at a seat.

GameSeats.lean has the law at Seat.onGu | Seat.onGomega under FirstOpens | FirstOpensOwn at the record behind the door in. Here that promise is:
  at Seat.onGu      the first fold's mask is noted (d.loc.firstMask.isSome) · the book is in order (BookOrd π.nums.firstTree d.book)
  at Seat.onGomega  BookStep π.nums.firstTree d.book d.roots: the book is in order and the record counts as many roots as the book has trees
at num := numAt t₁ t₂ c and no := fun z => numAt t₁ t₂ c (.own z): the tree at the place z of the chain's book is the chain's z-th over the file.
WHO EARNS THESE: the chain's first record has BookStep; K14's eight blocks keep it; WHERE THE PLAN's MASKS GO AHEAD (P.par.S.masksAhead = true: a premise on the plan there,
held at no real plan here) the second notes the mask, and the third to the eighth leave the note (Johnson/Desc/Sound/BookAtK14.lean); the test on G_u keeps BookStep and the
small record (BookThrough.lean).
ON THE PLAN, BESIDE THE LAW's OWN: ownLabelsB π (true at the two real places by evaluation: FirstBook.lean · FirstBookOwn.lean) · ownMask = false | true · the pins n2, n3 on numAt.
Limits: those of GameSeats.lean, FirstBook.lean, FirstBookOwn.lean. AT THE CHAIN's OWN RECORD St: not yet at a description's piece. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.GameSeats
import Johnson.Desc.K12.Coin.FirstBookOwn

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

/-- The chain's z-th tree, over the file. -/
abbrev noAt (t₁ t₂ c : ℕ) : ℕ → ℕ := fun z => VerifiableInference.Desc.numAt t₁ t₂ c (.own z)

/-- **The test on G_u.** -/
theorem k12_game_onGu_book (F : Frame) (W : Type) (π : P12) (t₁ t₂ c : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : _root_.Desc.K14.St × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e : ℕ)
    (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (hA : AtPlace F π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = false) (hP : ownLabelsB π = true)
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
      VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base) :
    (pieceOf (C := ckP .two) (F := F) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => a.1.loc.firstMask.isSome = true ∧ BookOrd π.nums.firstTree a.1.book)
      (fun a b => ∃ t t', inGu a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π (noAt t₁ t₂ c) rad rd) (t, a.2))
      (e, εt) := by
  intro a ha
  refine seat_of_book (W := W) F π hA.early hA.planOk ho hP t₁ t₂ c base dB dt e εt n2 n3 inGu
    Seat.leave _
    (k12_game_onGu F W π _ (noAt t₁ t₂ c) L mC mS mW rad rd base dB dt (fun _ _ w => w) e εt r hA hr
      hj hb1 hle) a fun t ht => ?_
  cases ht
  exact ha

/-- **The test on G_omega.** -/
theorem k12_game_onGomega_book (F : Frame) (W : Type) (π : P12) (t₁ t₂ c : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (ext : _root_.Desc.K14.St × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dt)) → W → W) (e v₀ : ℕ)
    (εt : Err (uLT (ckP .two) dt))
    (hA : AtPlaceOwn F π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad base dB dt εt)
    (hPay : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hP : ownLabelsB π = true)
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
      VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base) :
    (pieceOf (C := ckP .two) (F := F) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) base
        (dB :: dt) [] ⟨ext, (e, εt)⟩).ior.red.Leads
      (fun a => BookStep π.nums.firstTree a.1.book a.1.roots)
      (fun a b => ∃ t t', inGomega a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
        QN π (NTuple F π (noAt t₁ t₂ c) rad rd) (t, a.2))
      (e, εt) := by
  intro a ha
  refine seat_of_bookOwn (W := W) F π hA.early hA.planOk ho hP t₁ t₂ c base dB dt e εt hA.numOwn n2 n3
    inGomega Seat.leave _
    (k12_game_onGomega F W π _ (noAt t₁ t₂ c) L mC mS mW rad rd base dB dt (fun _ _ w => w) e v₀ εt hA
      hPay h1 hlog hle) a fun t ht => ?_
  cases ht
  exact ⟨rfl, ha⟩

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_game_onGu_book
#print axioms VerifiableInference.Desc.K12.Coin.k12_game_onGomega_book
