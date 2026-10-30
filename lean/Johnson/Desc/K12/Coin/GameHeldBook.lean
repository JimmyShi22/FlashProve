-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Coin/GameHeldBook.lean: **THE GAME OF THE PROXIMITY TEST AT THE PIECE THAT A DESCRIPTION HOLDS AT THE SHARED CHAIN's TWO SEATS, WITH A PROMISE THAT IS TWO TESTS WITH CODE ON THE CHAIN's OWN RECORD.**
Statements; each proof is GameBook.lean's law carried through both wraps by leads_under and leads_lift (Johnson/Desc/Plain/LiftBelow.lean), as GameHeld.lean carries GameSeat.lean's.

At a description the rows of pieces hold the blocks held b: below b (the test "every word is below the prime" in front), lifted to the pair of what was handed to the chain and the chain's own state.
  k12_held_onGu_book      at ANY piece over P₁ × St whose block is held (Seat.onGu (proximityTestKind guardedProximityTestParts π)), with nothing put back, base, data dB :: dt, errors (e, εt): under "the first fold's mask is noted; the book is in
                          order" at the state's second part; and, for certain, the first part rides along unturned.
  k12_held_onGomega_book  the like at Seat.onGomega, under BookStep.
  sharedX_gives_nine | _ten   the one X (sharedX 9 | 10, Johnson/Desc/Sound/SharedX.lean) gives the two promises, where the place's firstTree is K14's.
Limits: those of GameBook.lean. THE PIECE's TYPE OF CLAIMS IS Unit: over the one base a description's pieces hold b.retype at its own type of claims: the rule for that is not shown here. THE CONCLUSION IS
QN π (NTuple …): not the ledger's step. It closes no row. NO SOUNDNESS IS CLAIMED.

-/
import Johnson.Desc.K12.Coin.GameBook
import Johnson.Desc.Plain.LiftBelow
import Johnson.Desc.Sound.PaidAtDesc
import Johnson.Desc.Sound.SharedX

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
open _root_.Desc.K14 (St P14)
open _root_.Desc.K14.Law.Fence (sharedX sharedX_parts bookX_nine bookX_ten)

/-- **The test on G_u, at the piece that a description holds.** -/
theorem k12_held_onGu_book (P₁ : Type) (F : Frame) (W : Type) (π : P12) (t₁ t₂ c : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e : ℕ) (εt : Err (uLT (ckP .two) dt)) (r : Fmt.M1.Stage → ℕ)
    (p : Piece (ckP .two) F (P₁ × St) Unit W)
    (hb : p.b = held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)))
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlace F π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad base dB dt εt)
    (hr : ∀ s, rad s = r s.st) (hj : johOk π r = true) (hb1 : batOneOk π = true)
    (hle : batV0 π r * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = false) (hP : ownLabelsB π = true)
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
      VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base) :
    p.ior.red.Leads
      (fun a => a.1.2.loc.firstMask.isSome = true ∧ BookOrd π.nums.firstTree a.1.2.book)
      (fun a b => (∃ t t', inGu a.1.2 = .ok t ∧ Seat.leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π (noAt t₁ t₂ c) rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds herr
  subst hb h0 hbase hds
  obtain rfl := eq_of_heq herr
  exact leads_lift (S := P₁ × St) Prod.snd (fun t s => (t.1, s))
    (pieceOf (C := ckP .two) (F := F) (W := W) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit)) pbase
      (dB :: dt) [] ⟨fun _ _ w => w, (e, εt)⟩).under
    (fun a => a.1.loc.firstMask.isSome = true ∧ BookOrd π.nums.firstTree a.1.book)
    (fun a b => ∃ t t', inGu a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
      QN π (NTuple F π (noAt t₁ t₂ c) rad rd) (t, a.2))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (leads_under _ rfl _ _
      (k12_game_onGu_book F W π t₁ t₂ c L mC mS mW rad rd pbase dB dt (fun _ _ w => w) e εt r hA hr
        hj hb1 hle ho hP n2 n3))

/-- **The test on G_omega, at the piece that a description holds.** -/
theorem k12_held_onGomega_book (P₁ : Type) (F : Frame) (W : Type) (π : P12) (t₁ t₂ c : ℕ)
    (L mC mS mW : Sg → ℕ → ℕ) (rad : Sg → ℕ) (rd : ℕ → ℕ) (base : ℕ) (dB : RDT) (dt : List RDT)
    (e v₀ : ℕ) (εt : Err (uLT (ckP .two) dt)) (p : Piece (ckP .two) F (P₁ × St) Unit W)
    (hb : p.b = held (P := P₁) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit)))
    (h0 : p.back = []) (hbase : p.base = base) (hds : p.ds = dB :: dt)
    (herr : HEq p.err ((e, εt) : Err (uLT (ckP .two) (dB :: dt))))
    (hA : AtPlaceOwn F π (VerifiableInference.Desc.numAt t₁ t₂ c) L mC mS mW rad base dB dt εt)
    (hPay : PayPub π rad dB.entry.rows v₀) (h1 : Fmt.dsOf dB.entry dB.kind = [.elem, .trits 0])
    (hlog : dB.entry.logN ≤ 64) (hle : v₀ * (bsRound .two dB.entry dB.kind).w ≤ e)
    (ho : π.nums.ownMask = true) (hP : ownLabelsB π = true)
    (n2 : ∀ n, n < π.nums.free → VerifiableInference.Desc.numAt t₁ t₂ c (.own n) < base)
    (n3 : ∀ c' n, (c' + 1, n) ∈ π.before →
      VerifiableInference.Desc.numAt t₁ t₂ c (.taken c' n) < base) :
    p.ior.red.Leads (fun a => BookStep π.nums.firstTree a.1.2.book a.1.2.roots)
      (fun a b => (∃ t t', inGomega a.1.2 = .ok t ∧ Seat.leave a.1.2 t' = .ok b.1.2 ∧
        QN π (NTuple F π (noAt t₁ t₂ c) rad rd) (t, a.2)) ∧ b.1 = (a.1.1, b.1.2))
      p.err := by
  obtain ⟨pb, pbase, pds, pback, pext, perr⟩ := p
  dsimp only at hb h0 hbase hds herr
  subst hb h0 hbase hds
  obtain rfl := eq_of_heq herr
  exact leads_lift (S := P₁ × St) Prod.snd (fun t s => (t.1, s))
    (pieceOf (C := ckP .two) (F := F) (W := W) (Seat.onGomega (proximityTestKind guardedProximityTestParts π : Block T12 Unit))
      pbase (dB :: dt) [] ⟨fun _ _ w => w, (e, εt)⟩).under
    (fun a => BookStep π.nums.firstTree a.1.book a.1.roots)
    (fun a b => ∃ t t', inGomega a.1 = .ok t ∧ Seat.leave a.1 t' = .ok b.1 ∧
      QN π (NTuple F π (noAt t₁ t₂ c) rad rd) (t, a.2))
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    (leads_under _ rfl _ _
      (k12_game_onGomega_book F W π t₁ t₂ c L mC mS mW rad rd pbase dB dt (fun _ _ w => w) e v₀ εt
        hA hPay h1 hlog hle ho hP n2 n3))

/-- What the one X gives the law at Seat.onGu. -/
theorem sharedX_gives_nine (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (π : P12)
    (hft : π.nums.firstTree = P.par.toGPar.firstTree) (d : St)
    (h : sharedX P sentU layU layO 9 d = true) :
    d.loc.firstMask.isSome = true ∧ BookOrd π.nums.firstTree d.book := by
  rw [hft]
  exact bookX_nine _ d ((sharedX_parts P sentU layU layO 9 d).1 h).1

/-- What the one X gives the law at Seat.onGomega. -/
theorem sharedX_gives_ten (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay) (π : P12)
    (hft : π.nums.firstTree = P.par.toGPar.firstTree) (d : St)
    (h : sharedX P sentU layU layO 10 d = true) : BookStep π.nums.firstTree d.book d.roots := by
  rw [hft]
  exact bookX_ten _ d ((sharedX_parts P sentU layU layO 10 d).1 h).1

end VerifiableInference.Desc.K12.Coin

#print axioms VerifiableInference.Desc.K12.Coin.k12_held_onGu_book
#print axioms VerifiableInference.Desc.K12.Coin.k12_held_onGomega_book
#print axioms VerifiableInference.Desc.K12.Coin.sharedX_gives_nine
#print axioms VerifiableInference.Desc.K12.Coin.sharedX_gives_ten
