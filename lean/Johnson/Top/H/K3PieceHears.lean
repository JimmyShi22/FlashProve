-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3PieceHears.lean: the kind "lookup" (K3) as a piece of a chain: from the piece's
yes to what the lookup heard. A piece (Johnson/Desc/Sound/ChainRule.lean) is a block with its
stretch of rounds, read as an interactive oracle reduction. Here the piece holds `below (K3.block
…)`: the kind's own block behind the test that every word is below the prime. Theorems with their
proofs.

Main names:

  `piece_hears_below`: general in the block: at a piece that holds `below b` and puts no round
    behind its own, the yes gives the test of work, the oracles behind, `okRoundsE` of the rounds
    that decide is shown, and b's own decide's yes.
  `k3_piece_yes`: where the piece says yes at a transcript τ, `K3.block`'s own decide says yes at
    the rounds shown without the sealed digest, at the columns that the fold hands it, and gives
    the record behind; these rounds pass `okRoundsE`; the oracles behind are the stored table as
    it was and what the stage leaves.
  `k3_piece_hears`: with the law `K3DecideHears` (Johnson/Top/H/K3DecideHearsAt.lean): the record
    behind holds what was heard; the rounds SHOWN have the sizes of the shape's plan of rounds;
    and, where the ledger in front has its sizes, what was heard meets the library's record of end
    values at the rounds SHOWN, read: the digest's striking is gone from the statement.
  `k3_piece_hears_lift`: the same at a piece that holds `(below (K3.block …)).lift get set`: the
    kind's block at a part of a wider record.
  `k3DecideHears_below`: the law's conclusion at ALL rounds, with no premise on the words, from the
    yes of `(below (K3.block …)).decide`.
  `k3_piece_hears_calls`, `k3_piece_hears_digits`: `k3_piece_hears` at the seat of the lookup on a
    link's calls and at that on the smallness test's digits, with no premise on the seat.

Limits. One way alone: nothing is said where the piece refuses. The piece must hold `below
(K3.block …)`: at a piece that holds `K3.block …` itself the fold asks no test on the words, and
`okRoundsE` does not follow. The rounds shown are the transcript's rounds as a view has them, then
the piece's `back`. On the oracles behind see Johnson/Desc/Sound/PieceYes.lean (`left_below`,
`left_all`). These are ties: they have no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.PieceYes
import Johnson.Top.H.K3DecideHearsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open TwV OnBytes OnBytes.Model OnBytes.Model.Forest OnBytes.PscRun OnBytes.PscTie _root_.Fo
open Cb Cb.Fo
open OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (noDigest)
open VerifiableInference.Desc.Sound (Frame Piece below groupsAt)

variable {S Cl W : Type} {C : CK} {Fr : Frame}

/-- **From a piece's yes to its block's yes, in the form in which a chain's closing file asks it**:
general in the block b; the piece holds `below b` and puts no round behind its own. The test of work
has passed; the oracles behind are the stored table as it was and what the stage leaves; the rounds
that decide is shown pass `okRoundsE`; b's own decide says yes at them and gives the record
behind. -/
theorem piece_hears_below (p : Piece C Fr S Cl W) (b : Desc.Block S Cl) (hb : p.b = below b)
    (hback : p.back = []) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (a' : S × Fr.E.Str)
    (h : p.ior.red.out a τ = some a') :
    passT C p.ds (rhoT C p.ds τ) = true ∧ a'.2 = (a.2.1, sLeft C p.stage a.2 τ) ∧
      okRoundsE ((rvT C p.ds τ).map noDigest) = true ∧
      ∃ cols, b.decide a.1 ((rvT C p.ds τ).map noDigest) cols = .ok a'.1 :=
  Desc.Sound.piece_below_plain p b hb hback a a' τ h

/-- **Where the piece says yes, the kind's own decide says yes**, at rounds whose words are below
the prime. -/
theorem k3_piece_yes (p : Piece C Fr S Cl W) (seat : Desc.K3.Seat S Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl))
    (hb : p.b = below (Desc.K3.block seat piece laid before pp guests))
    (a a' : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some a') :
    (Desc.K3.block seat piece laid before pp guests).decide a.1 ((p.shownR τ).map noDigest)
        (groupsAt Fr.ft (Desc.K3.block seat piece laid before pp guests) (p.shownR τ)
          (sView C p.stage a.2 τ).opened) = .ok a'.1 ∧
      okRoundsE ((p.shownR τ).map noDigest) = true ∧
      a'.2 = (a.2.1, sLeft C p.stage a.2 τ) := by
  obtain ⟨_, _, f3, f5⟩ := Desc.Sound.piece_below_yes p _ hb a a' τ h
  exact ⟨f3, Desc.Sound.piece_below_words p _ hb a a' τ h, f5⟩

/-- **Where the piece says yes, what was heard meets the record of end values at the rounds
shown.** -/
theorem k3_piece_hears (p : Piece C Fr S Cl W) (seat : Desc.K3.Seat S Cl) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest S Cl))
    (hb : p.b = below (Desc.K3.block seat piece laid before pp guests))
    (hfork : SeatKeeps seat) (hheard : Desc.K3.SeatReads seat)
    (a a' : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some a')
    (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) :
    ∃ F F' g, seat.fork a.1 = some F ∧ seat.fork a'.1 = some F' ∧ seat.heard a'.1 = some g ∧
      (p.shownR τ).map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      (Sized F →
        ShapeOf pp.calls pp.pub pp.lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next ((p.shownR τ).map (rdRV ρ)))) := by
  obtain ⟨f3, f4, _⟩ := k3_piece_yes p seat piece laid before pp guests hb a a' τ h
  have L := k3DecideHears seat piece laid before pp guests hfork hheard
  unfold K3DecideHears at L
  obtain ⟨F, F', g, e1, e2, e3, e4, e5⟩ := L K ρ lm a.1 a'.1 _ _ f4 f3
  rw [List.map_map] at e4
  refine ⟨F, F', g, e1, e2, e3, e4, fun hS => ?_⟩
  obtain ⟨s1, s2, s3⟩ := e5 hS
  rw [List.map_map] at s3
  exact ⟨s1, s2, s3⟩

/-- **The same at a piece whose block is lifted to a wider record** (`Block.lift`): the piece holds
`(below (K3.block …)).lift get set`. The kind's record in front is `get a.1`; the record behind is
`set a.1 s'`. -/
theorem k3_piece_hears_lift {T : Type} (p : Piece C Fr T Cl W) (get : T → S) (set : T → S → T)
    (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat) (before : List (ℕ × ℕ))
    (pp : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hb : p.b = (below (Desc.K3.block seat piece laid before pp guests)).lift get set)
    (hfork : SeatKeeps seat) (hheard : Desc.K3.SeatReads seat)
    (a a' : T × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (h : p.ior.red.out a τ = some a')
    (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) :
    ∃ s' F F' g, a'.1 = set a.1 s' ∧ seat.fork (get a.1) = some F ∧ seat.fork s' = some F' ∧
      seat.heard s' = some g ∧
      (p.shownR τ).map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      (Sized F →
        ShapeOf pp.calls pp.pub pp.lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next ((p.shownR τ).map (rdRV ρ)))) := by
  obtain ⟨s', d, e, _, w, _⟩ := Desc.Sound.piece_lift_yes p get set _ hb a a' τ h
  have hok : okRoundsE ((p.shownR τ).map noDigest) = true := Desc.Sound.okWords_of_view _ w
  have L := k3DecideHears seat piece laid before pp guests hfork hheard
  unfold K3DecideHears at L
  obtain ⟨F, F', g, e1, e2, e3, e4, e5⟩ := L K ρ lm (get a.1) s' _ _ hok d
  rw [List.map_map] at e4
  refine ⟨s', F, F', g, e, e1, e2, e3, e4, fun hS => ?_⟩
  obtain ⟨s1, s2, s3⟩ := e5 hS
  rw [List.map_map] at s3
  exact ⟨s1, s2, s3⟩

/-- **The law on decide's yes without the premise on the words**, of the block behind the words'
test: `K3DecideHears`'s conclusion, at ALL rounds rs, from the yes of
`(below (K3.block …)).decide`: that block tests the words itself. -/
theorem k3DecideHears_below (seat : Desc.K3.Seat S Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P) (guests : List (Desc.First.Look.Guest S Cl))
    (hfork : SeatKeeps seat) (hheard : Desc.K3.SeatReads seat)
    (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) (s s' : S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (h : (below (Desc.K3.block seat piece laid before pp guests)).decide s rs cols = .ok s') :
    ∃ F F' g, seat.fork s = some F ∧ seat.fork s' = some F' ∧ seat.heard s' = some g ∧
      rs.map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      (Sized F →
        ShapeOf pp.calls pp.pub pp.lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next (rs.map (rdRV ρ)))) := by
  obtain ⟨g1, g2⟩ := Desc.Sound.below_yes _ s s' rs cols h
  have hok : okRoundsE rs = true := Desc.Sound.okWords_of_view _ g1
  have L := k3DecideHears seat piece laid before pp guests hfork hheard
  unfold K3DecideHears at L
  exact L K ρ lm s s' rs cols hok g2

/-- The same at the seat of the lookup on a link's calls. -/
theorem k3_piece_hears_calls (claim : Aff → Cl) (p : Piece C Fr Desc.First.S Cl W) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before pp guests))
    (a a' : Desc.First.S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some a')
    (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) :
    ∃ F F' g, (Desc.K3.seatCalls claim).fork a.1 = some F ∧
      (Desc.K3.seatCalls claim).fork a'.1 = some F' ∧
      (Desc.K3.seatCalls claim).heard a'.1 = some g ∧
      (p.shownR τ).map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      (Sized F →
        ShapeOf pp.calls pp.pub pp.lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next ((p.shownR τ).map (rdRV ρ)))) :=
  k3_piece_hears p _ piece laid before pp guests hb (seatCalls_keeps claim)
    (Desc.K3.seatCalls_reads claim) a a' τ h K ρ lm

/-- The same at the seat of the lookup on the smallness test's digits. -/
theorem k3_piece_hears_digits (claim : Aff → Cl) (p : Piece C Fr Desc.First.S Cl W) (piece : ℕ)
    (laid : Array Nat) (before : List (ℕ × ℕ)) (pp : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (hb : p.b = below (Desc.K3.block (Desc.K3.seatDigits claim) piece laid before pp guests))
    (a a' : Desc.First.S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds))
    (h : p.ior.red.out a τ = some a')
    (K : Type) [CommRing K] (ρ : OnBytes.Model.Reading K) (lm : ℕ) :
    ∃ F F' g, (Desc.K3.seatDigits claim).fork a.1 = some F ∧
      (Desc.K3.seatDigits claim).fork a'.1 = some F' ∧
      (Desc.K3.seatDigits claim).heard a'.1 = some g ∧
      (p.shownR τ).map (fun r => ((sentOf r).length, (drawnOf r).length)) = planF g.shape ∧
      (Sized F →
        ShapeOf pp.calls pp.pub pp.lid g.shape ∧ PadLeft g.shape F F' g ∧
          HeardIs ρ g F' (endsOf g.shape lm F.next ((p.shownR τ).map (rdRV ρ)))) :=
  k3_piece_hears p _ piece laid before pp guests hb (seatDigits_keeps claim)
    (Desc.K3.seatDigits_reads claim) a a' τ h K ρ lm

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.piece_hears_below
#print axioms VerifiableInference.OnPublicFiles.k3_piece_yes
#print axioms VerifiableInference.OnPublicFiles.k3_piece_hears
#print axioms VerifiableInference.OnPublicFiles.k3_piece_hears_lift
#print axioms VerifiableInference.OnPublicFiles.k3DecideHears_below
#print axioms VerifiableInference.OnPublicFiles.k3_piece_hears_calls
#print axioms VerifiableInference.OnPublicFiles.k3_piece_hears_digits
