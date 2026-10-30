-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/FenceK14AtDesc.lean: THE FENCE AT K14's TWO SENDINGS (Johnson/Desc/Sound/FenceK14Sends.lean), AT A PIECE OF THE FORM THAT A FILE's
DESCRIPTION HOLDS. Three theorems. (R) is asked under the fence in front, at a yes of the piece (FenceK14Sends.lean).


WHY. FenceK14Sends.lean speaks of a piece at the chain's own record St that holds the kind's block itself. The pieces of a
description are of another type and hold another block (`OfDesc`, Johnson/Desc/Sound/DescThree.lean): the record is the pair (what
was handed to the chain, the chain's own record), and the block is `(below b).lift Prod.snd fun t s => (t.1, s)`: b with the
test "every word is below the prime" in front, lifted. (The like at "LIN point" is cured
by belowPiece; here the same step for the book-keeping.)
  `decide_below_lift`: a yes of that block from t to t' IS a yes of b from t.2 to t'.2, on the same rounds and columns; and what
    was handed stays.
  `bookKept_at_send_desc`: BookKept (bookedOf lo low (·.2.st) (·.2.book) (·.2.roots)) rec q, for a piece q at the pair that holds
    (below b).lift …, b the second or the fifth of `blocks P`: under the same two premises (T), (R), said at q.
  `seatedNew_at_send_desc`: THE RIDER there: no premise but the fence.
By `piece_yes` (Johnson/Desc/K14/Law/Bridge.lean; general in the record), FenceSend.lean's two rules (general in the record), sends_received.

Every "there is", walked: as in FenceK14Sends.lean.
Limits. Book-keeping. THAT A REAL DESCRIPTION's PIECES AT THE SHARED CHAIN's PLACES 2 AND 5 HOLD THESE BLOCKS is OfDesc with "the shared chain's flat
list is the front block and then blocks P's eight …": not here. It closes no row. Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.FenceK14Sends
import Johnson.Desc.Sound.ExtHeardProofs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open VerifiableInference.Desc (Block mapOk viewWordsBelowPrime)
open VerifiableInference.Desc.Sound (Frame Piece below Received BookKept FenceAt SeatedAt bookedOf
  bookKept_of_recv seatedNew_of_recv)
open _root_.Run.PQ (CK)

/-- **A yes of the block with the test in front, lifted, is a yes of the block; what was handed stays.** -/
theorem decide_below_lift {S P₁ Cl : Type} (b : Block S Cl) (t t' : P₁ × S) (rs : List Fmt.RoundView)
    (gs : List (List (Nat × List UInt64)))
    (h : ((below b).lift Prod.snd fun (t : P₁ × S) s => (t.1, s)).decide t rs gs = .ok t') :
    b.decide t.2 rs gs = .ok t'.2 ∧ t'.1 = t.1 := by
  obtain ⟨s, hs, e⟩ := mapOk (x := (below b).decide t.2 rs gs) h
  have H' : (if viewWordsBelowPrime ⟨rs, (gs.flatMap id).map fun c => (0, c.1, c.2)⟩ then b.decide t.2 rs gs
      else .error "a word is not below the prime") = .ok s := hs
  subst e
  split at H'
  · exact ⟨H', rfl⟩
  · exact nomatch H'

variable {W ρ P₁ : Type} {F : Frame} {C : CK}

/-- **BookKept at K14's two sendings, at a piece of the description's form.** -/
theorem bookKept_at_send_desc (lo : ℕ) (low : Tree → Option ℕ) (rec : P₁ × St → ℕ → ρ) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b = b2 ∨ b = b5) (q : Piece C F (P₁ × St) Unit W)
    (hq : q.b = (below b).lift Prod.snd fun (t : P₁ × St) s => (t.1, s))
    (hT : ∀ d d' ft sent lay, Received ft sent lay d.st d.book d.roots d'.st d'.book d'.roots →
      (∃ rs gs, b.decide d rs gs = .ok d') → lay.shapes.size = q.trees)
    (hR : ∀ a τ c,
      FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
        (fun t => t.2.roots)) q.base a →
      q.ior.red.out a τ = some c → ∀ o, o < a.1.2.st.oracles.size → rec c.1 o = rec a.1 o) :
    BookKept (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book) (fun t => t.2.roots))
      rec q :=
  bookKept_of_recv lo low _ _ _ rec q
    (fun a τ c hc => by
      obtain ⟨_, gs, hd⟩ := piece_yes q a τ c hc
      exact ⟨_, gs, hd⟩)
    (fun t rs gs t' h => by
      rw [hq] at h
      obtain ⟨hd, _⟩ := decide_below_lift b t t' rs gs h
      obtain ⟨ft, sent, lay, hRc⟩ := sends_received P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb _ rs gs _ hd
      exact ⟨ft, sent, lay, hRc, hT _ _ ft sent lay hRc ⟨rs, gs, hd⟩⟩)
    hR

/-- **THE RIDER at K14's two sendings, at a piece of the description's form.** -/
theorem seatedNew_at_send_desc (lo : ℕ) (low : Tree → Option ℕ) (P : P14)
    (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hbl : blocks P = some [b1, b2, b3, b4, b5, b6, b7, b8]) (b : Block St Unit)
    (hb : b = b2 ∨ b = b5) (q : Piece C F (P₁ × St) Unit W)
    (hq : q.b = (below b).lift Prod.snd fun (t : P₁ × St) s => (t.1, s)) :
    ∀ a τ c,
      FenceAt (bookedOf lo low (fun t : P₁ × St => t.2.st) (fun t => t.2.book)
        (fun t => t.2.roots)) q.base a →
      q.ior.red.out a τ = some c →
      ∃ ft sent lay,
        Received ft sent lay a.1.2.st a.1.2.book a.1.2.roots c.1.2.st c.1.2.book c.1.2.roots ∧
        ∀ i, i < sent.size → SeatedAt lo low c.1.2.book (a.1.2.st.oracles.size + i)
          (q.base + lay.tree.getD i 0) (lay.part.getD i 0) :=
  seatedNew_of_recv lo low _ _ _ q
    (fun a τ c hc => by
      obtain ⟨_, gs, hd⟩ := piece_yes q a τ c hc
      exact ⟨_, gs, hd⟩)
    (fun t rs gs t' h => by
      rw [hq] at h
      obtain ⟨hd, _⟩ := decide_below_lift b t t' rs gs h
      exact sends_received P b1 b2 b3 b4 b5 b6 b7 b8 hbl b hb _ rs gs _ hd)

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.decide_below_lift
#print axioms Desc.K14.Law.Fence.bookKept_at_send_desc
#print axioms Desc.K14.Law.Fence.seatedNew_at_send_desc
