-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/SendLetters.lean: K01_law, J1: «THE DESCRIPTION's PIECE AT A PLACE OF KIND K1 HAS THE SENDING's PIECE's LETTERS» (HasSendLetters: the premise hQ of the road, at pc := fun c' => sendPiece c' base d₁ d₂ coordinates e), BROUGHT DOWN, WHERE THE ROW OF
PIECES IS THE MAKER's (cutRow, Johnson/Desc/Sound/Tiles.lean), TO THREE SENTENCES ON LETTERS, by the closed form of the maker at an index (Desc.K14.Law.cutRow_at, Johnson/Desc/K14/Law/CutAt.lean). The twin, for a sending, of
K13Letters.lean [not in this library] (HasM3Letters), lemma for lemma.
  hds    the stretch of the written rounds' data at block k is [d₁, d₂]
  herr   the family of rests gives the sending's own errors there: (seedMaps d₁ d₂ c).err (e, ())
  hlen   k is not the row's last number
  HasSendLetters · hasSendLetters_pieceOf · hasSendLetters_of_cut
  HasLettersE · hasLettersE_of_cut      THE LIKE WITH THE ERRORS A LETTER: herr FALLS: the piece's errors are the rest's own (at the maker's restCap: the cap); what is then owed is «the sending's own errors are at most these» (Err.le), spent by
                                        tiedAt_err (Johnson/Desc/Sound/TiedAtErr.lean) over goodIn_err (Johnson/Desc/Sound/GoodInErr.lean)
Nothing on soundness.
-/
import Johnson.Desc.K14.Law.CutAt
import Johnson.Desc.K1.Law.GoodSend3
import Johnson.Desc.First.State

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open _root_.Desc.K14.Law (roundsIn cutRow_at)

variable {Pp Cl W : Type} {Fr : Frame}

/-- The piece has the letters of a sending's piece: whatever block over the chain's state is laid into them. -/
def HasSendLetters (Fr : Frame) (base : ℕ) (d₁ d₂ : RDT) (c e : ℕ)
    (q : Sound.Piece (ckP .two) Fr (Pp × S) Cl W) : Prop :=
  ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Sound.Piece (ckP .two) Fr S Cl W) = sendPiece c' base d₁ d₂ c e

/-- A piece that is made of a sending's stretch, nothing behind it, and a rest with the sending's errors. -/
theorem hasSendLetters_pieceOf (base : ℕ) (d₁ d₂ : RDT) (c e : ℕ) (x : Block (Pp × S) Cl)
    (Rs : Sound.Rest (ckP .two) Fr (Pp × S) W [d₁, d₂])
    (he : Rs.err = (seedMaps d₁ d₂ c).err ((e, ()) : Nat × Unit)) :
    HasSendLetters Fr base d₁ d₂ c e (pieceOf x base [d₁, d₂] [] Rs) := by
  intro c'
  show (⟨c', base, [d₁, d₂], [], fun _ _ w => w, Rs.err⟩ : Sound.Piece (ckP .two) Fr S Cl W) =
    ⟨c', base, [d₁, d₂], [], fun _ _ w => w, (seedMaps d₁ d₂ c).err ((e, ()) : Nat × Unit)⟩
  rw [he]

/-- **At the maker's row.** -/
theorem hasSendLetters_of_cut
    (rest : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) Fr (Pp × S) W ds) (putBack : List Fmt.RoundView)
    (l : List (Block (Pp × S) Cl)) (b : Block (Pp × S) Cl) (all : List RDT) (k : ℕ)
    (x : Block (Pp × S) Cl) (hx : (b :: l)[k]? = some x) (hlen : k < l.length)
    (d₁ d₂ : RDT) (c e : ℕ)
    (hds : (all.drop (roundsIn ((b :: l).take k))).take x.rounds.length = [d₁, d₂])
    (herr : (rest k [d₁, d₂]).err = (seedMaps d₁ d₂ c).err ((e, ()) : Nat × Unit))
    (q : Sound.Piece (ckP .two) Fr (Pp × S) Cl W)
    (hq : ((cutRow rest putBack 0 0 all b l).1 :: (cutRow rest putBack 0 0 all b l).2)[k]? =
      some q) :
    HasSendLetters Fr (nTrees (all.take (roundsIn ((b :: l).take k)))) d₁ d₂ c e q := by
  obtain ⟨q', h0, _, h2, h3, _, h5⟩ := cutRow_at rest putBack l b 0 0 all k x hx hlen
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans h0)
  rw [h5, h2, h3.trans hds, Nat.zero_add, Nat.zero_add]
  exact hasSendLetters_pieceOf _ d₁ d₂ c e x _ herr

/-! ## The like with the errors a letter: the maker's rests give THE CAP, not the kind's own errors -/

/-- The piece has a sending's stretch, nothing behind it, and the errors ε. -/
def HasLettersE (Fr : Frame) (base : ℕ) (d₁ d₂ : RDT) (ε : Err (uLT (ckP .two) [d₁, d₂]))
    (q : Sound.Piece (ckP .two) Fr (Pp × S) Cl W) : Prop :=
  ∀ c' : Block S Cl, (⟨c', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
    Sound.Piece (ckP .two) Fr S Cl W) = ⟨c', base, [d₁, d₂], [], fun _ _ w => w, ε⟩

/-- **At the maker's row: the errors are the rest's own: nothing is asked of them.** -/
theorem hasLettersE_of_cut
    (rest : (i : ℕ) → (ds : List RDT) → Sound.Rest (ckP .two) Fr (Pp × S) W ds) (putBack : List Fmt.RoundView)
    (l : List (Block (Pp × S) Cl)) (b : Block (Pp × S) Cl) (all : List RDT) (k : ℕ)
    (x : Block (Pp × S) Cl) (hx : (b :: l)[k]? = some x) (hlen : k < l.length)
    (d₁ d₂ : RDT)
    (hds : (all.drop (roundsIn ((b :: l).take k))).take x.rounds.length = [d₁, d₂])
    (q : Sound.Piece (ckP .two) Fr (Pp × S) Cl W)
    (hq : ((cutRow rest putBack 0 0 all b l).1 :: (cutRow rest putBack 0 0 all b l).2)[k]? =
      some q) :
    HasLettersE Fr (nTrees (all.take (roundsIn ((b :: l).take k)))) d₁ d₂ (rest k [d₁, d₂]).err q := by
  obtain ⟨q', h0, _, h2, h3, _, h5⟩ := cutRow_at rest putBack l b 0 0 all k x hx hlen
  obtain rfl : q = q' := Option.some.inj (hq.symm.trans h0)
  rw [h5, h2, h3.trans hds, Nat.zero_add, Nat.zero_add]
  exact fun _ => rfl

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hasLettersE_of_cut
#print axioms VerifiableInference.Desc.K1.hasSendLetters_pieceOf
#print axioms VerifiableInference.Desc.K1.hasSendLetters_of_cut
