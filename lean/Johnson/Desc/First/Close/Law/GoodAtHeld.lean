-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GoodAtHeld.lean: FROM K10's LAW AT ITS OWN PIECE (OVER THE FIRST
CHAIN's STATE), WITH ITS OWN EXTRACTOR, TO THE PIECE THAT THE MAKER CUTS AT A DESCRIPTION (OVER THE
PAIR). One statement and its proof. (In the Lean names a "block" is a sub-protocol and a
"description" the IOP as written in Lean.)

Why. K10's law in the form that the rule of composition asks (`Piece.GoodIn`: `k10_goodIn`,
GoodOf.lean, beside this file) stands at `pieceOn b ..` (AtAny.lean): `below b` over the first
chain's state, WITH AN EXTRACTOR THAT IS A LETTER. A description's pieces hold `held b`, over the
pair of what was handed to the chain and the verifier's state. K10's row of the table of joints
LAYS: its extractor lays the closed group's messages into the witness: it is not the identity, and
it may read the pair's first part.
  `goodIn_held_of_on`: EXT z: an extractor for each value z of the pair's first part. `GoodIn` at
    `pieceOn b base dB dE dR k (EXT z) x.err`, at conditions and relations that hang on z, for every
    z; at an accepting transcript the maker's extractor x.ext is EXT at the pair's first part, read
    at the state: THEN the maker's piece `pieceOf (held b) base (dB :: dE :: k times dR) [] x` has
    `GoodIn` at the same, read at z := the pair's first part. By `liftGoodInExt`
    (Johnson/Desc/Sound/LiftOwn.lean: a lift whose extractor reads the rest of the state too) and
    `goodIn_ext` (Johnson/Road/K4/PieceAtCut.lean: `GoodIn` reads the extractor at an accepting
    transcript alone).
Limits. `k10_goodIn` is not called here: its premises stay its own. hx IS THE TRUE DEBT THAT IS
LEFT: that the table's extractor at K10's number is the extractor of K10's law: shown of no
extractor here. Nothing on soundness.


-/
import Johnson.Desc.First.Close.Law.AtAny
import Johnson.Desc.Sound.LiftOwn
import Johnson.Road.K4.PieceAtCut

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open OnBytes.Road.K4 (goodIn_ext)
open _root_.Run (ckP)

/-- **K10's law, with its own extractor, carried to the maker's piece at a description.** -/
theorem goodIn_held_of_on {P₀ Cl W : Type} {F : Frame}
    (b : Block VerifiableInference.Desc.First.S Cl) (base : ℕ) (dB dE dR : RDT) (k : ℕ)
    (x : Rest (ckP .two) F (P₀ × VerifiableInference.Desc.First.S) W
      (dB :: dE :: List.replicate k dR))
    (EXT : P₀ → VerifiableInference.Desc.First.S × F.E.Str →
      Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
    (on on' : P₀ → VerifiableInference.Desc.First.S × F.E.Str → Prop)
    (R R' : P₀ → VerifiableInference.Desc.First.S × F.E.Str → W → Prop)
    (h : ∀ z, (pieceOn b base dB dE dR k (EXT z) x.err :
      Piece (ckP .two) F VerifiableInference.Desc.First.S Cl W).GoodIn (on z) (on' z) (R z) (R' z))
    (hx : ∀ a τ a' w, (pieceOf (held b) base (dB :: dE :: List.replicate k dR) [] x).ior.red.out
      a τ = some a' → x.ext a τ w = EXT a.1.1 (a.1.2, a.2) τ w) :
    (pieceOf (held b) base (dB :: dE :: List.replicate k dR) [] x).GoodIn
      (fun a => on a.1.1 (a.1.2, a.2)) (fun a => on' a.1.1 (a.1.2, a.2))
      (fun a w => R a.1.1 (a.1.2, a.2) w) (fun a w => R' a.1.1 (a.1.2, a.2) w) :=
  goodIn_ext
    ((pieceOn b base dB dE dR k (fun _ _ w => w) x.err :
      Piece (ckP .two) F VerifiableInference.Desc.First.S Cl W).liftAt Prod.snd
        (fun (t : P₀ × VerifiableInference.Desc.First.S) s => (t.1, s)) Prod.fst EXT)
    x.ext (fun a τ a' w ha => hx a τ a' w ha)
    (liftGoodInExt (P₀ × VerifiableInference.Desc.First.S) VerifiableInference.Desc.First.S P₀ Cl W
      (ckP .two) F Prod.snd (fun t s => (t.1, s)) Prod.fst
      (pieceOn b base dB dE dR k (fun _ _ w => w) x.err) EXT on on' R R' (fun _ _ => rfl)
      (fun _ _ _ => rfl) (fun _ _ => rfl) h)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.goodIn_held_of_on
