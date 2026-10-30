-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/GoodAtMaker.lean: K10's LAW AT THE MAKER's PIECE, WITH THE MAKER's OWN
EXTRACTOR: NO PREMISE ON THE EXTRACTOR IS LEFT. One statement and its proof. (In the Lean names a
"block" is a sub-protocol.)

Why. `goodIn_held_of_on` (GoodAtHeld.lean, beside this file) carries `GoodIn` from `pieceOn b ..
(EXT z) ..` to the maker's piece `pieceOf (held b) .. x`, if at an accepting transcript x.ext is
EXT. K10's law in the form `GoodIn` (`k10_goodIn`, GoodOf.lean) has NO EXTRACTOR OF ITS OWN: its
extractor is a letter: the law's end speaks of the decoded messages, not of a witness, and what it
asks of the extractor stands in one premise (its hQ: a witness behind, carried through the
extractor, is a witness in front). So EXT can be chosen: the maker's own.
  `goodIn_at_maker`: `GoodIn` at `pieceOn b base dB dE dR k (fun a τ w => x.ext ((z, a.1), a.2) τ w)
    x.err` for every z: THEN at `pieceOf (held b) base (dB :: dE :: k times dR) [] x`, read at the
    pair: the premise on the extractor holds by rfl.
Limits. The whole weight now lies where it belongs: in `k10_goodIn`'s hQ AT THAT EXTRACTOR: that
what the table's extractor lays into the witness at K10's number are the messages of which the law's
end speaks. Shown of no extractor here. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.GoodAtHeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run (ckP)

/-- **K10's law at the maker's piece, with the maker's own extractor.** -/
theorem goodIn_at_maker {P₀ Cl W : Type} {F : Frame}
    (b : Block VerifiableInference.Desc.First.S Cl) (base : ℕ) (dB dE dR : RDT) (k : ℕ)
    (x : Rest (ckP .two) F (P₀ × VerifiableInference.Desc.First.S) W
      (dB :: dE :: List.replicate k dR))
    (on on' : P₀ → VerifiableInference.Desc.First.S × F.E.Str → Prop)
    (R R' : P₀ → VerifiableInference.Desc.First.S × F.E.Str → W → Prop)
    (h : ∀ z, (pieceOn b base dB dE dR k (fun a τ w => x.ext ((z, a.1), a.2) τ w) x.err :
      Piece (ckP .two) F VerifiableInference.Desc.First.S Cl W).GoodIn (on z) (on' z) (R z)
        (R' z)) :
    (pieceOf (held b) base (dB :: dE :: List.replicate k dR) [] x).GoodIn
      (fun a => on a.1.1 (a.1.2, a.2)) (fun a => on' a.1.1 (a.1.2, a.2))
      (fun a w => R a.1.1 (a.1.2, a.2) w) (fun a w => R' a.1.1 (a.1.2, a.2) w) :=
  goodIn_held_of_on b base dB dE dR k x (fun z a τ w => x.ext ((z, a.1), a.2) τ w) on on' R R' h
    fun _ _ _ _ _ => rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.goodIn_at_maker
