-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/MakerOut.lean (kind K10): WHERE K10's LAW's OWN PIECE SAYS YES, THE
MAKER's PIECE OVER THE SAME SUB-PROTOCOL SAYS YES, BESIDE ANY PUBLIC PART; AND ITS EXTRACTOR, IF IT
IS A MAP OF THE TWO STATEMENTS, IS THAT MAP THERE. Statements and proofs.

Why. The sentence hQ of `k10_law_withMap` (KindK10Law.lean, beside this file) names the piece's yes
at `pieceOn b ..` (the state alone), and the extractor's value at `(pieceOf (held b) ..).withMap e`
(the state beside a public part z). `Piece.withMap` (Johnson/Desc/Sound/ReExt.lean) is e at a yes OF
THE SECOND PIECE and the identity elsewhere. Whoever pays hQ needs the second yes from the first.
  `maker_out_of_on`: `(pieceOn b base dB dE dR k ext err)`'s out at a, τ is a': THEN `(pieceOf (held
    b) base (dB :: dE :: k x dR) [] x)`'s out at ((z, a.1), a.2), τ is ((z, a'.1), a'.2). By
    `liftOut` (Johnson/Desc/Sound/LiftRule.lean): both pieces hold the sub-protocol under `below`; a
    piece's out reads neither its extractor nor its errors.
  `maker_ext_of_on`: so `((pieceOf (held b) ..).withMap e).ext ((z, a.1), a.2) τ w = e ((z, a.1),
    a.2) ((z, a'.1), a'.2) w`.
Limits. Two small lemmas on the pieces' text. Nothing on the laws. Nothing on soundness.

-/
import Johnson.Desc.First.Close.Law.GoodAtMaker
import Johnson.Desc.Sound.TiedLays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open _root_.Run (ckP)

local notation "S1" => VerifiableInference.Desc.First.S

variable {Pz Cl W : Type} {F : Frame} (b : Block S1 Cl) (base : ℕ) (dB dE dR : RDT) (k : ℕ)
  (x : Rest (ckP .two) F (Pz × S1) W (dB :: dE :: List.replicate k dR))
  (ext : S1 × F.E.Str → Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)) → W → W)
  (err : Iop.Err (uLT (ckP .two) (dB :: dE :: List.replicate k dR)))

/-- **The law's own piece's yes is the maker's piece's yes, beside any public part.** -/
theorem maker_out_of_on (z : Pz) (a a' : S1 × F.E.Str)
    (τ : Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)))
    (h : (pieceOn (W := W) (F := F) b base dB dE dR k ext err).ior.red.out a τ = some a') :
    (pieceOf (held b) base (dB :: dE :: List.replicate k dR) [] x).ior.red.out ((z, a.1), a.2) τ =
      some ((z, a'.1), a'.2) := by
  have e := liftOut (Pz × S1) S1 Cl W (ckP .two) F Prod.snd (fun t s => (t.1, s))
    (pieceOn (W := W) (F := F) b base dB dE dR k ext err) (fun _ _ => rfl) (fun _ _ _ => rfl)
    ((z, a.1), a.2) τ
  have h' : (pieceOn (W := W) (F := F) b base dB dE dR k ext err).ior.red.out
      (atPart Prod.snd (((z, a.1), a.2) : (Pz × S1) × F.E.Str)) τ = some a' := h
  rw [h'] at e
  exact e

/-- **So a map of the two statements, laid in as the maker's piece's extractor, is that map
there.** -/
theorem maker_ext_of_on (e : (Pz × S1) × F.E.Str → (Pz × S1) × F.E.Str → W → W) (z : Pz)
    (a a' : S1 × F.E.Str) (τ : Iop.Tr (uLT (ckP .two) (dB :: dE :: List.replicate k dR)))
    (h : (pieceOn (W := W) (F := F) b base dB dE dR k ext err).ior.red.out a τ = some a') (w : W) :
    ((pieceOf (held b) base (dB :: dE :: List.replicate k dR) [] x).withMap e).ext
      ((z, a.1), a.2) τ w = e ((z, a.1), a.2) ((z, a'.1), a'.2) w :=
  (withMap_ext_eq (pieceOf (held b) base (dB :: dE :: List.replicate k dR) [] x) e
    ((z, a.1), a.2) τ w).trans (by rw [maker_out_of_on b base dB dE dR k x ext err z a a' τ h]; rfl)

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.maker_out_of_on
#print axioms VerifiableInference.Desc.First.Close.maker_ext_of_on
