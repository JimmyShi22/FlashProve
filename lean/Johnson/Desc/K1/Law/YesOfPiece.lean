-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K1/Law/YesOfPiece.lean: the piece's accept is an accept of the place's bare sub-protocol, in the top's own form YesOf (after yes_of_piece, Johnson/Desc/K1/Law/HpubOf.lean).
Nothing on soundness.
-/
import Johnson.Desc.K1.Law.HpubOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open Iop Run OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)

theorem yesOf_of_piece {Pp W : Type} {F : Frame} (B : Block S Unit) (c : Block S Cl)
    (hu : c.UnderR (B.retype : Block S Cl)) (base : ℕ) (d₁ d₂ : RDT) (cc e : ℕ) (z : Pp)
    (a : S × F.E.Str) (τ : Tr (uLT (ckP .two) [d₁, d₂])) (x : S × F.E.Str)
    (hx : (sendPiece (W := W) (F := F) c base d₁ d₂ cc e).ior.red.out a τ = some x) :
    YesOf B (z, a.1) (z, x.1) := by
  obtain ⟨rs, cols, n, hst⟩ := K13.Law.piece_step _ hx
  obtain ⟨hfit, gs, hd⟩ := step_ok F.ft c _ _ rs cols n hst
  rw [hu.1] at hfit
  exact ⟨rfl, rs, gs, hfit, hu.2 _ _ _ _ hd⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.yesOf_of_piece
