-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyIdPiece.lean: one small tool for the key file's rows: a piece with the identity
for its extractor, at another type of
witnesses. A law in the plain form (Leads, Keeps) reads of a piece its reduction and its errors, not
its extractor; a kind's law in the
form of the rule of composition (Piece.GoodIn) names the extractor and the witnesses' type. idPiece
W' pc has pc's block, base, stretch,
"laid behind" and errors, so its reduction is pc's by rfl.

-/
import Johnson.Desc.Sound.ChainRule

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open VerifiableInference.Desc.Sound
open _root_.Run.PQ (CK)

/-- A piece with the identity for its extractor, at another type of witnesses: the same reduction.
-/
abbrev idPiece {C : CK} {Fr : Frame} {S Cl W : Type} (W' : Type) (pc : Piece C Fr S Cl W) : Piece C
    Fr S Cl W' :=
  ⟨pc.b, pc.base, pc.ds, pc.back, fun _ _ w => w, pc.err⟩

theorem idPiece_ior {C : CK} {Fr : Frame} {S Cl W : Type} (W' : Type) (pc : Piece C Fr S Cl W) :
    (idPiece W' pc).ior = pc.ior := rfl

end Johnson.RunOne.KeyRows23
