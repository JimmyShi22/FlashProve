-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05Piece.lean: kind K5 as a piece in the form of the rule of composition
(Johnson/Desc/Sound/ChainRule.lean: Piece: a block with its stretch's data, an extractor and
errors).

Main names:
  `k5Piece`: the kind's block at a stretch's data, with the extractor that hands the witness
    through.
  `token_passes`: for every reading tok of the witness: tok (ext a τ w) = tok w.

Limits. token_passes holds by k5Piece's definition and cannot fail of a piece so made; it is no law
on the
kind. The proved chain's knowledge soundness is stated at an extractor that also hands the witness
through
(Cb/Pv/Att/OwnAt.lean: ownAt_knowAt), but nothing in this file or in what it imports ties the two:
that this piece is good at
this extractor (PieceOfProved, PieceGood) is not shown; the witness types differ. base, ds and err
are
parameters: whoever lays the chain's row gives them.
Source: `PassesTok` is typed here as ExtHeard.lean has it: a copy, not an import.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Sound.ChainRule
import Johnson.Desc.First.Att.K5AttentionKind

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc.Sound (Frame Piece)
open _root_.Run.PQ (CK)
open _root_.Iop (Err)

variable {S Cl W : Type}

/-- **K5 as a piece**: its extractor hands the witness through. -/
def k5Piece (C : CK) (F : Frame) (seat : Seat S) (claims : List (String × (Nat → S → Except String (List Cl × S))))
    (p : Par) (base : ℕ) (ds : List RDT) (err : Err (uLT C ds)) : Piece C F S Cl W :=
  { b := attentionKind seat claims p, base := base, ds := ds, ext := fun _ _ w => w, err := err }

/-- **token_passes.** -/
theorem token_passes {Tok : Type} (tok : W → Tok) (C : CK) (F : Frame) (seat : Seat S)
    (claims : List (String × (Nat → S → Except String (List Cl × S)))) (p : Par) (base : ℕ) (ds : List RDT)
    (err : Err (uLT C ds)) :
    ∀ a τ w, tok ((k5Piece (W := W) C F seat claims p base ds err).ext a τ w) = tok w := fun _ _ _ => rfl

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.token_passes
