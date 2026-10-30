-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Link/Law/AtRecPays.lean: SIX OF THE LAW's PREMISES ON ITS THREE PIECES HOLD
OUTRIGHT AT THE PIECES THAT THE CARRIAGE TO A DESCRIPTION USES (`atRec q b₀`, LinkTiedPub.lean: the
piece over the verifier's state that holds the block b₀, with q's own stretch, rounds put back and
errors, and the identity for its extractor). Two theorems; and the batching kind's block tells no
oracle.

What is said.
  `pieces_atRec`: `OwesPieces` at these pieces: that each holds its block is so by the making; the
    first piece's one round and «nothing is put back» are handed through, as facts on the
    description's own piece. `caller_atRec`: `OwesCaller`: the three extractors are the identity by
    the making; the first piece's error is handed through. `batch_tells`: the batching kind's block,
    at whatever gatherer, declares one round with no oracle: flattened: none.

Limits. Three premises stay, on the description's first piece: its round, what is put back, its
error. Nothing on soundness.

-/
import Johnson.Desc.First.Link.Law.LinkTiedPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin
open OnBytes OnBytes.Model OnBytes.Maker OnBytes.Flat KObj
open VerifiableInference.Desc.K9 (Where atS)
open VerifiableInference.Desc.K9L
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open _root_.Run (ckP)
open _root_.Iop (Err)

variable {P W : Type} {F : Frame}

/-- **OwesPieces AT THE CARRIAGE's PIECES.** -/
theorem pieces_atRec (L : Link S Claim) (p : Where) (b₃ : Block S Claim)
    (qb qq qe : Piece (ckP .two) F (P × S) Claim W) (hds : qb.ds = [k9Round p])
    (hbk : qb.back = []) :
    OwesPieces L p b₃ (atRec qb (below L.batchB)) (atRec qq (below L.behindB))
      (atRec qe (below b₃)) :=
  ⟨rfl, rfl, rfl, hds, hbk⟩

/-- **OwesCaller AT THE CARRIAGE's PIECES.** -/
theorem caller_atRec (b₁ b₂ b₃ : Block S Claim) (qb qq qe : Piece (ckP .two) F (P × S) Claim W)
    (hcap : qb.err = Err.cap 128 (uLT (ckP .two) qb.ds)) :
    OwesCaller (atRec qb b₁) (atRec qq b₂) (atRec qe b₃) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, hcap⟩

/-- The batching kind's block tells no oracle. -/
theorem batch_tells {T : Type} (X : K9.Lens T) (p : Where)
    (g : T → Except String (List Claim × T)) : (K9.batch X p g).oracles.flatten = [] := rfl

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.pieces_atRec
#print axioms VerifiableInference.Desc.LinkJoin.caller_atRec
#print axioms VerifiableInference.Desc.LinkJoin.batch_tells
