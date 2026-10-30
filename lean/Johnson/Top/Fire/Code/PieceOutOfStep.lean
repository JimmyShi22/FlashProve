-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/Fire/Code/PieceOutOfStep.lean: A COROLLARY, IN THE STEP's FORM, OF `Piece.out_iff`
(Johnson/Desc/Sound/RunIsDecide.lean): where the tests that stand before a piece's run pass, its
block's step says yes on the transcript's own rounds and the stage's own opened columns, and no
column is left over, the piece's reduction puts out. General in the piece.
Main name. `piece_out_of_step`: by `Piece.out_iff`, `step_ok_iff` (the same file) and
`roundsFit_length` (Johnson/Desc/K13/Law/Then.lean): three calls. It is a partial converse of
`piece_steps_at` (Reached.lean).
OBJECT: `Piece.ior` · USER: Johnson/Top/Fire/Code/PieceYesBare.lean · LETTERS: all.
Limits. It serves non-emptiness alone: that a law's piece says yes at a statement. That a transcript
with given rounds exists is not said here. Nothing on soundness.

-/
import Johnson.Top.Fire.Code.Reached
import Johnson.Desc.Sound.RunIsDecide
import Johnson.Desc.K13.Law.Then

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LPFD
open OnBytes.Maker OnBytes.Flat KObj
open _root_.Run.PQ (CK)
open VerifiableInference.Desc VerifiableInference.Desc.Sound

variable {S Cl W : Type} {C : CK} {Fr : Frame}

/-- **Where the tests in front pass, the block's step says yes and no column is left over, the
piece's reduction puts out.** -/
theorem piece_out_of_step (p : Piece C Fr S Cl W) (a : S × Fr.E.Str) (τ : Iop.Tr (uLT C p.ds)) (s' : S) (n : ℕ)
    (hT : sTests C p.stage a.2 τ = true)
    (hs : p.b.step Fr.ft a.1 ((sView C p.stage a.2 τ).rounds ++ p.back) (sView C p.stage a.2 τ).opened = .ok (s', n))
    (hn : (sView C p.stage a.2 τ).opened.drop n = []) :
    p.ior.red.out a τ = some (s', p.ior.imp a.2 τ) := by
  obtain ⟨h1, h2, -, h4⟩ := (step_ok_iff Fr.ft p.b a.1 s' _ _ n).1 hs
  have ht : (sView C p.stage a.2 τ).opened.take n = (sView C p.stage a.2 τ).opened :=
    List.take_of_length_le (List.drop_eq_nil_iff.1 hn)
  rw [ht] at h2 h4
  exact (Piece.out_iff p a (s', p.ior.imp a.2 τ) τ).2
    ⟨hT, ⟨VerifiableInference.Desc.K13.Law.roundsFit_length _ _ h1, h1, h2⟩, h4, rfl⟩

end LPFD

#print axioms LPFD.piece_out_of_step
