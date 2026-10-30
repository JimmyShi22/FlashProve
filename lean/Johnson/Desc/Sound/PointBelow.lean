-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/PointBelow.lean: THE TIE AT "LIN point": FROM THE BARE BLOCK, LIFTED, TO THE PIECE THAT A DESCRIPTION's SHARED CHAIN HOLDS: the block WITH THE TEST "every word is below the prime" IN FRONT (below, Johnson/Desc/Sound/ChainRule.lean), lifted. Small lemmas, one
theorem. (A description's piece holds (below b1).lift …, not b1.lift ….) A joint build of files of Johnson/Desc/Sound/ and of Johnson/Desc/K14/, as PointAtK14.lean.

  leadsB_narrow: the plain form for a batch in two parts reads a piece through "it puts out" alone: it passes to a piece whose block narrows.
  belowPiece: the piece that holds (below b).lift Prod.snd … at one written round. leadsB_at_belowPiece: what is had at liftedPiece is had at belowPiece.
  acts_same, on_same, step_same: the table's acting part and promise in front of the block, and the relation owed, read a chain's pieces through their bases and rounds alone: at the two lists they are one. leadsB_at_desc_piece: SO THE DEBT STANDS AT
    belowPiece, IN THE LIST OF PIECES THAT HOLDS belowPiece.
By Block.Narrows, below_narrows, lift_narrows, out_narrow (Johnson/Desc/Sound/MergeNarrow.lean): CALLED.

Limits. That the real description's piece at the shared chain's place 1 IS belowPiece b1 base d ext err (b1 the first of blocks P; the same base, round, extractor, errors) stays owed.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.PointAtK14Fill
import Johnson.Desc.Sound.MergeNarrow

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Run OnBytes.Maker OnBytes.Flat
open _root_.Run.PQ (CK)
open VerifiableInference.Desc (Block Strs lift_narrows)
open VerifiableInference.Desc.Sound (Frame Piece onQ₂ actQ stepPt below below_narrows out_narrow)
open VerifiableInference.Desc.Shared (NumbersS MeaningS PromMeaning)

/-- The plain form for a batch in two parts passes to a piece whose block narrows. -/
theorem leadsB_narrow {S Cl W κ : Type} {C : CK} {F : Frame} (p : Piece C F S Cl W) (B' : Block S Cl)
    (h : B'.Narrows p.b) (key : S × F.E.Str → κ) (on : S × F.E.Str → Prop)
    (Q : S × F.E.Str → S × F.E.Str → Prop) (εK εO : Err (uLT C p.ds))
    (g : p.ior.red.LeadsB key on Q εK εO) :
    ({ p with b := B' } : Piece C F S Cl W).ior.red.LeadsB key on Q εK εO := by
  obtain ⟨lK, lO, h1, h2, h3⟩ := g
  exact ⟨lK, lO, h1, h2, fun a τ b ha hk ho hb => h3 a τ b ha hk ho (out_narrow p B' h a b τ hb)⟩

variable {W P₁ : Type} {F : Frame}

/-- The piece that a description's shared chain holds: the block with the test below the prime in front, lifted. -/
def belowPiece (b : Block St Unit) (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W)
    (err : Err (uLT (ckP .two) [d])) : Piece (ckP .two) F (P₁ × St) Unit W :=
  ⟨(below b).lift Prod.snd fun t s => (t.1, s), base, [d], [], ext, err⟩

/-- **What is had at the bare block, lifted, is had at the description's piece.** -/
theorem leadsB_at_belowPiece {κ : Type} (b : Block St Unit) (base : Nat) (d : RDT)
    (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) (err : Err (uLT (ckP .two) [d]))
    (key : (P₁ × St) × F.E.Str → κ) (on : (P₁ × St) × F.E.Str → Prop)
    (Q : (P₁ × St) × F.E.Str → (P₁ × St) × F.E.Str → Prop) (εK εO : Err (uLT (ckP .two) [d]))
    (g : (liftedPiece (W := W) (F := F) (P₁ := P₁) b base d ext err).ior.red.LeadsB key on Q εK εO) :
    (belowPiece (W := W) (F := F) (P₁ := P₁) b base d ext err).ior.red.LeadsB key on Q εK εO :=
  leadsB_narrow (liftedPiece b base d ext err) _ (lift_narrows _ _ (below_narrows b)) key on Q εK εO g

section
variable (b : Block St Unit) (base : Nat) (d : RDT)
  (ext : (P₁ × St) × F.E.Str → Tr (uLT (ckP .two) [d]) → W → W) (err : Err (uLT (ckP .two) [d]))
  (N : NumbersS) (Mg : MeaningS St P₁ W) (Pm : PromMeaning St) (Oc : P₁ → Strs → Prop) (split : Bool)
  (f : Piece (ckP .two) F (P₁ × St) Unit W) (r : List (Piece (ckP .two) F (P₁ × St) Unit W))

/-- The acting parts in front of the block, at the two lists of pieces, are one. -/
theorem acts_same :
    actQ N f (belowPiece b base d ext err :: r) 1 = actQ N f (liftedPiece b base d ext err :: r) 1 := rfl

/-- So are the promises in front of it. -/
theorem on_same :
    onQ₂ N Pm Oc split f (belowPiece b base d ext err :: r) 1 =
      onQ₂ N Pm Oc split f (liftedPiece b base d ext err :: r) 1 := rfl

/-- So is the relation that is owed. -/
theorem step_same (E : (P₁ × St) × F.E.Str → W → W) :
    stepPt N Mg Pm Oc split f (belowPiece b base d ext err :: r) E =
      stepPt N Mg Pm Oc split f (liftedPiece b base d ext err :: r) E := by
  cases r <;> rfl

/-- **The debt at the description's piece, in the description's own list of pieces, from the debt at the bare block, lifted.** -/
theorem leadsB_at_desc_piece (E : (P₁ × St) × F.E.Str → W → W) (εK εO : Err (uLT (ckP .two) [d]))
    (g : (liftedPiece (W := W) (F := F) (P₁ := P₁) b base d ext err).ior.red.LeadsB
      (actQ N f (liftedPiece b base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (liftedPiece b base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (liftedPiece b base d ext err :: r) E) εK εO) :
    (belowPiece (W := W) (F := F) (P₁ := P₁) b base d ext err).ior.red.LeadsB
      (actQ N f (belowPiece b base d ext err :: r) 1).2
      (onQ₂ N Pm Oc split f (belowPiece b base d ext err :: r) 1)
      (stepPt N Mg Pm Oc split f (belowPiece b base d ext err :: r) E) εK εO := by
  rw [step_same]
  exact leadsB_at_belowPiece b base d ext err _ _ _ εK εO g

end

end Desc.K14.Law

#print axioms Desc.K14.Law.leadsB_narrow
#print axioms Desc.K14.Law.leadsB_at_belowPiece
#print axioms Desc.K14.Law.acts_same
#print axioms Desc.K14.Law.on_same
#print axioms Desc.K14.Law.step_same
#print axioms Desc.K14.Law.leadsB_at_desc_piece
