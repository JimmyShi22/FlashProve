-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/LedgerAt.lean: the named hypothesis "HoleAt.sound a" of Johnson/Top/OnFilesAt.lean,
paid
for every description whose indices are read as matrices of the committed matrix's shape and whose
relaxed relation gives the claim RelL of Johnson/Flat/LedgerClaim.lean.

One structure and one theorem.
  ReadsCells a s rows cols: a map from a's indices to matrices, a map from a's instances to the
    model's requests, and three laws: what a's builder builds is what requestOfTokens builds; a's
    model is nextTok s at the index's matrix; a's relaxed relation gives RelL s.
  HoleAt.sound_of_cells: at a lawful table of scales, and a shape within the reference's.
Beside Johnson/Top/SoundAt.lean: there an index of the description is mapped to a well-formed table
by a total map, and the model's law is asked at every index. Here an index is any matrix: one that
holds no well-formed table has no next token, and the relation is false of it.

Limits: no description is given here. "HoleAt.proofSound a" reads the same relation.

-/
import Johnson.Top.OnFilesAt
import Johnson.Flat.LedgerClaim

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles

open Inst.Model
open Inst.Model.Layout (kRef hRef)

/-- A description's indices are read as matrices, and its relation gives the claim on them. -/
structure ReadsCells (a : DescriptionAt) (s : Cm.Scales) (rows cols : ℕ) where
  /-- the matrix of an index -/
  cells : a.I → Fin rows → Fin cols → Flat.GE
  /-- an instance is a request of the model -/
  req : a.X → Instance ppref
  /-- what the description's builder builds is what "requestOfTokens" builds -/
  build : ∀ x' b x, a.build x' b = some x → requestOfTokens x' b = some (req x)
  /-- the description's model is the integer model at the index that the matrix holds -/
  next : ∀ i l, a.nextToken i l = Flat.nextTok s (cells i) l
  /-- the relaxed relation gives the claim -/
  rel : ∀ i x w, a.Rno i x w → Flat.RelL s (cells i) (req x)

/-- **The meaning, at a description on matrices.** -/
theorem HoleAt.sound_of_cells (a : DescriptionAt) {s : Cm.Scales} (lawful : s.Lawful)
    {rows cols : ℕ} (hr : rows ≤ hRef) (hc : cols ≤ 2 ^ kRef) (R : ReadsCells a s rows cols) :
    HoleAt.sound a := by
  intro i x' b x hb hw position h
  obtain ⟨w, hw⟩ := hw
  show a.nextToken i (x'.1 ++ x'.2.take position) = some x'.2[position]
  rw [R.next]
  exact Flat.sound_core lawful hr hc (R.build x' b x hb) (R.rel i x w hw) position h

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.HoleAt.sound_of_cells
