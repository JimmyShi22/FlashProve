-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoZTests0.lean.
The tests on public numbers of the lookup on the digits: all ten clauses of Fo.ZTests from the
success of the verifier's own routines.

OnBytes/Tie/Pv/Lookup/Ends/FoZPlaced1.lean has nine of the ten clauses at every smallness test of
the byte-level verifier's record of public numbers, and leaves tailTest.
OnBytes/Tie/Pv/Lookup/Ends/PiecesFTail.lean shows tailTest of whatever HTailF2.piecesF returns. A
plan's record is what piecesF returned but for fields that the test does not read (Fo.SameP). So
where Verify.publicOf returns X, Fo.ZTests holds at every member of X: it is no premise.

Main names:
  `tailTest_same`: tailTest reads the fields of Fo.SameP alone.
  `tailTest_from`, `placed3_from`: Fo.ZPlan.FromPieces tl gives tailTest tl = true, and so
    Fo.ZPlan.Placed3 tl.
  `public_G_zTests0`, `public_A_zTests0`, `public_H_zTests0`: Fo.ZTests at X's own members, from
    Verify.publicOf's success and membership alone.
Limits: the records are the plans': nothing on a record that a later routine of a run has turned.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoZPlaced1
import OnBytes.Tie.Pv.Lookup.Ends.PiecesFTail

set_option autoImplicit false

namespace Fo.ZPlan
open OnBytes OnBytes.Model OnBytes.DgP

theorem tailTest_same {a b : HTailF2} (h : SameP a b) : tailTest b = tailTest a := by
  rw [h.eq]
  rfl

theorem tailTest_from {tl : HTailF2} (h : FromPieces tl) : tailTest tl = true := by
  obtain ⟨tl0, tlp, h1, h2⟩ := h
  rw [tailTest_same h2]
  exact Fo.PiecesF.piecesF_tailTest tl0 tlp h1

theorem placed3_from {tl : HTailF2} (h : FromPieces tl) : Placed3 tl :=
  placed3_of h (tailTest_from h)

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}

theorem public_G_zTests0 (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (hp : Layer.HPlan2) (hg : X.G[g]? = some hp) : ZTests hp.tl hp.tl hp.Fp :=
  public_G_zTests h g hp hg (placed3_from (public_G_from h g hp hg))

theorem public_A_zTests0 (h : Verify.publicOf pol KL layout = .ok X) (g : Nat)
    (a : Attention.Plan) (hg : X.A[g]? = some a) : ZTests a.seam.tl a.seam.tl a.seam.Fp :=
  public_A_zTests h g a hg (placed3_from (public_A_from h g a hg))

theorem public_H_zTests0 (h : Verify.publicOf pol KL layout = .ok X) :
    ZTests X.H.tl X.H.tl X.H.Fp :=
  public_H_zTests h (placed3_from (public_H_from h))

end

end Fo.ZPlan
